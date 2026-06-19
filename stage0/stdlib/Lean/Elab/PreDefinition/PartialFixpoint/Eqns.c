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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_769_; size_t v___x_770_; size_t v___x_771_; 
v___x_769_ = ((size_t)5ULL);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_shift_left(v___x_770_, v___x_769_);
return v___x_771_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; 
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_774_ = lean_usize_sub(v___x_773_, v___x_772_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(lean_object* v_x_776_, size_t v_x_777_, size_t v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
lean_object* v_es_781_; size_t v___x_782_; size_t v___x_783_; size_t v___x_784_; size_t v___x_785_; lean_object* v_j_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_es_781_ = lean_ctor_get(v_x_776_, 0);
v___x_782_ = ((size_t)5ULL);
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_785_ = lean_usize_land(v_x_777_, v___x_784_);
v_j_786_ = lean_usize_to_nat(v___x_785_);
v___x_787_ = lean_array_get_size(v_es_781_);
v___x_788_ = lean_nat_dec_lt(v_j_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_dec(v_j_786_);
lean_dec(v_x_780_);
lean_dec(v_x_779_);
return v_x_776_;
}
else
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_825_; 
lean_inc_ref(v_es_781_);
v_isSharedCheck_825_ = !lean_is_exclusive(v_x_776_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v_x_776_, 0);
lean_dec(v_unused_826_);
v___x_790_ = v_x_776_;
v_isShared_791_ = v_isSharedCheck_825_;
goto v_resetjp_789_;
}
else
{
lean_dec(v_x_776_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_825_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_v_792_; lean_object* v___x_793_; lean_object* v_xs_x27_794_; lean_object* v___y_796_; 
v_v_792_ = lean_array_fget(v_es_781_, v_j_786_);
v___x_793_ = lean_box(0);
v_xs_x27_794_ = lean_array_fset(v_es_781_, v_j_786_, v___x_793_);
switch(lean_obj_tag(v_v_792_))
{
case 0:
{
lean_object* v_key_801_; lean_object* v_val_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_812_; 
v_key_801_ = lean_ctor_get(v_v_792_, 0);
v_val_802_ = lean_ctor_get(v_v_792_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v_v_792_);
if (v_isSharedCheck_812_ == 0)
{
v___x_804_ = v_v_792_;
v_isShared_805_ = v_isSharedCheck_812_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_val_802_);
lean_inc(v_key_801_);
lean_dec(v_v_792_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_812_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
uint8_t v___x_806_; 
v___x_806_ = l_Lean_instBEqMVarId_beq(v_x_779_, v_key_801_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_del_object(v___x_804_);
v___x_807_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_801_, v_val_802_, v_x_779_, v_x_780_);
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___y_796_ = v___x_808_;
goto v___jp_795_;
}
else
{
lean_object* v___x_810_; 
lean_dec(v_val_802_);
lean_dec(v_key_801_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v_x_780_);
lean_ctor_set(v___x_804_, 0, v_x_779_);
v___x_810_ = v___x_804_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_x_779_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_x_780_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
v___y_796_ = v___x_810_;
goto v___jp_795_;
}
}
}
}
case 1:
{
lean_object* v_node_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_823_; 
v_node_813_ = lean_ctor_get(v_v_792_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_v_792_);
if (v_isSharedCheck_823_ == 0)
{
v___x_815_ = v_v_792_;
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_node_813_);
lean_dec(v_v_792_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_817_ = lean_usize_shift_right(v_x_777_, v___x_782_);
v___x_818_ = lean_usize_add(v_x_778_, v___x_783_);
v___x_819_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_node_813_, v___x_817_, v___x_818_, v_x_779_, v_x_780_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_819_);
v___x_821_ = v___x_815_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
v___y_796_ = v___x_821_;
goto v___jp_795_;
}
}
}
default: 
{
lean_object* v___x_824_; 
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_x_779_);
lean_ctor_set(v___x_824_, 1, v_x_780_);
v___y_796_ = v___x_824_;
goto v___jp_795_;
}
}
v___jp_795_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_array_fset(v_xs_x27_794_, v_j_786_, v___y_796_);
lean_dec(v_j_786_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_797_);
v___x_799_ = v___x_790_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
else
{
lean_object* v_ks_827_; lean_object* v_vs_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_848_; 
v_ks_827_ = lean_ctor_get(v_x_776_, 0);
v_vs_828_ = lean_ctor_get(v_x_776_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_x_776_);
if (v_isSharedCheck_848_ == 0)
{
v___x_830_ = v_x_776_;
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_vs_828_);
lean_inc(v_ks_827_);
lean_dec(v_x_776_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_ks_827_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_vs_828_);
v___x_833_ = v_reuseFailAlloc_847_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v_newNode_834_; uint8_t v___y_836_; size_t v___x_842_; uint8_t v___x_843_; 
v_newNode_834_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v___x_833_, v_x_779_, v_x_780_);
v___x_842_ = ((size_t)7ULL);
v___x_843_ = lean_usize_dec_le(v___x_842_, v_x_778_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_834_);
v___x_845_ = lean_unsigned_to_nat(4u);
v___x_846_ = lean_nat_dec_lt(v___x_844_, v___x_845_);
lean_dec(v___x_844_);
v___y_836_ = v___x_846_;
goto v___jp_835_;
}
else
{
v___y_836_ = v___x_843_;
goto v___jp_835_;
}
v___jp_835_:
{
if (v___y_836_ == 0)
{
lean_object* v_ks_837_; lean_object* v_vs_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_ks_837_ = lean_ctor_get(v_newNode_834_, 0);
lean_inc_ref(v_ks_837_);
v_vs_838_ = lean_ctor_get(v_newNode_834_, 1);
lean_inc_ref(v_vs_838_);
lean_dec_ref(v_newNode_834_);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_841_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_778_, v_ks_837_, v_vs_838_, v___x_839_, v___x_840_);
lean_dec_ref(v_vs_838_);
lean_dec_ref(v_ks_837_);
return v___x_841_;
}
else
{
return v_newNode_834_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_849_, lean_object* v_keys_850_, lean_object* v_vals_851_, lean_object* v_i_852_, lean_object* v_entries_853_){
_start:
{
lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_854_ = lean_array_get_size(v_keys_850_);
v___x_855_ = lean_nat_dec_lt(v_i_852_, v___x_854_);
if (v___x_855_ == 0)
{
lean_dec(v_i_852_);
return v_entries_853_;
}
else
{
lean_object* v_k_856_; lean_object* v_v_857_; uint64_t v___x_858_; size_t v_h_859_; size_t v___x_860_; lean_object* v___x_861_; size_t v___x_862_; size_t v___x_863_; size_t v___x_864_; size_t v_h_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_k_856_ = lean_array_fget_borrowed(v_keys_850_, v_i_852_);
v_v_857_ = lean_array_fget_borrowed(v_vals_851_, v_i_852_);
v___x_858_ = l_Lean_instHashableMVarId_hash(v_k_856_);
v_h_859_ = lean_uint64_to_usize(v___x_858_);
v___x_860_ = ((size_t)5ULL);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_sub(v_depth_849_, v___x_862_);
v___x_864_ = lean_usize_mul(v___x_860_, v___x_863_);
v_h_865_ = lean_usize_shift_right(v_h_859_, v___x_864_);
v___x_866_ = lean_nat_add(v_i_852_, v___x_861_);
lean_dec(v_i_852_);
lean_inc(v_v_857_);
lean_inc(v_k_856_);
v___x_867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_entries_853_, v_h_865_, v_depth_849_, v_k_856_, v_v_857_);
v_i_852_ = v___x_866_;
v_entries_853_ = v___x_867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_869_, lean_object* v_keys_870_, lean_object* v_vals_871_, lean_object* v_i_872_, lean_object* v_entries_873_){
_start:
{
size_t v_depth_boxed_874_; lean_object* v_res_875_; 
v_depth_boxed_874_ = lean_unbox_usize(v_depth_869_);
lean_dec(v_depth_869_);
v_res_875_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_874_, v_keys_870_, v_vals_871_, v_i_872_, v_entries_873_);
lean_dec_ref(v_vals_871_);
lean_dec_ref(v_keys_870_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
size_t v_x_2123__boxed_881_; size_t v_x_2124__boxed_882_; lean_object* v_res_883_; 
v_x_2123__boxed_881_ = lean_unbox_usize(v_x_877_);
lean_dec(v_x_877_);
v_x_2124__boxed_882_ = lean_unbox_usize(v_x_878_);
lean_dec(v_x_878_);
v_res_883_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_876_, v_x_2123__boxed_881_, v_x_2124__boxed_882_, v_x_879_, v_x_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
uint64_t v___x_887_; size_t v___x_888_; size_t v___x_889_; lean_object* v___x_890_; 
v___x_887_ = l_Lean_instHashableMVarId_hash(v_x_885_);
v___x_888_ = lean_uint64_to_usize(v___x_887_);
v___x_889_ = ((size_t)1ULL);
v___x_890_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_884_, v___x_888_, v___x_889_, v_x_885_, v_x_886_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(lean_object* v_mvarId_891_, lean_object* v_val_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; lean_object* v_mctx_896_; lean_object* v_cache_897_; lean_object* v_zetaDeltaFVarIds_898_; lean_object* v_postponed_899_; lean_object* v_diag_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_928_; 
v___x_895_ = lean_st_ref_take(v___y_893_);
v_mctx_896_ = lean_ctor_get(v___x_895_, 0);
v_cache_897_ = lean_ctor_get(v___x_895_, 1);
v_zetaDeltaFVarIds_898_ = lean_ctor_get(v___x_895_, 2);
v_postponed_899_ = lean_ctor_get(v___x_895_, 3);
v_diag_900_ = lean_ctor_get(v___x_895_, 4);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_928_ == 0)
{
v___x_902_ = v___x_895_;
v_isShared_903_ = v_isSharedCheck_928_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_diag_900_);
lean_inc(v_postponed_899_);
lean_inc(v_zetaDeltaFVarIds_898_);
lean_inc(v_cache_897_);
lean_inc(v_mctx_896_);
lean_dec(v___x_895_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_928_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_depth_904_; lean_object* v_levelAssignDepth_905_; lean_object* v_lmvarCounter_906_; lean_object* v_mvarCounter_907_; lean_object* v_lDecls_908_; lean_object* v_decls_909_; lean_object* v_userNames_910_; lean_object* v_lAssignment_911_; lean_object* v_eAssignment_912_; lean_object* v_dAssignment_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_927_; 
v_depth_904_ = lean_ctor_get(v_mctx_896_, 0);
v_levelAssignDepth_905_ = lean_ctor_get(v_mctx_896_, 1);
v_lmvarCounter_906_ = lean_ctor_get(v_mctx_896_, 2);
v_mvarCounter_907_ = lean_ctor_get(v_mctx_896_, 3);
v_lDecls_908_ = lean_ctor_get(v_mctx_896_, 4);
v_decls_909_ = lean_ctor_get(v_mctx_896_, 5);
v_userNames_910_ = lean_ctor_get(v_mctx_896_, 6);
v_lAssignment_911_ = lean_ctor_get(v_mctx_896_, 7);
v_eAssignment_912_ = lean_ctor_get(v_mctx_896_, 8);
v_dAssignment_913_ = lean_ctor_get(v_mctx_896_, 9);
v_isSharedCheck_927_ = !lean_is_exclusive(v_mctx_896_);
if (v_isSharedCheck_927_ == 0)
{
v___x_915_ = v_mctx_896_;
v_isShared_916_ = v_isSharedCheck_927_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_dAssignment_913_);
lean_inc(v_eAssignment_912_);
lean_inc(v_lAssignment_911_);
lean_inc(v_userNames_910_);
lean_inc(v_decls_909_);
lean_inc(v_lDecls_908_);
lean_inc(v_mvarCounter_907_);
lean_inc(v_lmvarCounter_906_);
lean_inc(v_levelAssignDepth_905_);
lean_inc(v_depth_904_);
lean_dec(v_mctx_896_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_927_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_912_, v_mvarId_891_, v_val_892_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 8, v___x_917_);
v___x_919_ = v___x_915_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_depth_904_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_levelAssignDepth_905_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_lmvarCounter_906_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_mvarCounter_907_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v_lDecls_908_);
lean_ctor_set(v_reuseFailAlloc_926_, 5, v_decls_909_);
lean_ctor_set(v_reuseFailAlloc_926_, 6, v_userNames_910_);
lean_ctor_set(v_reuseFailAlloc_926_, 7, v_lAssignment_911_);
lean_ctor_set(v_reuseFailAlloc_926_, 8, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_926_, 9, v_dAssignment_913_);
v___x_919_ = v_reuseFailAlloc_926_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_919_);
v___x_921_ = v___x_902_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_cache_897_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_zetaDeltaFVarIds_898_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_postponed_899_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_diag_900_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_st_ref_set(v___y_893_, v___x_921_);
v___x_923_ = lean_box(0);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object* v_mvarId_929_, lean_object* v_val_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_929_, v_val_930_, v___y_931_);
lean_dec(v___y_931_);
return v_res_933_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_938_ = lean_unsigned_to_nat(41u);
v___x_939_ = lean_unsigned_to_nat(70u);
v___x_940_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_941_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_942_ = l_mkPanicMessageWithDecl(v___x_941_, v___x_940_, v___x_939_, v___x_938_, v___x_937_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_943_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2));
v___x_944_ = lean_unsigned_to_nat(51u);
v___x_945_ = lean_unsigned_to_nat(72u);
v___x_946_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_947_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_948_ = l_mkPanicMessageWithDecl(v___x_947_, v___x_946_, v___x_945_, v___x_944_, v___x_943_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object* v_mvarId_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; 
lean_inc(v_mvarId_949_);
v___x_955_ = l_Lean_MVarId_getType_x27(v_mvarId_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
v___x_957_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_958_ = lean_unsigned_to_nat(3u);
v___x_959_ = l_Lean_Expr_isAppOfArity(v_a_956_, v___x_957_, v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec(v_a_956_);
lean_dec(v_mvarId_949_);
v___x_960_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
v___x_961_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_960_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v___x_961_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = l_Lean_Expr_appFn_x21(v_a_956_);
v___x_963_ = l_Lean_Expr_appArg_x21(v___x_962_);
lean_dec_ref(v___x_962_);
v___x_964_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_963_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc_n(v_a_965_, 2);
lean_dec_ref_known(v___x_964_, 1);
lean_inc(v___y_953_);
lean_inc_ref(v___y_952_);
lean_inc(v___y_951_);
lean_inc_ref(v___y_950_);
v___x_966_ = lean_infer_type(v_a_965_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; uint8_t v___x_968_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = l_Lean_Expr_isAppOfArity(v_a_967_, v___x_957_, v___x_958_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec(v_a_967_);
lean_dec(v_a_965_);
lean_dec(v_a_956_);
lean_dec(v_mvarId_949_);
v___x_969_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4);
v___x_970_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_969_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = l_Lean_Expr_appArg_x21(v_a_956_);
lean_dec(v_a_956_);
v___x_972_ = l_Lean_Expr_appArg_x21(v_a_967_);
lean_dec(v_a_967_);
v___x_973_ = l_Lean_Meta_mkEq(v___x_972_, v___x_971_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = lean_box(0);
v___x_976_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_974_, v___x_975_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc_n(v_a_977_, 2);
lean_dec_ref_known(v___x_976_, 1);
v___x_978_ = l_Lean_Meta_mkEqTrans(v_a_965_, v_a_977_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v___y_950_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_988_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_949_, v_a_979_, v___y_951_);
lean_dec(v___y_951_);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v___x_980_, 0);
lean_dec(v_unused_989_);
v___x_982_ = v___x_980_;
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
else
{
lean_dec(v___x_980_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = l_Lean_Expr_mvarId_x21(v_a_977_);
lean_dec(v_a_977_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_984_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_977_);
lean_dec(v___y_951_);
lean_dec(v_mvarId_949_);
v_a_990_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_978_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_978_);
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
lean_dec(v_a_965_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v_mvarId_949_);
v_a_998_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_976_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_976_);
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
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v_a_965_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v_mvarId_949_);
v_a_1006_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_973_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_973_);
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
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_a_965_);
lean_dec(v_a_956_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v_mvarId_949_);
v_a_1014_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_966_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_966_);
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
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_a_956_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v_mvarId_949_);
v_a_1022_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_964_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_964_);
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
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v_mvarId_949_);
v_a_1030_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_955_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_955_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object* v_mvarId_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object* v_mvarId_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___f_1051_; lean_object* v___x_1052_; 
lean_inc(v_mvarId_1045_);
v___f_1051_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1051_, 0, v_mvarId_1045_);
v___x_1052_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1045_, v___f_1051_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object* v_mvarId_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object* v_mvarId_1060_, lean_object* v_val_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1060_, v_val_1061_, v___y_1063_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object* v_mvarId_1068_, lean_object* v_val_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_1068_, v_val_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object* v_00_u03b2_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_1077_, v_x_1078_, v_x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1081_, lean_object* v_x_1082_, size_t v_x_1083_, size_t v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1082_, v_x_1083_, v_x_1084_, v_x_1085_, v_x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
size_t v_x_2609__boxed_1094_; size_t v_x_2610__boxed_1095_; lean_object* v_res_1096_; 
v_x_2609__boxed_1094_ = lean_unbox_usize(v_x_1090_);
lean_dec(v_x_1090_);
v_x_2610__boxed_1095_ = lean_unbox_usize(v_x_1091_);
lean_dec(v_x_1091_);
v_res_1096_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_1088_, v_x_1089_, v_x_2609__boxed_1094_, v_x_2610__boxed_1095_, v_x_1092_, v_x_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1097_, lean_object* v_n_1098_, lean_object* v_k_1099_, lean_object* v_v_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1098_, v_k_1099_, v_v_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1102_, size_t v_depth_1103_, lean_object* v_keys_1104_, lean_object* v_vals_1105_, lean_object* v_heq_1106_, lean_object* v_i_1107_, lean_object* v_entries_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1103_, v_keys_1104_, v_vals_1105_, v_i_1107_, v_entries_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1110_, lean_object* v_depth_1111_, lean_object* v_keys_1112_, lean_object* v_vals_1113_, lean_object* v_heq_1114_, lean_object* v_i_1115_, lean_object* v_entries_1116_){
_start:
{
size_t v_depth_boxed_1117_; lean_object* v_res_1118_; 
v_depth_boxed_1117_ = lean_unbox_usize(v_depth_1111_);
lean_dec(v_depth_1111_);
v_res_1118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1110_, v_depth_boxed_1117_, v_keys_1112_, v_vals_1113_, v_heq_1114_, v_i_1115_, v_entries_1116_);
lean_dec_ref(v_vals_1113_);
lean_dec_ref(v_keys_1112_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1120_, v_x_1121_, v_x_1122_, v_x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_1125_, lean_object* v_opt_1126_){
_start:
{
lean_object* v_name_1127_; lean_object* v_defValue_1128_; lean_object* v_map_1129_; lean_object* v___x_1130_; 
v_name_1127_ = lean_ctor_get(v_opt_1126_, 0);
v_defValue_1128_ = lean_ctor_get(v_opt_1126_, 1);
v_map_1129_ = lean_ctor_get(v_opts_1125_, 0);
v___x_1130_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1129_, v_name_1127_);
if (lean_obj_tag(v___x_1130_) == 0)
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_unbox(v_defValue_1128_);
return v___x_1131_;
}
else
{
lean_object* v_val_1132_; 
v_val_1132_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_val_1132_);
lean_dec_ref_known(v___x_1130_, 1);
if (lean_obj_tag(v_val_1132_) == 1)
{
uint8_t v_v_1133_; 
v_v_1133_ = lean_ctor_get_uint8(v_val_1132_, 0);
lean_dec_ref_known(v_val_1132_, 0);
return v_v_1133_;
}
else
{
uint8_t v___x_1134_; 
lean_dec(v_val_1132_);
v___x_1134_ = lean_unbox(v_defValue_1128_);
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_1135_, lean_object* v_opt_1136_){
_start:
{
uint8_t v_res_1137_; lean_object* v_r_1138_; 
v_res_1137_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_1135_, v_opt_1136_);
lean_dec_ref(v_opt_1136_);
lean_dec_ref(v_opts_1135_);
v_r_1138_ = lean_box(v_res_1137_);
return v_r_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_1139_, lean_object* v_opt_1140_){
_start:
{
lean_object* v_name_1141_; lean_object* v_defValue_1142_; lean_object* v_map_1143_; lean_object* v___x_1144_; 
v_name_1141_ = lean_ctor_get(v_opt_1140_, 0);
v_defValue_1142_ = lean_ctor_get(v_opt_1140_, 1);
v_map_1143_ = lean_ctor_get(v_opts_1139_, 0);
v___x_1144_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1143_, v_name_1141_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_inc(v_defValue_1142_);
return v_defValue_1142_;
}
else
{
lean_object* v_val_1145_; 
v_val_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_val_1145_);
lean_dec_ref_known(v___x_1144_, 1);
if (lean_obj_tag(v_val_1145_) == 3)
{
lean_object* v_v_1146_; 
v_v_1146_ = lean_ctor_get(v_val_1145_, 0);
lean_inc(v_v_1146_);
lean_dec_ref_known(v_val_1145_, 1);
return v_v_1146_;
}
else
{
lean_dec(v_val_1145_);
lean_inc(v_defValue_1142_);
return v_defValue_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_1147_, lean_object* v_opt_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_1147_, v_opt_1148_);
lean_dec_ref(v_opt_1148_);
lean_dec_ref(v_opts_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(lean_object* v_e_1150_, lean_object* v___y_1151_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = l_Lean_Expr_hasMVar(v_e_1150_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_e_1150_);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; lean_object* v_mctx_1156_; lean_object* v___x_1157_; lean_object* v_fst_1158_; lean_object* v_snd_1159_; lean_object* v___x_1160_; lean_object* v_cache_1161_; lean_object* v_zetaDeltaFVarIds_1162_; lean_object* v_postponed_1163_; lean_object* v_diag_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1173_; 
v___x_1155_ = lean_st_ref_get(v___y_1151_);
v_mctx_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc_ref(v_mctx_1156_);
lean_dec(v___x_1155_);
v___x_1157_ = l_Lean_instantiateMVarsCore(v_mctx_1156_, v_e_1150_);
v_fst_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_fst_1158_);
v_snd_1159_ = lean_ctor_get(v___x_1157_, 1);
lean_inc(v_snd_1159_);
lean_dec_ref(v___x_1157_);
v___x_1160_ = lean_st_ref_take(v___y_1151_);
v_cache_1161_ = lean_ctor_get(v___x_1160_, 1);
v_zetaDeltaFVarIds_1162_ = lean_ctor_get(v___x_1160_, 2);
v_postponed_1163_ = lean_ctor_get(v___x_1160_, 3);
v_diag_1164_ = lean_ctor_get(v___x_1160_, 4);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; 
v_unused_1174_ = lean_ctor_get(v___x_1160_, 0);
lean_dec(v_unused_1174_);
v___x_1166_ = v___x_1160_;
v_isShared_1167_ = v_isSharedCheck_1173_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_diag_1164_);
lean_inc(v_postponed_1163_);
lean_inc(v_zetaDeltaFVarIds_1162_);
lean_inc(v_cache_1161_);
lean_dec(v___x_1160_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1173_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v_snd_1159_);
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_snd_1159_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_cache_1161_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_zetaDeltaFVarIds_1162_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_postponed_1163_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v_diag_1164_);
v___x_1169_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_st_ref_set(v___y_1151_, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_fst_1158_);
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg___boxed(lean_object* v_e_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_e_1175_, v___y_1176_);
lean_dec(v___y_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object* v_e_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_e_1179_, v___y_1181_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object* v_e_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v_e_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(lean_object* v_k_1193_, uint8_t v_allowLevelAssignments_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1194_, v_k_1193_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_a_1209_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1200_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1200_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg___boxed(lean_object* v_k_1217_, lean_object* v_allowLevelAssignments_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1224_; lean_object* v_res_1225_; 
v_allowLevelAssignments_boxed_1224_ = lean_unbox(v_allowLevelAssignments_1218_);
v_res_1225_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v_k_1217_, v_allowLevelAssignments_boxed_1224_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(lean_object* v_00_u03b1_1226_, lean_object* v_k_1227_, uint8_t v_allowLevelAssignments_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v_k_1227_, v_allowLevelAssignments_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___boxed(lean_object* v_00_u03b1_1235_, lean_object* v_k_1236_, lean_object* v_allowLevelAssignments_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1243_; lean_object* v_res_1244_; 
v_allowLevelAssignments_boxed_1243_ = lean_unbox(v_allowLevelAssignments_1237_);
v_res_1244_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v_00_u03b1_1235_, v_k_1236_, v_allowLevelAssignments_boxed_1243_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(lean_object* v_thm_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; lean_object* v_env_1249_; lean_object* v_toConstantVal_1250_; lean_object* v_value_1251_; lean_object* v_all_1252_; uint8_t v___y_1254_; lean_object* v_type_1262_; uint8_t v___x_1263_; 
v___x_1248_ = lean_st_ref_get(v___y_1246_);
v_env_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc_ref_n(v_env_1249_, 2);
lean_dec(v___x_1248_);
v_toConstantVal_1250_ = lean_ctor_get(v_thm_1245_, 0);
v_value_1251_ = lean_ctor_get(v_thm_1245_, 1);
v_all_1252_ = lean_ctor_get(v_thm_1245_, 2);
v_type_1262_ = lean_ctor_get(v_toConstantVal_1250_, 2);
v___x_1263_ = l_Lean_Environment_hasUnsafe(v_env_1249_, v_type_1262_);
if (v___x_1263_ == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = l_Lean_Environment_hasUnsafe(v_env_1249_, v_value_1251_);
v___y_1254_ = v___x_1264_;
goto v___jp_1253_;
}
else
{
lean_dec_ref(v_env_1249_);
v___y_1254_ = v___x_1263_;
goto v___jp_1253_;
}
v___jp_1253_:
{
if (v___y_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_thm_1245_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_inc(v_all_1252_);
lean_inc_ref(v_value_1251_);
lean_inc_ref(v_toConstantVal_1250_);
lean_dec_ref(v_thm_1245_);
v___x_1257_ = lean_box(0);
v___x_1258_ = 0;
v___x_1259_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1259_, 0, v_toConstantVal_1250_);
lean_ctor_set(v___x_1259_, 1, v_value_1251_);
lean_ctor_set(v___x_1259_, 2, v___x_1257_);
lean_ctor_set(v___x_1259_, 3, v_all_1252_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*4, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg___boxed(lean_object* v_thm_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_thm_1265_, v___y_1266_);
lean_dec(v___y_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(lean_object* v_thm_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_thm_1269_, v___y_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___boxed(lean_object* v_thm_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(v_thm_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0(lean_object* v_k_1283_, lean_object* v_b_1284_, lean_object* v_c_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1291_ = lean_apply_7(v_k_1283_, v_b_1284_, v_c_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, lean_box(0));
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0___boxed(lean_object* v_k_1292_, lean_object* v_b_1293_, lean_object* v_c_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0(v_k_1292_, v_b_1293_, v_c_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(lean_object* v_e_1301_, lean_object* v_k_1302_, uint8_t v_cleanupAnnotations_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___f_1309_; uint8_t v___x_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___f_1309_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1309_, 0, v_k_1302_);
v___x_1310_ = 1;
v___x_1311_ = 0;
v___x_1312_ = lean_box(0);
v___x_1313_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1301_, v___x_1310_, v___x_1311_, v___x_1310_, v___x_1311_, v___x_1312_, v___f_1309_, v_cleanupAnnotations_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
v_a_1322_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1313_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1313_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___boxed(lean_object* v_e_1330_, lean_object* v_k_1331_, lean_object* v_cleanupAnnotations_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1338_; lean_object* v_res_1339_; 
v_cleanupAnnotations_boxed_1338_ = lean_unbox(v_cleanupAnnotations_1332_);
v_res_1339_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_e_1330_, v_k_1331_, v_cleanupAnnotations_boxed_1338_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(lean_object* v_00_u03b1_1340_, lean_object* v_e_1341_, lean_object* v_k_1342_, uint8_t v_cleanupAnnotations_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_e_1341_, v_k_1342_, v_cleanupAnnotations_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_e_1351_, lean_object* v_k_1352_, lean_object* v_cleanupAnnotations_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1359_; lean_object* v_res_1360_; 
v_cleanupAnnotations_boxed_1359_ = lean_unbox(v_cleanupAnnotations_1353_);
v_res_1360_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(v_00_u03b1_1350_, v_e_1351_, v_k_1352_, v_cleanupAnnotations_boxed_1359_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object* v___x_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_options_1370_; uint8_t v_hasTrace_1371_; 
v_options_1370_ = lean_ctor_get(v___y_1367_, 2);
v_hasTrace_1371_ = lean_ctor_get_uint8(v_options_1370_, sizeof(void*)*1);
if (v_hasTrace_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec(v___x_1364_);
v___x_1372_ = lean_box(v_hasTrace_1371_);
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
else
{
lean_object* v_inheritedTraceOptions_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_inheritedTraceOptions_1374_ = lean_ctor_get(v___y_1367_, 13);
v___x_1375_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_1376_ = l_Lean_Name_append(v___x_1375_, v___x_1364_);
v___x_1377_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1374_, v_options_1370_, v___x_1376_);
lean_dec(v___x_1376_);
v___x_1378_ = lean_box(v___x_1377_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
return v___x_1379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v___x_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1386_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1387_; double v___x_1388_; 
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_float_of_nat(v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(lean_object* v_cls_1392_, lean_object* v_msg_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_ref_1399_; lean_object* v___x_1400_; lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1445_; 
v_ref_1399_ = lean_ctor_get(v___y_1396_, 5);
v___x_1400_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1445_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1445_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v_traceState_1406_; lean_object* v_env_1407_; lean_object* v_nextMacroScope_1408_; lean_object* v_ngen_1409_; lean_object* v_auxDeclNGen_1410_; lean_object* v_cache_1411_; lean_object* v_messages_1412_; lean_object* v_infoState_1413_; lean_object* v_snapshotTasks_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1444_; 
v___x_1405_ = lean_st_ref_take(v___y_1397_);
v_traceState_1406_ = lean_ctor_get(v___x_1405_, 4);
v_env_1407_ = lean_ctor_get(v___x_1405_, 0);
v_nextMacroScope_1408_ = lean_ctor_get(v___x_1405_, 1);
v_ngen_1409_ = lean_ctor_get(v___x_1405_, 2);
v_auxDeclNGen_1410_ = lean_ctor_get(v___x_1405_, 3);
v_cache_1411_ = lean_ctor_get(v___x_1405_, 5);
v_messages_1412_ = lean_ctor_get(v___x_1405_, 6);
v_infoState_1413_ = lean_ctor_get(v___x_1405_, 7);
v_snapshotTasks_1414_ = lean_ctor_get(v___x_1405_, 8);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1416_ = v___x_1405_;
v_isShared_1417_ = v_isSharedCheck_1444_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_snapshotTasks_1414_);
lean_inc(v_infoState_1413_);
lean_inc(v_messages_1412_);
lean_inc(v_cache_1411_);
lean_inc(v_traceState_1406_);
lean_inc(v_auxDeclNGen_1410_);
lean_inc(v_ngen_1409_);
lean_inc(v_nextMacroScope_1408_);
lean_inc(v_env_1407_);
lean_dec(v___x_1405_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1444_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
uint64_t v_tid_1418_; lean_object* v_traces_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1443_; 
v_tid_1418_ = lean_ctor_get_uint64(v_traceState_1406_, sizeof(void*)*1);
v_traces_1419_ = lean_ctor_get(v_traceState_1406_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_traceState_1406_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1421_ = v_traceState_1406_;
v_isShared_1422_ = v_isSharedCheck_1443_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_traces_1419_);
lean_dec(v_traceState_1406_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1443_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; double v___x_1424_; uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0);
v___x_1425_ = 0;
v___x_1426_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1));
v___x_1427_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1427_, 0, v_cls_1392_);
lean_ctor_set(v___x_1427_, 1, v___x_1423_);
lean_ctor_set(v___x_1427_, 2, v___x_1426_);
lean_ctor_set_float(v___x_1427_, sizeof(void*)*3, v___x_1424_);
lean_ctor_set_float(v___x_1427_, sizeof(void*)*3 + 8, v___x_1424_);
lean_ctor_set_uint8(v___x_1427_, sizeof(void*)*3 + 16, v___x_1425_);
v___x_1428_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2));
v___x_1429_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v_a_1401_);
lean_ctor_set(v___x_1429_, 2, v___x_1428_);
lean_inc(v_ref_1399_);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_ref_1399_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = l_Lean_PersistentArray_push___redArg(v_traces_1419_, v___x_1430_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1431_);
v___x_1433_ = v___x_1421_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1431_);
lean_ctor_set_uint64(v_reuseFailAlloc_1442_, sizeof(void*)*1, v_tid_1418_);
v___x_1433_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1435_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 4, v___x_1433_);
v___x_1435_ = v___x_1416_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_env_1407_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_nextMacroScope_1408_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_ngen_1409_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_auxDeclNGen_1410_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1441_, 5, v_cache_1411_);
lean_ctor_set(v_reuseFailAlloc_1441_, 6, v_messages_1412_);
lean_ctor_set(v_reuseFailAlloc_1441_, 7, v_infoState_1413_);
lean_ctor_set(v_reuseFailAlloc_1441_, 8, v_snapshotTasks_1414_);
v___x_1435_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1436_ = lean_st_ref_set(v___y_1397_, v___x_1435_);
v___x_1437_ = lean_box(0);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1437_);
v___x_1439_ = v___x_1403_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___boxed(lean_object* v_cls_1446_, lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v_cls_1446_, v_msg_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_o_1454_, lean_object* v_k_1455_, uint8_t v_v_1456_){
_start:
{
lean_object* v_map_1457_; uint8_t v_hasTrace_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1472_; 
v_map_1457_ = lean_ctor_get(v_o_1454_, 0);
v_hasTrace_1458_ = lean_ctor_get_uint8(v_o_1454_, sizeof(void*)*1);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_o_1454_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1460_ = v_o_1454_;
v_isShared_1461_ = v_isSharedCheck_1472_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_map_1457_);
lean_dec(v_o_1454_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1472_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1462_, 0, v_v_1456_);
lean_inc(v_k_1455_);
v___x_1463_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1455_, v___x_1462_, v_map_1457_);
if (v_hasTrace_1458_ == 0)
{
lean_object* v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1467_; 
v___x_1464_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_1465_ = l_Lean_Name_isPrefixOf(v___x_1464_, v_k_1455_);
lean_dec(v_k_1455_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1463_);
v___x_1467_ = v___x_1460_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1463_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_ctor_set_uint8(v___x_1467_, sizeof(void*)*1, v___x_1465_);
return v___x_1467_;
}
}
else
{
lean_object* v___x_1470_; 
lean_dec(v_k_1455_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1463_);
v___x_1470_ = v___x_1460_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1463_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*1, v_hasTrace_1458_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_o_1473_, lean_object* v_k_1474_, lean_object* v_v_1475_){
_start:
{
uint8_t v_v_boxed_1476_; lean_object* v_res_1477_; 
v_v_boxed_1476_ = lean_unbox(v_v_1475_);
v_res_1477_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(v_o_1473_, v_k_1474_, v_v_boxed_1476_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object* v_opts_1478_, lean_object* v_opt_1479_, uint8_t v_val_1480_){
_start:
{
lean_object* v_name_1481_; lean_object* v___x_1482_; 
v_name_1481_ = lean_ctor_get(v_opt_1479_, 0);
lean_inc(v_name_1481_);
lean_dec_ref(v_opt_1479_);
v___x_1482_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(v_opts_1478_, v_name_1481_, v_val_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_opts_1483_, lean_object* v_opt_1484_, lean_object* v_val_1485_){
_start:
{
uint8_t v_val_boxed_1486_; lean_object* v_res_1487_; 
v_val_boxed_1486_ = lean_unbox(v_val_1485_);
v_res_1487_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_opts_1483_, v_opt_1484_, v_val_boxed_1486_);
return v_res_1487_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0));
v___x_1490_ = l_Lean_stringToMessageData(v___x_1489_);
return v___x_1490_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2));
v___x_1493_ = l_Lean_stringToMessageData(v___x_1492_);
return v___x_1493_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4));
v___x_1496_ = l_Lean_stringToMessageData(v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object* v_declName_1497_, lean_object* v_declNameNonRec_1498_, lean_object* v___x_1499_, lean_object* v___f_1500_, lean_object* v_a_1501_, lean_object* v___x_1502_, lean_object* v_____r_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___y_1510_; lean_object* v___y_1511_; uint8_t v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; uint8_t v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v_fileName_1521_; lean_object* v_fileMap_1522_; lean_object* v_currRecDepth_1523_; lean_object* v_ref_1524_; lean_object* v_currNamespace_1525_; lean_object* v_openDecls_1526_; lean_object* v_initHeartbeats_1527_; lean_object* v_maxHeartbeats_1528_; lean_object* v_quotContext_1529_; lean_object* v_currMacroScope_1530_; lean_object* v_cancelTk_x3f_1531_; uint8_t v_suppressElabErrors_1532_; lean_object* v_inheritedTraceOptions_1533_; lean_object* v___y_1534_; lean_object* v___y_1565_; lean_object* v___y_1566_; uint8_t v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; uint8_t v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; uint8_t v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; uint8_t v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; uint8_t v___y_1603_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; uint8_t v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; uint8_t v___y_1631_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___x_1709_; 
v___x_1709_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_1497_, v_declNameNonRec_1498_, v___x_1499_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___x_1749_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
lean_inc_ref(v___f_1500_);
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
v___x_1749_ = lean_apply_5(v___f_1500_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, lean_box(0));
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; uint8_t v___x_1751_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = lean_unbox(v_a_1750_);
lean_dec(v_a_1750_);
if (v___x_1751_ == 0)
{
v___y_1712_ = v___y_1504_;
v___y_1713_ = v___y_1505_;
v___y_1714_ = v___y_1506_;
v___y_1715_ = v___y_1507_;
goto v___jp_1711_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1752_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5);
lean_inc(v_a_1710_);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_a_1710_);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
lean_inc(v___x_1502_);
v___x_1755_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1502_, v___x_1754_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_dec_ref_known(v___x_1755_, 1);
v___y_1712_ = v___y_1504_;
v___y_1713_ = v___y_1505_;
v___y_1714_ = v___y_1506_;
v___y_1715_ = v___y_1507_;
goto v___jp_1711_;
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_a_1710_);
lean_dec(v___x_1502_);
lean_dec_ref(v_a_1501_);
lean_dec_ref(v___f_1500_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec(v_a_1710_);
lean_dec(v___x_1502_);
lean_dec_ref(v_a_1501_);
lean_dec_ref(v___f_1500_);
v_a_1764_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1749_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1749_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
v___jp_1711_:
{
lean_object* v___x_1716_; 
v___x_1716_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_a_1710_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
lean_inc(v___y_1715_);
lean_inc_ref(v___y_1714_);
lean_inc(v___y_1713_);
lean_inc_ref(v___y_1712_);
v___x_1718_ = lean_apply_5(v___f_1500_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, lean_box(0));
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; uint8_t v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = lean_unbox(v_a_1719_);
lean_dec(v_a_1719_);
if (v___x_1720_ == 0)
{
v___y_1699_ = v_a_1717_;
v___y_1700_ = v___y_1712_;
v___y_1701_ = v___y_1713_;
v___y_1702_ = v___y_1714_;
v___y_1703_ = v___y_1715_;
goto v___jp_1698_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1721_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3);
lean_inc(v_a_1717_);
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_a_1717_);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
lean_inc(v___x_1502_);
v___x_1724_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1502_, v___x_1723_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_dec_ref_known(v___x_1724_, 1);
v___y_1699_ = v_a_1717_;
v___y_1700_ = v___y_1712_;
v___y_1701_ = v___y_1713_;
v___y_1702_ = v___y_1714_;
v___y_1703_ = v___y_1715_;
goto v___jp_1698_;
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_a_1717_);
lean_dec(v___x_1502_);
lean_dec_ref(v_a_1501_);
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_a_1717_);
lean_dec(v___x_1502_);
lean_dec_ref(v_a_1501_);
v_a_1733_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1718_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1718_);
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
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v___x_1502_);
lean_dec_ref(v_a_1501_);
lean_dec_ref(v___f_1500_);
v_a_1741_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1716_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1716_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec(v___x_1502_);
lean_dec_ref(v_a_1501_);
lean_dec_ref(v___f_1500_);
v_a_1772_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1709_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1709_);
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
v___jp_1509_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1535_ = l_Lean_maxRecDepth;
v___x_1536_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___y_1513_, v___x_1535_);
lean_inc_ref(v_inheritedTraceOptions_1533_);
lean_inc(v_cancelTk_x3f_1531_);
lean_inc(v_currMacroScope_1530_);
lean_inc(v_quotContext_1529_);
lean_inc(v_maxHeartbeats_1528_);
lean_inc(v_initHeartbeats_1527_);
lean_inc(v_openDecls_1526_);
lean_inc(v_currNamespace_1525_);
lean_inc(v_ref_1524_);
lean_inc(v_currRecDepth_1523_);
lean_inc_ref(v_fileMap_1522_);
lean_inc_ref(v_fileName_1521_);
v___x_1537_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1537_, 0, v_fileName_1521_);
lean_ctor_set(v___x_1537_, 1, v_fileMap_1522_);
lean_ctor_set(v___x_1537_, 2, v___y_1513_);
lean_ctor_set(v___x_1537_, 3, v_currRecDepth_1523_);
lean_ctor_set(v___x_1537_, 4, v___x_1536_);
lean_ctor_set(v___x_1537_, 5, v_ref_1524_);
lean_ctor_set(v___x_1537_, 6, v_currNamespace_1525_);
lean_ctor_set(v___x_1537_, 7, v_openDecls_1526_);
lean_ctor_set(v___x_1537_, 8, v_initHeartbeats_1527_);
lean_ctor_set(v___x_1537_, 9, v_maxHeartbeats_1528_);
lean_ctor_set(v___x_1537_, 10, v_quotContext_1529_);
lean_ctor_set(v___x_1537_, 11, v_currMacroScope_1530_);
lean_ctor_set(v___x_1537_, 12, v_cancelTk_x3f_1531_);
lean_ctor_set(v___x_1537_, 13, v_inheritedTraceOptions_1533_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*14, v___y_1512_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*14 + 1, v_suppressElabErrors_1532_);
v___x_1538_ = l_Lean_MVarId_refl(v___y_1514_, v___y_1517_, v___y_1515_, v___y_1511_, v___x_1537_, v___y_1534_);
lean_dec_ref_known(v___x_1537_, 14);
lean_dec_ref(v___y_1515_);
if (lean_obj_tag(v___x_1538_) == 0)
{
uint8_t v_hasTrace_1539_; 
lean_dec_ref_known(v___x_1538_, 1);
v_hasTrace_1539_ = lean_ctor_get_uint8(v___y_1518_, sizeof(void*)*1);
if (v_hasTrace_1539_ == 0)
{
lean_object* v___x_1540_; 
lean_dec_ref(v___y_1518_);
lean_dec(v___x_1502_);
v___x_1540_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1501_, v___y_1511_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1541_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
lean_inc(v___x_1502_);
v___x_1542_ = l_Lean_Name_append(v___x_1541_, v___x_1502_);
v___x_1543_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1519_, v___y_1518_, v___x_1542_);
lean_dec(v___x_1542_);
lean_dec_ref(v___y_1518_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; 
lean_dec(v___x_1502_);
v___x_1544_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1501_, v___y_1511_);
return v___x_1544_;
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1);
v___x_1546_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1502_, v___x_1545_, v___y_1520_, v___y_1511_, v___y_1510_, v___y_1516_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1547_; 
lean_dec_ref_known(v___x_1546_, 1);
v___x_1547_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_1501_, v___y_1511_);
return v___x_1547_;
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec_ref(v_a_1501_);
v_a_1548_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1546_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1546_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec_ref(v___y_1518_);
lean_dec(v___x_1502_);
lean_dec_ref(v_a_1501_);
v_a_1556_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1538_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1538_);
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
v___jp_1564_:
{
lean_object* v_fileName_1578_; lean_object* v_fileMap_1579_; lean_object* v_currRecDepth_1580_; lean_object* v_ref_1581_; lean_object* v_currNamespace_1582_; lean_object* v_openDecls_1583_; lean_object* v_initHeartbeats_1584_; lean_object* v_maxHeartbeats_1585_; lean_object* v_quotContext_1586_; lean_object* v_currMacroScope_1587_; lean_object* v_cancelTk_x3f_1588_; uint8_t v_suppressElabErrors_1589_; lean_object* v_inheritedTraceOptions_1590_; 
v_fileName_1578_ = lean_ctor_get(v___y_1576_, 0);
v_fileMap_1579_ = lean_ctor_get(v___y_1576_, 1);
v_currRecDepth_1580_ = lean_ctor_get(v___y_1576_, 3);
v_ref_1581_ = lean_ctor_get(v___y_1576_, 5);
v_currNamespace_1582_ = lean_ctor_get(v___y_1576_, 6);
v_openDecls_1583_ = lean_ctor_get(v___y_1576_, 7);
v_initHeartbeats_1584_ = lean_ctor_get(v___y_1576_, 8);
v_maxHeartbeats_1585_ = lean_ctor_get(v___y_1576_, 9);
v_quotContext_1586_ = lean_ctor_get(v___y_1576_, 10);
v_currMacroScope_1587_ = lean_ctor_get(v___y_1576_, 11);
v_cancelTk_x3f_1588_ = lean_ctor_get(v___y_1576_, 12);
v_suppressElabErrors_1589_ = lean_ctor_get_uint8(v___y_1576_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1590_ = lean_ctor_get(v___y_1576_, 13);
v___y_1510_ = v___y_1565_;
v___y_1511_ = v___y_1566_;
v___y_1512_ = v___y_1567_;
v___y_1513_ = v___y_1568_;
v___y_1514_ = v___y_1569_;
v___y_1515_ = v___y_1570_;
v___y_1516_ = v___y_1571_;
v___y_1517_ = v___y_1572_;
v___y_1518_ = v___y_1573_;
v___y_1519_ = v___y_1574_;
v___y_1520_ = v___y_1575_;
v_fileName_1521_ = v_fileName_1578_;
v_fileMap_1522_ = v_fileMap_1579_;
v_currRecDepth_1523_ = v_currRecDepth_1580_;
v_ref_1524_ = v_ref_1581_;
v_currNamespace_1525_ = v_currNamespace_1582_;
v_openDecls_1526_ = v_openDecls_1583_;
v_initHeartbeats_1527_ = v_initHeartbeats_1584_;
v_maxHeartbeats_1528_ = v_maxHeartbeats_1585_;
v_quotContext_1529_ = v_quotContext_1586_;
v_currMacroScope_1530_ = v_currMacroScope_1587_;
v_cancelTk_x3f_1531_ = v_cancelTk_x3f_1588_;
v_suppressElabErrors_1532_ = v_suppressElabErrors_1589_;
v_inheritedTraceOptions_1533_ = v_inheritedTraceOptions_1590_;
v___y_1534_ = v___y_1577_;
goto v___jp_1509_;
}
v___jp_1591_:
{
if (v___y_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v_env_1605_; lean_object* v_nextMacroScope_1606_; lean_object* v_ngen_1607_; lean_object* v_auxDeclNGen_1608_; lean_object* v_traceState_1609_; lean_object* v_messages_1610_; lean_object* v_infoState_1611_; lean_object* v_snapshotTasks_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1622_; 
v___x_1604_ = lean_st_ref_take(v___y_1599_);
v_env_1605_ = lean_ctor_get(v___x_1604_, 0);
v_nextMacroScope_1606_ = lean_ctor_get(v___x_1604_, 1);
v_ngen_1607_ = lean_ctor_get(v___x_1604_, 2);
v_auxDeclNGen_1608_ = lean_ctor_get(v___x_1604_, 3);
v_traceState_1609_ = lean_ctor_get(v___x_1604_, 4);
v_messages_1610_ = lean_ctor_get(v___x_1604_, 6);
v_infoState_1611_ = lean_ctor_get(v___x_1604_, 7);
v_snapshotTasks_1612_ = lean_ctor_get(v___x_1604_, 8);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; 
v_unused_1623_ = lean_ctor_get(v___x_1604_, 5);
lean_dec(v_unused_1623_);
v___x_1614_ = v___x_1604_;
v_isShared_1615_ = v_isSharedCheck_1622_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_snapshotTasks_1612_);
lean_inc(v_infoState_1611_);
lean_inc(v_messages_1610_);
lean_inc(v_traceState_1609_);
lean_inc(v_auxDeclNGen_1608_);
lean_inc(v_ngen_1607_);
lean_inc(v_nextMacroScope_1606_);
lean_inc(v_env_1605_);
lean_dec(v___x_1604_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1622_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1616_ = l_Lean_Kernel_enableDiag(v_env_1605_, v___y_1595_);
v___x_1617_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 5, v___x_1617_);
lean_ctor_set(v___x_1614_, 0, v___x_1616_);
v___x_1619_ = v___x_1614_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_nextMacroScope_1606_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_ngen_1607_);
lean_ctor_set(v_reuseFailAlloc_1621_, 3, v_auxDeclNGen_1608_);
lean_ctor_set(v_reuseFailAlloc_1621_, 4, v_traceState_1609_);
lean_ctor_set(v_reuseFailAlloc_1621_, 5, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1621_, 6, v_messages_1610_);
lean_ctor_set(v_reuseFailAlloc_1621_, 7, v_infoState_1611_);
lean_ctor_set(v_reuseFailAlloc_1621_, 8, v_snapshotTasks_1612_);
v___x_1619_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_st_ref_set(v___y_1599_, v___x_1619_);
v___y_1565_ = v___y_1592_;
v___y_1566_ = v___y_1594_;
v___y_1567_ = v___y_1595_;
v___y_1568_ = v___y_1593_;
v___y_1569_ = v___y_1596_;
v___y_1570_ = v___y_1597_;
v___y_1571_ = v___y_1599_;
v___y_1572_ = v___y_1598_;
v___y_1573_ = v___y_1600_;
v___y_1574_ = v___y_1602_;
v___y_1575_ = v___y_1601_;
v___y_1576_ = v___y_1592_;
v___y_1577_ = v___y_1599_;
goto v___jp_1564_;
}
}
}
else
{
v___y_1565_ = v___y_1592_;
v___y_1566_ = v___y_1594_;
v___y_1567_ = v___y_1595_;
v___y_1568_ = v___y_1593_;
v___y_1569_ = v___y_1596_;
v___y_1570_ = v___y_1597_;
v___y_1571_ = v___y_1599_;
v___y_1572_ = v___y_1598_;
v___y_1573_ = v___y_1600_;
v___y_1574_ = v___y_1602_;
v___y_1575_ = v___y_1601_;
v___y_1576_ = v___y_1592_;
v___y_1577_ = v___y_1599_;
goto v___jp_1564_;
}
}
v___jp_1624_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v_foApprox_1634_; uint8_t v_ctxApprox_1635_; uint8_t v_quasiPatternApprox_1636_; uint8_t v_constApprox_1637_; uint8_t v_isDefEqStuckEx_1638_; uint8_t v_unificationHints_1639_; uint8_t v_proofIrrelevance_1640_; uint8_t v_assignSyntheticOpaque_1641_; uint8_t v_offsetCnstrs_1642_; uint8_t v_etaStruct_1643_; uint8_t v_univApprox_1644_; uint8_t v_iota_1645_; uint8_t v_beta_1646_; uint8_t v_proj_1647_; uint8_t v_zeta_1648_; uint8_t v_zetaDelta_1649_; uint8_t v_zetaUnused_1650_; uint8_t v_zetaHave_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1697_; 
v___x_1632_ = lean_st_ref_get(v___y_1629_);
v___x_1633_ = l_Lean_Meta_Context_config(v___y_1630_);
v_foApprox_1634_ = lean_ctor_get_uint8(v___x_1633_, 0);
v_ctxApprox_1635_ = lean_ctor_get_uint8(v___x_1633_, 1);
v_quasiPatternApprox_1636_ = lean_ctor_get_uint8(v___x_1633_, 2);
v_constApprox_1637_ = lean_ctor_get_uint8(v___x_1633_, 3);
v_isDefEqStuckEx_1638_ = lean_ctor_get_uint8(v___x_1633_, 4);
v_unificationHints_1639_ = lean_ctor_get_uint8(v___x_1633_, 5);
v_proofIrrelevance_1640_ = lean_ctor_get_uint8(v___x_1633_, 6);
v_assignSyntheticOpaque_1641_ = lean_ctor_get_uint8(v___x_1633_, 7);
v_offsetCnstrs_1642_ = lean_ctor_get_uint8(v___x_1633_, 8);
v_etaStruct_1643_ = lean_ctor_get_uint8(v___x_1633_, 10);
v_univApprox_1644_ = lean_ctor_get_uint8(v___x_1633_, 11);
v_iota_1645_ = lean_ctor_get_uint8(v___x_1633_, 12);
v_beta_1646_ = lean_ctor_get_uint8(v___x_1633_, 13);
v_proj_1647_ = lean_ctor_get_uint8(v___x_1633_, 14);
v_zeta_1648_ = lean_ctor_get_uint8(v___x_1633_, 15);
v_zetaDelta_1649_ = lean_ctor_get_uint8(v___x_1633_, 16);
v_zetaUnused_1650_ = lean_ctor_get_uint8(v___x_1633_, 17);
v_zetaHave_1651_ = lean_ctor_get_uint8(v___x_1633_, 18);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1653_ = v___x_1633_;
v_isShared_1654_ = v_isSharedCheck_1697_;
goto v_resetjp_1652_;
}
else
{
lean_dec(v___x_1633_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1697_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
uint8_t v_trackZetaDelta_1655_; lean_object* v_zetaDeltaSet_1656_; lean_object* v_lctx_1657_; lean_object* v_localInstances_1658_; lean_object* v_defEqCtx_x3f_1659_; lean_object* v_synthPendingDepth_1660_; lean_object* v_canUnfold_x3f_1661_; uint8_t v_univApprox_1662_; uint8_t v_inTypeClassResolution_1663_; uint8_t v_cacheInferType_1664_; lean_object* v_fileName_1665_; lean_object* v_fileMap_1666_; lean_object* v_options_1667_; lean_object* v_currRecDepth_1668_; lean_object* v_ref_1669_; lean_object* v_currNamespace_1670_; lean_object* v_openDecls_1671_; lean_object* v_initHeartbeats_1672_; lean_object* v_maxHeartbeats_1673_; lean_object* v_quotContext_1674_; lean_object* v_currMacroScope_1675_; lean_object* v_cancelTk_x3f_1676_; uint8_t v_suppressElabErrors_1677_; lean_object* v_inheritedTraceOptions_1678_; lean_object* v_env_1679_; lean_object* v_config_1681_; 
v_trackZetaDelta_1655_ = lean_ctor_get_uint8(v___y_1630_, sizeof(void*)*7);
v_zetaDeltaSet_1656_ = lean_ctor_get(v___y_1630_, 1);
v_lctx_1657_ = lean_ctor_get(v___y_1630_, 2);
v_localInstances_1658_ = lean_ctor_get(v___y_1630_, 3);
v_defEqCtx_x3f_1659_ = lean_ctor_get(v___y_1630_, 4);
v_synthPendingDepth_1660_ = lean_ctor_get(v___y_1630_, 5);
v_canUnfold_x3f_1661_ = lean_ctor_get(v___y_1630_, 6);
v_univApprox_1662_ = lean_ctor_get_uint8(v___y_1630_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1663_ = lean_ctor_get_uint8(v___y_1630_, sizeof(void*)*7 + 2);
v_cacheInferType_1664_ = lean_ctor_get_uint8(v___y_1630_, sizeof(void*)*7 + 3);
v_fileName_1665_ = lean_ctor_get(v___y_1625_, 0);
v_fileMap_1666_ = lean_ctor_get(v___y_1625_, 1);
v_options_1667_ = lean_ctor_get(v___y_1625_, 2);
v_currRecDepth_1668_ = lean_ctor_get(v___y_1625_, 3);
v_ref_1669_ = lean_ctor_get(v___y_1625_, 5);
v_currNamespace_1670_ = lean_ctor_get(v___y_1625_, 6);
v_openDecls_1671_ = lean_ctor_get(v___y_1625_, 7);
v_initHeartbeats_1672_ = lean_ctor_get(v___y_1625_, 8);
v_maxHeartbeats_1673_ = lean_ctor_get(v___y_1625_, 9);
v_quotContext_1674_ = lean_ctor_get(v___y_1625_, 10);
v_currMacroScope_1675_ = lean_ctor_get(v___y_1625_, 11);
v_cancelTk_x3f_1676_ = lean_ctor_get(v___y_1625_, 12);
v_suppressElabErrors_1677_ = lean_ctor_get_uint8(v___y_1625_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1678_ = lean_ctor_get(v___y_1625_, 13);
v_env_1679_ = lean_ctor_get(v___x_1632_, 0);
lean_inc_ref(v_env_1679_);
lean_dec(v___x_1632_);
if (v_isShared_1654_ == 0)
{
v_config_1681_ = v___x_1653_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 0, v_foApprox_1634_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 1, v_ctxApprox_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 2, v_quasiPatternApprox_1636_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 3, v_constApprox_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 4, v_isDefEqStuckEx_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 5, v_unificationHints_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 6, v_proofIrrelevance_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 7, v_assignSyntheticOpaque_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 8, v_offsetCnstrs_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 10, v_etaStruct_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 11, v_univApprox_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 12, v_iota_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 13, v_beta_1646_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 14, v_proj_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 15, v_zeta_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 16, v_zetaDelta_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 17, v_zetaUnused_1650_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, 18, v_zetaHave_1651_);
v_config_1681_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
uint64_t v___x_1682_; uint64_t v___x_1683_; uint64_t v___x_1684_; uint64_t v___x_1685_; uint64_t v___x_1686_; uint64_t v_key_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; uint8_t v___x_1695_; 
lean_ctor_set_uint8(v_config_1681_, 9, v___y_1631_);
v___x_1682_ = l_Lean_Meta_Context_configKey(v___y_1630_);
v___x_1683_ = 3ULL;
v___x_1684_ = lean_uint64_shift_right(v___x_1682_, v___x_1683_);
v___x_1685_ = lean_uint64_shift_left(v___x_1684_, v___x_1683_);
v___x_1686_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1631_);
v_key_1687_ = lean_uint64_lor(v___x_1685_, v___x_1686_);
v___x_1688_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1688_, 0, v_config_1681_);
lean_ctor_set_uint64(v___x_1688_, sizeof(void*)*1, v_key_1687_);
lean_inc(v_canUnfold_x3f_1661_);
lean_inc(v_synthPendingDepth_1660_);
lean_inc(v_defEqCtx_x3f_1659_);
lean_inc_ref(v_localInstances_1658_);
lean_inc_ref(v_lctx_1657_);
lean_inc(v_zetaDeltaSet_1656_);
v___x_1689_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v_zetaDeltaSet_1656_);
lean_ctor_set(v___x_1689_, 2, v_lctx_1657_);
lean_ctor_set(v___x_1689_, 3, v_localInstances_1658_);
lean_ctor_set(v___x_1689_, 4, v_defEqCtx_x3f_1659_);
lean_ctor_set(v___x_1689_, 5, v_synthPendingDepth_1660_);
lean_ctor_set(v___x_1689_, 6, v_canUnfold_x3f_1661_);
lean_ctor_set_uint8(v___x_1689_, sizeof(void*)*7, v_trackZetaDelta_1655_);
lean_ctor_set_uint8(v___x_1689_, sizeof(void*)*7 + 1, v_univApprox_1662_);
lean_ctor_set_uint8(v___x_1689_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1663_);
lean_ctor_set_uint8(v___x_1689_, sizeof(void*)*7 + 3, v_cacheInferType_1664_);
v___x_1690_ = l_Lean_Meta_smartUnfolding;
v___x_1691_ = 0;
lean_inc_ref(v_options_1667_);
v___x_1692_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_1667_, v___x_1690_, v___x_1691_);
v___x_1693_ = l_Lean_diagnostics;
v___x_1694_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_1692_, v___x_1693_);
v___x_1695_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1679_);
lean_dec_ref(v_env_1679_);
if (v___x_1695_ == 0)
{
if (v___x_1694_ == 0)
{
lean_inc_ref(v_options_1667_);
v___y_1510_ = v___y_1625_;
v___y_1511_ = v___y_1626_;
v___y_1512_ = v___x_1694_;
v___y_1513_ = v___x_1692_;
v___y_1514_ = v___y_1627_;
v___y_1515_ = v___x_1689_;
v___y_1516_ = v___y_1629_;
v___y_1517_ = v___y_1628_;
v___y_1518_ = v_options_1667_;
v___y_1519_ = v_inheritedTraceOptions_1678_;
v___y_1520_ = v___y_1630_;
v_fileName_1521_ = v_fileName_1665_;
v_fileMap_1522_ = v_fileMap_1666_;
v_currRecDepth_1523_ = v_currRecDepth_1668_;
v_ref_1524_ = v_ref_1669_;
v_currNamespace_1525_ = v_currNamespace_1670_;
v_openDecls_1526_ = v_openDecls_1671_;
v_initHeartbeats_1527_ = v_initHeartbeats_1672_;
v_maxHeartbeats_1528_ = v_maxHeartbeats_1673_;
v_quotContext_1529_ = v_quotContext_1674_;
v_currMacroScope_1530_ = v_currMacroScope_1675_;
v_cancelTk_x3f_1531_ = v_cancelTk_x3f_1676_;
v_suppressElabErrors_1532_ = v_suppressElabErrors_1677_;
v_inheritedTraceOptions_1533_ = v_inheritedTraceOptions_1678_;
v___y_1534_ = v___y_1629_;
goto v___jp_1509_;
}
else
{
lean_inc_ref(v_options_1667_);
v___y_1592_ = v___y_1625_;
v___y_1593_ = v___x_1692_;
v___y_1594_ = v___y_1626_;
v___y_1595_ = v___x_1694_;
v___y_1596_ = v___y_1627_;
v___y_1597_ = v___x_1689_;
v___y_1598_ = v___y_1628_;
v___y_1599_ = v___y_1629_;
v___y_1600_ = v_options_1667_;
v___y_1601_ = v___y_1630_;
v___y_1602_ = v_inheritedTraceOptions_1678_;
v___y_1603_ = v___x_1695_;
goto v___jp_1591_;
}
}
else
{
lean_inc_ref(v_options_1667_);
v___y_1592_ = v___y_1625_;
v___y_1593_ = v___x_1692_;
v___y_1594_ = v___y_1626_;
v___y_1595_ = v___x_1694_;
v___y_1596_ = v___y_1627_;
v___y_1597_ = v___x_1689_;
v___y_1598_ = v___y_1628_;
v___y_1599_ = v___y_1629_;
v___y_1600_ = v_options_1667_;
v___y_1601_ = v___y_1630_;
v___y_1602_ = v_inheritedTraceOptions_1678_;
v___y_1603_ = v___x_1694_;
goto v___jp_1591_;
}
}
}
}
v___jp_1698_:
{
lean_object* v___x_1704_; uint8_t v_transparency_1705_; uint8_t v___x_1706_; uint8_t v___x_1707_; uint8_t v___x_1708_; 
v___x_1704_ = l_Lean_Meta_Context_config(v___y_1700_);
v_transparency_1705_ = lean_ctor_get_uint8(v___x_1704_, 9);
lean_dec_ref(v___x_1704_);
v___x_1706_ = 0;
v___x_1707_ = 1;
v___x_1708_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1705_, v___x_1706_);
if (v___x_1708_ == 0)
{
v___y_1625_ = v___y_1702_;
v___y_1626_ = v___y_1701_;
v___y_1627_ = v___y_1699_;
v___y_1628_ = v___x_1707_;
v___y_1629_ = v___y_1703_;
v___y_1630_ = v___y_1700_;
v___y_1631_ = v_transparency_1705_;
goto v___jp_1624_;
}
else
{
v___y_1625_ = v___y_1702_;
v___y_1626_ = v___y_1701_;
v___y_1627_ = v___y_1699_;
v___y_1628_ = v___x_1707_;
v___y_1629_ = v___y_1703_;
v___y_1630_ = v___y_1700_;
v___y_1631_ = v___x_1706_;
goto v___jp_1624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object* v_declName_1780_, lean_object* v_declNameNonRec_1781_, lean_object* v___x_1782_, lean_object* v___f_1783_, lean_object* v_a_1784_, lean_object* v___x_1785_, lean_object* v_____r_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1780_, v_declNameNonRec_1781_, v___x_1782_, v___f_1783_, v_a_1784_, v___x_1785_, v_____r_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1792_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0));
v___x_1795_ = l_Lean_stringToMessageData(v___x_1794_);
return v___x_1795_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2));
v___x_1798_ = l_Lean_stringToMessageData(v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8));
v___x_1809_ = l_Lean_stringToMessageData(v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object* v_declName_1810_, lean_object* v_a_1811_, lean_object* v___x_1812_, lean_object* v_declNameNonRec_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___y_1820_; lean_object* v___y_1821_; uint8_t v___y_1822_; lean_object* v___y_1832_; lean_object* v_a_1833_; lean_object* v___y_1837_; lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1811_, v___x_1812_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1841_; lean_object* v___f_1842_; lean_object* v___x_1843_; lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1868_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v___x_1841_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6));
v___f_1842_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7));
v___x_1843_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_1841_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1868_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1868_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = l_Lean_Expr_mvarId_x21(v_a_1840_);
v___x_1849_ = lean_unbox(v_a_1844_);
lean_dec(v_a_1844_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_del_object(v___x_1846_);
v___x_1850_ = lean_box(0);
lean_inc(v_declName_1810_);
v___x_1851_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1810_, v_declNameNonRec_1813_, v___x_1848_, v___f_1842_, v_a_1840_, v___x_1841_, v___x_1850_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
v___y_1837_ = v___x_1851_;
goto v___jp_1836_;
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9);
lean_inc(v___x_1848_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set_tag(v___x_1846_, 1);
lean_ctor_set(v___x_1846_, 0, v___x_1848_);
v___x_1854_ = v___x_1846_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1848_);
v___x_1854_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1852_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_1841_, v___x_1855_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 1);
lean_inc(v_declName_1810_);
v___x_1858_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_1810_, v_declNameNonRec_1813_, v___x_1848_, v___f_1842_, v_a_1840_, v___x_1841_, v_a_1857_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
v___y_1837_ = v___x_1858_;
goto v___jp_1836_;
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v___x_1848_);
lean_dec(v_a_1840_);
lean_dec(v_declNameNonRec_1813_);
v_a_1859_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1856_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1856_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
lean_inc(v_a_1859_);
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
v___y_1832_ = v___x_1864_;
v_a_1833_ = v_a_1859_;
goto v___jp_1831_;
}
}
}
}
}
}
}
else
{
lean_dec(v_declNameNonRec_1813_);
v___y_1837_ = v___x_1839_;
goto v___jp_1836_;
}
v___jp_1819_:
{
if (v___y_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec_ref(v___y_1820_);
v___x_1823_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1);
v___x_1824_ = l_Lean_MessageData_ofConstName(v_declName_1810_, v___y_1822_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = l_Lean_Exception_toMessageData(v___y_1821_);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1827_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_1829_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
return v___x_1830_;
}
else
{
lean_dec_ref(v___y_1821_);
lean_dec(v_declName_1810_);
return v___y_1820_;
}
}
v___jp_1831_:
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Lean_Exception_isInterrupt(v_a_1833_);
if (v___x_1834_ == 0)
{
uint8_t v___x_1835_; 
lean_inc_ref(v_a_1833_);
v___x_1835_ = l_Lean_Exception_isRuntime(v_a_1833_);
v___y_1820_ = v___y_1832_;
v___y_1821_ = v_a_1833_;
v___y_1822_ = v___x_1835_;
goto v___jp_1819_;
}
else
{
v___y_1820_ = v___y_1832_;
v___y_1821_ = v_a_1833_;
v___y_1822_ = v___x_1834_;
goto v___jp_1819_;
}
}
v___jp_1836_:
{
if (lean_obj_tag(v___y_1837_) == 0)
{
lean_dec(v_declName_1810_);
return v___y_1837_;
}
else
{
lean_object* v_a_1838_; 
v_a_1838_ = lean_ctor_get(v___y_1837_, 0);
lean_inc(v_a_1838_);
v___y_1832_ = v___y_1837_;
v_a_1833_ = v_a_1838_;
goto v___jp_1831_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object* v_declName_1869_, lean_object* v_a_1870_, lean_object* v___x_1871_, lean_object* v_declNameNonRec_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_declName_1869_, v_a_1870_, v___x_1871_, v_declNameNonRec_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
if (lean_obj_tag(v_a_1879_) == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = l_List_reverse___redArg(v_a_1880_);
return v___x_1881_;
}
else
{
lean_object* v_head_1882_; lean_object* v_tail_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1892_; 
v_head_1882_ = lean_ctor_get(v_a_1879_, 0);
v_tail_1883_ = lean_ctor_get(v_a_1879_, 1);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_a_1879_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1885_ = v_a_1879_;
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_tail_1883_);
lean_inc(v_head_1882_);
lean_dec(v_a_1879_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = l_Lean_mkLevelParam(v_head_1882_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v_a_1880_);
lean_ctor_set(v___x_1885_, 0, v___x_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_a_1880_);
v___x_1889_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
v_a_1879_ = v_tail_1883_;
v_a_1880_ = v___x_1889_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(lean_object* v_levelParams_1893_, lean_object* v_declName_1894_, lean_object* v_declNameNonRec_1895_, lean_object* v_name_1896_, lean_object* v_xs_1897_, lean_object* v_body_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; lean_object* v_us_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1904_ = lean_box(0);
lean_inc(v_levelParams_1893_);
v_us_1905_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_levelParams_1893_, v___x_1904_);
lean_inc(v_declName_1894_);
v___x_1906_ = l_Lean_mkConst(v_declName_1894_, v_us_1905_);
v___x_1907_ = l_Lean_mkAppN(v___x_1906_, v_xs_1897_);
v___x_1908_ = l_Lean_Meta_mkEq(v___x_1907_, v_body_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; lean_object* v___f_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc_n(v_a_1909_, 2);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1910_ = lean_box(0);
v___f_1911_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1911_, 0, v_declName_1894_);
lean_closure_set(v___f_1911_, 1, v_a_1909_);
lean_closure_set(v___f_1911_, 2, v___x_1910_);
lean_closure_set(v___f_1911_, 3, v_declNameNonRec_1895_);
v___x_1912_ = 0;
v___x_1913_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v___f_1911_, v___x_1912_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; uint8_t v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = 1;
v___x_1916_ = 1;
v___x_1917_ = l_Lean_Meta_mkForallFVars(v_xs_1897_, v_a_1909_, v___x_1912_, v___x_1915_, v___x_1915_, v___x_1916_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = l_Lean_Meta_letToHave(v_a_1918_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = l_Lean_Meta_mkLambdaFVars(v_xs_1897_, v_a_1914_, v___x_1912_, v___x_1915_, v___x_1912_, v___x_1915_, v___x_1916_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
lean_inc(v_name_1896_);
v___x_1923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1923_, 0, v_name_1896_);
lean_ctor_set(v___x_1923_, 1, v_levelParams_1893_);
lean_ctor_set(v___x_1923_, 2, v_a_1920_);
v___x_1924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_name_1896_);
lean_ctor_set(v___x_1924_, 1, v___x_1904_);
v___x_1925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v_a_1922_);
lean_ctor_set(v___x_1925_, 2, v___x_1924_);
v___x_1926_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v___x_1925_, v___y_1902_);
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref(v___x_1926_);
v___x_1928_ = l_Lean_addDecl(v_a_1927_, v___x_1912_, v___y_1901_, v___y_1902_);
return v___x_1928_;
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v_a_1920_);
lean_dec(v_name_1896_);
lean_dec(v_levelParams_1893_);
v_a_1929_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1921_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1921_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec(v_a_1914_);
lean_dec(v_name_1896_);
lean_dec(v_levelParams_1893_);
v_a_1937_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1919_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1919_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_a_1914_);
lean_dec(v_name_1896_);
lean_dec(v_levelParams_1893_);
v_a_1945_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1917_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1917_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_a_1909_);
lean_dec(v_name_1896_);
lean_dec(v_levelParams_1893_);
v_a_1953_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1913_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1913_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v_name_1896_);
lean_dec(v_declNameNonRec_1895_);
lean_dec(v_declName_1894_);
lean_dec(v_levelParams_1893_);
v_a_1961_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1908_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1908_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed(lean_object* v_levelParams_1969_, lean_object* v_declName_1970_, lean_object* v_declNameNonRec_1971_, lean_object* v_name_1972_, lean_object* v_xs_1973_, lean_object* v_body_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(v_levelParams_1969_, v_declName_1970_, v_declNameNonRec_1971_, v_name_1972_, v_xs_1973_, v_body_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec_ref(v_xs_1973_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object* v_declName_1981_, lean_object* v_info_1982_, lean_object* v_name_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v___x_1989_; lean_object* v_levelParams_1990_; lean_object* v_value_1991_; lean_object* v_declNameNonRec_1992_; lean_object* v_fileName_1993_; lean_object* v_fileMap_1994_; lean_object* v_options_1995_; lean_object* v_currRecDepth_1996_; lean_object* v_ref_1997_; lean_object* v_currNamespace_1998_; lean_object* v_openDecls_1999_; lean_object* v_initHeartbeats_2000_; lean_object* v_maxHeartbeats_2001_; lean_object* v_quotContext_2002_; lean_object* v_currMacroScope_2003_; lean_object* v_cancelTk_x3f_2004_; uint8_t v_suppressElabErrors_2005_; lean_object* v_inheritedTraceOptions_2006_; lean_object* v_env_2007_; lean_object* v___f_2008_; uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; lean_object* v_fileName_2015_; lean_object* v_fileMap_2016_; lean_object* v_currRecDepth_2017_; lean_object* v_ref_2018_; lean_object* v_currNamespace_2019_; lean_object* v_openDecls_2020_; lean_object* v_initHeartbeats_2021_; lean_object* v_maxHeartbeats_2022_; lean_object* v_quotContext_2023_; lean_object* v_currMacroScope_2024_; lean_object* v_cancelTk_x3f_2025_; uint8_t v_suppressElabErrors_2026_; lean_object* v_inheritedTraceOptions_2027_; lean_object* v___y_2028_; uint8_t v___y_2034_; uint8_t v___x_2055_; 
v___x_1989_ = lean_st_ref_get(v_a_1987_);
v_levelParams_1990_ = lean_ctor_get(v_info_1982_, 1);
lean_inc(v_levelParams_1990_);
v_value_1991_ = lean_ctor_get(v_info_1982_, 3);
lean_inc_ref(v_value_1991_);
v_declNameNonRec_1992_ = lean_ctor_get(v_info_1982_, 5);
lean_inc(v_declNameNonRec_1992_);
lean_dec_ref(v_info_1982_);
v_fileName_1993_ = lean_ctor_get(v_a_1986_, 0);
v_fileMap_1994_ = lean_ctor_get(v_a_1986_, 1);
v_options_1995_ = lean_ctor_get(v_a_1986_, 2);
v_currRecDepth_1996_ = lean_ctor_get(v_a_1986_, 3);
v_ref_1997_ = lean_ctor_get(v_a_1986_, 5);
v_currNamespace_1998_ = lean_ctor_get(v_a_1986_, 6);
v_openDecls_1999_ = lean_ctor_get(v_a_1986_, 7);
v_initHeartbeats_2000_ = lean_ctor_get(v_a_1986_, 8);
v_maxHeartbeats_2001_ = lean_ctor_get(v_a_1986_, 9);
v_quotContext_2002_ = lean_ctor_get(v_a_1986_, 10);
v_currMacroScope_2003_ = lean_ctor_get(v_a_1986_, 11);
v_cancelTk_x3f_2004_ = lean_ctor_get(v_a_1986_, 12);
v_suppressElabErrors_2005_ = lean_ctor_get_uint8(v_a_1986_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2006_ = lean_ctor_get(v_a_1986_, 13);
v_env_2007_ = lean_ctor_get(v___x_1989_, 0);
lean_inc_ref(v_env_2007_);
lean_dec(v___x_1989_);
v___f_2008_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed), 11, 4);
lean_closure_set(v___f_2008_, 0, v_levelParams_1990_);
lean_closure_set(v___f_2008_, 1, v_declName_1981_);
lean_closure_set(v___f_2008_, 2, v_declNameNonRec_1992_);
lean_closure_set(v___f_2008_, 3, v_name_1983_);
v___x_2009_ = 0;
v___x_2010_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_1995_);
v___x_2011_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_1995_, v___x_2010_, v___x_2009_);
v___x_2012_ = l_Lean_diagnostics;
v___x_2013_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_2011_, v___x_2012_);
v___x_2055_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2007_);
lean_dec_ref(v_env_2007_);
if (v___x_2055_ == 0)
{
if (v___x_2013_ == 0)
{
v_fileName_2015_ = v_fileName_1993_;
v_fileMap_2016_ = v_fileMap_1994_;
v_currRecDepth_2017_ = v_currRecDepth_1996_;
v_ref_2018_ = v_ref_1997_;
v_currNamespace_2019_ = v_currNamespace_1998_;
v_openDecls_2020_ = v_openDecls_1999_;
v_initHeartbeats_2021_ = v_initHeartbeats_2000_;
v_maxHeartbeats_2022_ = v_maxHeartbeats_2001_;
v_quotContext_2023_ = v_quotContext_2002_;
v_currMacroScope_2024_ = v_currMacroScope_2003_;
v_cancelTk_x3f_2025_ = v_cancelTk_x3f_2004_;
v_suppressElabErrors_2026_ = v_suppressElabErrors_2005_;
v_inheritedTraceOptions_2027_ = v_inheritedTraceOptions_2006_;
v___y_2028_ = v_a_1987_;
goto v___jp_2014_;
}
else
{
v___y_2034_ = v___x_2055_;
goto v___jp_2033_;
}
}
else
{
v___y_2034_ = v___x_2013_;
goto v___jp_2033_;
}
v___jp_2014_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2029_ = l_Lean_maxRecDepth;
v___x_2030_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___x_2011_, v___x_2029_);
lean_inc_ref(v_inheritedTraceOptions_2027_);
lean_inc(v_cancelTk_x3f_2025_);
lean_inc(v_currMacroScope_2024_);
lean_inc(v_quotContext_2023_);
lean_inc(v_maxHeartbeats_2022_);
lean_inc(v_initHeartbeats_2021_);
lean_inc(v_openDecls_2020_);
lean_inc(v_currNamespace_2019_);
lean_inc(v_ref_2018_);
lean_inc(v_currRecDepth_2017_);
lean_inc_ref(v_fileMap_2016_);
lean_inc_ref(v_fileName_2015_);
v___x_2031_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2031_, 0, v_fileName_2015_);
lean_ctor_set(v___x_2031_, 1, v_fileMap_2016_);
lean_ctor_set(v___x_2031_, 2, v___x_2011_);
lean_ctor_set(v___x_2031_, 3, v_currRecDepth_2017_);
lean_ctor_set(v___x_2031_, 4, v___x_2030_);
lean_ctor_set(v___x_2031_, 5, v_ref_2018_);
lean_ctor_set(v___x_2031_, 6, v_currNamespace_2019_);
lean_ctor_set(v___x_2031_, 7, v_openDecls_2020_);
lean_ctor_set(v___x_2031_, 8, v_initHeartbeats_2021_);
lean_ctor_set(v___x_2031_, 9, v_maxHeartbeats_2022_);
lean_ctor_set(v___x_2031_, 10, v_quotContext_2023_);
lean_ctor_set(v___x_2031_, 11, v_currMacroScope_2024_);
lean_ctor_set(v___x_2031_, 12, v_cancelTk_x3f_2025_);
lean_ctor_set(v___x_2031_, 13, v_inheritedTraceOptions_2027_);
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*14, v___x_2013_);
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*14 + 1, v_suppressElabErrors_2026_);
v___x_2032_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_value_1991_, v___f_2008_, v___x_2009_, v_a_1984_, v_a_1985_, v___x_2031_, v___y_2028_);
lean_dec_ref_known(v___x_2031_, 14);
return v___x_2032_;
}
v___jp_2033_:
{
if (v___y_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v_env_2036_; lean_object* v_nextMacroScope_2037_; lean_object* v_ngen_2038_; lean_object* v_auxDeclNGen_2039_; lean_object* v_traceState_2040_; lean_object* v_messages_2041_; lean_object* v_infoState_2042_; lean_object* v_snapshotTasks_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2053_; 
v___x_2035_ = lean_st_ref_take(v_a_1987_);
v_env_2036_ = lean_ctor_get(v___x_2035_, 0);
v_nextMacroScope_2037_ = lean_ctor_get(v___x_2035_, 1);
v_ngen_2038_ = lean_ctor_get(v___x_2035_, 2);
v_auxDeclNGen_2039_ = lean_ctor_get(v___x_2035_, 3);
v_traceState_2040_ = lean_ctor_get(v___x_2035_, 4);
v_messages_2041_ = lean_ctor_get(v___x_2035_, 6);
v_infoState_2042_ = lean_ctor_get(v___x_2035_, 7);
v_snapshotTasks_2043_ = lean_ctor_get(v___x_2035_, 8);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v___x_2035_, 5);
lean_dec(v_unused_2054_);
v___x_2045_ = v___x_2035_;
v_isShared_2046_ = v_isSharedCheck_2053_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_snapshotTasks_2043_);
lean_inc(v_infoState_2042_);
lean_inc(v_messages_2041_);
lean_inc(v_traceState_2040_);
lean_inc(v_auxDeclNGen_2039_);
lean_inc(v_ngen_2038_);
lean_inc(v_nextMacroScope_2037_);
lean_inc(v_env_2036_);
lean_dec(v___x_2035_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2053_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2047_ = l_Lean_Kernel_enableDiag(v_env_2036_, v___x_2013_);
v___x_2048_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2, &l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 5, v___x_2048_);
lean_ctor_set(v___x_2045_, 0, v___x_2047_);
v___x_2050_ = v___x_2045_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_nextMacroScope_2037_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_ngen_2038_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v_auxDeclNGen_2039_);
lean_ctor_set(v_reuseFailAlloc_2052_, 4, v_traceState_2040_);
lean_ctor_set(v_reuseFailAlloc_2052_, 5, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2052_, 6, v_messages_2041_);
lean_ctor_set(v_reuseFailAlloc_2052_, 7, v_infoState_2042_);
lean_ctor_set(v_reuseFailAlloc_2052_, 8, v_snapshotTasks_2043_);
v___x_2050_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_st_ref_set(v_a_1987_, v___x_2050_);
v_fileName_2015_ = v_fileName_1993_;
v_fileMap_2016_ = v_fileMap_1994_;
v_currRecDepth_2017_ = v_currRecDepth_1996_;
v_ref_2018_ = v_ref_1997_;
v_currNamespace_2019_ = v_currNamespace_1998_;
v_openDecls_2020_ = v_openDecls_1999_;
v_initHeartbeats_2021_ = v_initHeartbeats_2000_;
v_maxHeartbeats_2022_ = v_maxHeartbeats_2001_;
v_quotContext_2023_ = v_quotContext_2002_;
v_currMacroScope_2024_ = v_currMacroScope_2003_;
v_cancelTk_x3f_2025_ = v_cancelTk_x3f_2004_;
v_suppressElabErrors_2026_ = v_suppressElabErrors_2005_;
v_inheritedTraceOptions_2027_ = v_inheritedTraceOptions_2006_;
v___y_2028_ = v_a_1987_;
goto v___jp_2014_;
}
}
}
else
{
v_fileName_2015_ = v_fileName_1993_;
v_fileMap_2016_ = v_fileMap_1994_;
v_currRecDepth_2017_ = v_currRecDepth_1996_;
v_ref_2018_ = v_ref_1997_;
v_currNamespace_2019_ = v_currNamespace_1998_;
v_openDecls_2020_ = v_openDecls_1999_;
v_initHeartbeats_2021_ = v_initHeartbeats_2000_;
v_maxHeartbeats_2022_ = v_maxHeartbeats_2001_;
v_quotContext_2023_ = v_quotContext_2002_;
v_currMacroScope_2024_ = v_currMacroScope_2003_;
v_cancelTk_x3f_2025_ = v_cancelTk_x3f_2004_;
v_suppressElabErrors_2026_ = v_suppressElabErrors_2005_;
v_inheritedTraceOptions_2027_ = v_inheritedTraceOptions_2006_;
v___y_2028_ = v_a_1987_;
goto v___jp_2014_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_2056_, lean_object* v_info_2057_, lean_object* v_name_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_2056_, v_info_2057_, v_name_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* v_declName_2065_, lean_object* v_info_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2072_; lean_object* v_env_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2072_ = lean_st_ref_get(v_a_2070_);
v_env_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc_ref(v_env_2073_);
lean_dec(v___x_2072_);
v___x_2074_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc_n(v_declName_2065_, 2);
v___x_2075_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2073_, v_declName_2065_, v___x_2074_);
lean_inc_n(v___x_2075_, 2);
v___x_2076_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_2076_, 0, v_declName_2065_);
lean_closure_set(v___x_2076_, 1, v_info_2066_);
lean_closure_set(v___x_2076_, 2, v___x_2075_);
v___x_2077_ = l_Lean_Meta_realizeConst(v_declName_2065_, v___x_2075_, v___x_2076_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2084_ == 0)
{
lean_object* v_unused_2085_; 
v_unused_2085_ = lean_ctor_get(v___x_2077_, 0);
lean_dec(v_unused_2085_);
v___x_2079_ = v___x_2077_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_dec(v___x_2077_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2075_);
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2075_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v___x_2075_);
v_a_2086_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2077_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2077_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object* v_declName_2094_, lean_object* v_info_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2094_, v_info_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* v_declName_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v_env_2110_; lean_object* v_env_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; uint8_t v___x_2115_; 
v___x_2108_ = lean_st_ref_get(v_a_2106_);
v___x_2109_ = lean_st_ref_get(v_a_2106_);
v_env_2110_ = lean_ctor_get(v___x_2108_, 0);
lean_inc_ref(v_env_2110_);
lean_dec(v___x_2108_);
v_env_2111_ = lean_ctor_get(v___x_2109_, 0);
lean_inc_ref_n(v_env_2111_, 2);
lean_dec(v___x_2109_);
v___x_2112_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_2102_);
v___x_2113_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2110_, v_declName_2102_, v___x_2112_);
v___x_2114_ = 1;
lean_inc(v___x_2113_);
v___x_2115_ = l_Lean_Environment_contains(v_env_2111_, v___x_2113_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v_toEnvExtension_2117_; lean_object* v_asyncMode_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; 
lean_dec(v___x_2113_);
v___x_2116_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
v_toEnvExtension_2117_ = lean_ctor_get(v___x_2116_, 0);
v_asyncMode_2118_ = lean_ctor_get(v_toEnvExtension_2117_, 2);
v___x_2119_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
v___x_2120_ = 0;
lean_inc(v_declName_2102_);
v___x_2121_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2119_, v___x_2116_, v_env_2111_, v_declName_2102_, v_asyncMode_2118_, v___x_2120_);
if (lean_obj_tag(v___x_2121_) == 1)
{
lean_object* v_val_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2146_; 
v_val_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2146_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_val_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2146_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_2102_, v_val_2122_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2137_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2137_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2137_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_a_2127_);
v___x_2132_ = v___x_2124_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2132_);
v___x_2134_ = v___x_2129_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_del_object(v___x_2124_);
v_a_2138_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2126_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2126_);
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
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec(v___x_2121_);
lean_dec(v_declName_2102_);
v___x_2147_ = lean_box(0);
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec_ref(v_env_2111_);
lean_dec(v_declName_2102_);
v___x_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2113_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
return v___x_2150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object* v_declName_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_));
v___x_2161_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object* v_a_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
return v_res_2163_;
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
