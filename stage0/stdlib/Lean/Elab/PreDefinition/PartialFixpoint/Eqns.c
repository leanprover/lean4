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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_Meta_smartUnfolding;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasExposedBody(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_addNoncomputable(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PartialFixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eqnInfoExt"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 126, 228, 214, 96, 108, 195, 201)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 154, 190, 235, 71, 53, 215, 0)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_eqnInfoExt;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(18, 104, 23, 57, 110, 104, 99, 16)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lfp_monotone"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(226, 115, 213, 20, 156, 86, 56, 31)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "mkFixEq: unexpected body of `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lfp_monotone_fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(178, 113, 187, 250, 69, 106, 19, 81)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fix_eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(83, 197, 58, 21, 58, 52, 66, 18)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not a definition"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__4 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__4_value;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isDefn\?"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__5 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__5_value;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_fix_eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_functional"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__5;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__6;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "rwFixUnder: unexpected expression "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateProj!Impl"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3;
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "_private.Lean.Elab.PreDefinition.PartialFixpoint.Eqns.0.Lean.Elab.PartialFixpoint.rwFixEqWith"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rwFixEqWith"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(21, 245, 144, 142, 29, 56, 3, 70)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no application of `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "` found"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "mkUnfoldEq rfl succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "mkUnfoldEq after rwFixEq:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "mkUnfoldEq after deltaLHS:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to generate unfold theorem for `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`:\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "partialFixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(21, 214, 78, 192, 157, 92, 193, 45)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6_value)} };
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__7_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "mkUnfoldEq start:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_9_ = lean_box(0);
v___x_10_ = l_Lean_Elab_instInhabitedFixedParamPerms_default;
v___x_11_ = ((lean_object*)(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3));
v___x_12_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2, &l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2_once, _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2);
v___x_13_ = lean_box(0);
v___x_14_ = lean_box(0);
v___x_15_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_12_);
lean_ctor_set(v___x_15_, 3, v___x_12_);
lean_ctor_set(v___x_15_, 4, v___x_11_);
lean_ctor_set(v___x_15_, 5, v___x_14_);
lean_ctor_set(v___x_15_, 6, v___x_10_);
lean_ctor_set(v___x_15_, 7, v___x_11_);
lean_ctor_set(v___x_15_, 8, v___x_9_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4, &l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4_once, _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
return v___x_17_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_(lean_object* v_env_18_, lean_object* v_n_19_, lean_object* v_x_20_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = l_Lean_Environment_hasExposedBody(v_env_18_, v_n_19_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object* v_env_22_, lean_object* v_n_23_, lean_object* v_x_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_(v_env_22_, v_n_23_, v_x_24_);
lean_dec_ref(v_x_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_27_, lean_object* v_x_28_){
_start:
{
if (lean_obj_tag(v_x_28_) == 0)
{
lean_object* v_k_29_; lean_object* v_v_30_; lean_object* v_l_31_; lean_object* v_r_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_k_29_ = lean_ctor_get(v_x_28_, 1);
v_v_30_ = lean_ctor_get(v_x_28_, 2);
v_l_31_ = lean_ctor_get(v_x_28_, 3);
v_r_32_ = lean_ctor_get(v_x_28_, 4);
v___x_33_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_27_, v_l_31_);
lean_inc(v_v_30_);
lean_inc(v_k_29_);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v_k_29_);
lean_ctor_set(v___x_34_, 1, v_v_30_);
v___x_35_ = lean_array_push(v___x_33_, v___x_34_);
v_init_27_ = v___x_35_;
v_x_28_ = v_r_32_;
goto _start;
}
else
{
return v_init_27_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_37_, v_x_38_);
lean_dec(v_x_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_(lean_object* v_env_42_, lean_object* v_s_43_){
_start:
{
lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v_all_46_; lean_object* v___x_47_; lean_object* v_exported_48_; lean_object* v___x_49_; 
v___f_44_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_44_, 0, v_env_42_);
v___x_45_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_));
v_all_46_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v___x_45_, v_s_43_);
v___x_47_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_44_, v_s_43_);
v_exported_48_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v___x_45_, v___x_47_);
lean_dec(v___x_47_);
lean_inc_ref(v_exported_48_);
v___x_49_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_49_, 0, v_exported_48_);
lean_ctor_set(v___x_49_, 1, v_exported_48_);
lean_ctor_set(v___x_49_, 2, v_all_46_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; lean_object* v___x_67_; 
v___f_63_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_));
v___x_64_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_));
v___x_65_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_));
v___x_66_ = 1;
v___x_67_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_64_, v___x_65_, v___x_66_, v___f_63_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0(lean_object* v_init_70_, lean_object* v_t_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_70_, v_t_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_73_, lean_object* v_t_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0(v_init_73_, v_t_74_);
lean_dec(v_t_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0(lean_object* v_k_76_, lean_object* v_b_77_, lean_object* v_c_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; 
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
v___x_84_ = lean_apply_7(v_k_76_, v_b_77_, v_c_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, lean_box(0));
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0___boxed(lean_object* v_k_85_, lean_object* v_b_86_, lean_object* v_c_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0(v_k_85_, v_b_86_, v_c_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(lean_object* v_e_94_, lean_object* v_k_95_, uint8_t v_cleanupAnnotations_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___f_102_; uint8_t v___x_103_; uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___f_102_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_102_, 0, v_k_95_);
v___x_103_ = 1;
v___x_104_ = 0;
v___x_105_ = lean_box(0);
v___x_106_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_94_, v___x_103_, v___x_104_, v___x_103_, v___x_104_, v___x_105_, v___f_102_, v_cleanupAnnotations_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
else
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
v_a_115_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_106_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_106_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___boxed(lean_object* v_e_123_, lean_object* v_k_124_, lean_object* v_cleanupAnnotations_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_131_; lean_object* v_res_132_; 
v_cleanupAnnotations_boxed_131_ = lean_unbox(v_cleanupAnnotations_125_);
v_res_132_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_e_123_, v_k_124_, v_cleanupAnnotations_boxed_131_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3(lean_object* v_00_u03b1_133_, lean_object* v_e_134_, lean_object* v_k_135_, uint8_t v_cleanupAnnotations_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_e_134_, v_k_135_, v_cleanupAnnotations_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___boxed(lean_object* v_00_u03b1_143_, lean_object* v_e_144_, lean_object* v_k_145_, lean_object* v_cleanupAnnotations_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_152_; lean_object* v_res_153_; 
v_cleanupAnnotations_boxed_152_ = lean_unbox(v_cleanupAnnotations_146_);
v_res_153_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3(v_00_u03b1_143_, v_e_144_, v_k_145_, v_cleanupAnnotations_boxed_152_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(lean_object* v_thm_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; lean_object* v_env_158_; lean_object* v_toConstantVal_159_; lean_object* v_value_160_; lean_object* v_all_161_; lean_object* v_type_168_; uint8_t v___x_169_; 
v___x_157_ = lean_st_ref_get(v___y_155_);
v_env_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc_ref_n(v_env_158_, 2);
lean_dec(v___x_157_);
v_toConstantVal_159_ = lean_ctor_get(v_thm_154_, 0);
v_value_160_ = lean_ctor_get(v_thm_154_, 1);
v_all_161_ = lean_ctor_get(v_thm_154_, 2);
v_type_168_ = lean_ctor_get(v_toConstantVal_159_, 2);
v___x_169_ = l_Lean_Environment_hasUnsafe(v_env_158_, v_type_168_);
if (v___x_169_ == 0)
{
uint8_t v___x_170_; 
v___x_170_ = l_Lean_Environment_hasUnsafe(v_env_158_, v_value_160_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_171_, 0, v_thm_154_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
else
{
lean_inc(v_all_161_);
lean_inc_ref(v_value_160_);
lean_inc_ref(v_toConstantVal_159_);
lean_dec_ref(v_thm_154_);
goto v___jp_162_;
}
}
else
{
lean_inc(v_all_161_);
lean_inc_ref(v_value_160_);
lean_inc_ref(v_toConstantVal_159_);
lean_dec_ref(v_env_158_);
lean_dec_ref(v_thm_154_);
goto v___jp_162_;
}
v___jp_162_:
{
lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_163_ = lean_box(0);
v___x_164_ = 0;
v___x_165_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_165_, 0, v_toConstantVal_159_);
lean_ctor_set(v___x_165_, 1, v_value_160_);
lean_ctor_set(v___x_165_, 2, v___x_163_);
lean_ctor_set(v___x_165_, 3, v_all_161_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*4, v___x_164_);
v___x_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___boxed(lean_object* v_thm_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v_thm_173_, v___y_174_);
lean_dec(v___y_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5(lean_object* v_thm_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v_thm_177_, v___y_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___boxed(lean_object* v_thm_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5(v_thm_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(lean_object* v_msgData_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; lean_object* v_env_198_; uint8_t v___x_199_; lean_object* v_env_200_; lean_object* v___x_201_; lean_object* v_toCold_202_; lean_object* v_mctx_203_; lean_object* v_lctx_204_; lean_object* v_options_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_197_ = lean_st_ref_get(v___y_195_);
v_env_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc_ref(v_env_198_);
lean_dec(v___x_197_);
v___x_199_ = 0;
v_env_200_ = l_Lean_Environment_setRecordingDeps(v_env_198_, v___x_199_);
v___x_201_ = lean_st_ref_get(v___y_193_);
v_toCold_202_ = lean_ctor_get(v___y_194_, 0);
v_mctx_203_ = lean_ctor_get(v___x_201_, 0);
lean_inc_ref(v_mctx_203_);
lean_dec(v___x_201_);
v_lctx_204_ = lean_ctor_get(v___y_192_, 2);
v_options_205_ = lean_ctor_get(v_toCold_202_, 2);
lean_inc_ref(v_options_205_);
lean_inc_ref(v_lctx_204_);
v___x_206_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_206_, 0, v_env_200_);
lean_ctor_set(v___x_206_, 1, v_mctx_203_);
lean_ctor_set(v___x_206_, 2, v_lctx_204_);
lean_ctor_set(v___x_206_, 3, v_options_205_);
v___x_207_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v_msgData_191_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0___boxed(lean_object* v_msgData_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msgData_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(lean_object* v_msg_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_ref_222_; lean_object* v___x_223_; lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_232_; 
v_ref_222_ = lean_ctor_get(v___y_219_, 2);
v___x_223_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msg_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
v_a_224_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_232_ == 0)
{
v___x_226_ = v___x_223_;
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
lean_inc(v_ref_222_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v_ref_222_);
lean_ctor_set(v___x_228_, 1, v_a_224_);
if (v_isShared_227_ == 0)
{
lean_ctor_set_tag(v___x_226_, 1);
lean_ctor_set(v___x_226_, 0, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg___boxed(lean_object* v_msg_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v_msg_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
return v_res_239_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__5));
v___x_253_ = l_Lean_stringToMessageData(v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__7));
v___x_256_ = l_Lean_stringToMessageData(v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0(lean_object* v_declNameNonRec_257_, lean_object* v_xs_258_, lean_object* v_body_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_309_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2));
v___x_310_ = lean_unsigned_to_nat(4u);
v___x_311_ = l_Lean_Expr_isAppOfArity(v_body_259_, v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4));
v___x_313_ = l_Lean_Expr_isAppOfArity(v_body_259_, v___x_312_, v___x_310_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v___x_314_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6);
v___x_315_ = l_Lean_MessageData_ofConstName(v_declNameNonRec_257_, v___x_313_);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = l_Lean_indentExpr(v_body_259_);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_320_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
v_a_322_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_321_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
lean_dec(v_declNameNonRec_257_);
goto v___jp_265_;
}
}
else
{
lean_dec(v_declNameNonRec_257_);
goto v___jp_265_;
}
v___jp_265_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = l_Lean_Expr_appFn_x21(v_body_259_);
lean_dec_ref(v_body_259_);
v___x_267_ = l_Lean_Expr_appArg_x21(v___x_266_);
lean_dec_ref(v___x_266_);
lean_inc(v___y_263_);
lean_inc_ref(v___y_262_);
lean_inc(v___y_261_);
lean_inc_ref(v___y_260_);
lean_inc_ref(v___x_267_);
v___x_268_ = lean_infer_type(v___x_267_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; uint8_t v___x_270_; uint8_t v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v___x_268_, 1);
v___x_270_ = 0;
v___x_271_ = 1;
v___x_272_ = 1;
v___x_273_ = l_Lean_Meta_mkForallFVars(v_xs_258_, v_a_269_, v___x_270_, v___x_271_, v___x_271_, v___x_272_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
v___x_275_ = l_Lean_Meta_mkLambdaFVars(v_xs_258_, v___x_267_, v___x_270_, v___x_271_, v___x_270_, v___x_271_, v___x_272_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_284_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_284_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_a_274_);
lean_ctor_set(v___x_280_, 1, v_a_276_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec(v_a_274_);
v_a_285_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_275_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_275_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec_ref(v___x_267_);
v_a_293_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_273_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_273_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec_ref(v___x_267_);
v_a_301_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_268_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_268_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___boxed(lean_object* v_declNameNonRec_330_, lean_object* v_xs_331_, lean_object* v_body_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0(v_declNameNonRec_330_, v_xs_331_, v_body_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec_ref(v_xs_331_);
return v_res_338_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0(void){
_start:
{
lean_object* v___x_339_; lean_object* v_dummy_340_; 
v___x_339_ = lean_box(0);
v_dummy_340_ = l_Lean_Expr_sort___override(v___x_339_);
return v_dummy_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1(lean_object* v_declNameNonRec_351_, lean_object* v___x_352_, lean_object* v___x_353_, uint8_t v___x_354_, lean_object* v_xs_355_, lean_object* v_body_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; uint8_t v___x_369_; lean_object* v___y_371_; 
lean_inc(v___x_352_);
v___x_362_ = l_Lean_mkConst(v_declNameNonRec_351_, v___x_352_);
v___x_363_ = l_Lean_mkAppN(v___x_362_, v_xs_355_);
v___x_364_ = l_Lean_mkConst(v___x_353_, v___x_352_);
v___x_365_ = l_Lean_mkAppN(v___x_364_, v_xs_355_);
lean_inc_ref(v___x_363_);
v___x_366_ = l_Lean_Expr_app___override(v___x_365_, v___x_363_);
v___x_367_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2));
v___x_368_ = l_Lean_Expr_isAppOf(v_body_356_, v___x_367_);
v___x_369_ = 1;
if (v___x_368_ == 0)
{
lean_object* v___x_421_; 
v___x_421_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2));
v___y_371_ = v___x_421_;
goto v___jp_370_;
}
else
{
lean_object* v___x_422_; 
v___x_422_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4));
v___y_371_ = v___x_422_;
goto v___jp_370_;
}
v___jp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v_dummy_375_; lean_object* v_nargs_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_372_ = l_Lean_Expr_getAppFn(v_body_356_);
v___x_373_ = l_Lean_Expr_constLevels_x21(v___x_372_);
lean_dec_ref(v___x_372_);
lean_inc(v___y_371_);
v___x_374_ = l_Lean_mkConst(v___y_371_, v___x_373_);
v_dummy_375_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_376_ = l_Lean_Expr_getAppNumArgs(v_body_356_);
lean_inc(v_nargs_376_);
v___x_377_ = lean_mk_array(v_nargs_376_, v_dummy_375_);
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = lean_nat_sub(v_nargs_376_, v___x_378_);
lean_dec(v_nargs_376_);
v___x_380_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_body_356_, v___x_377_, v___x_379_);
v___x_381_ = l_Lean_mkAppN(v___x_374_, v___x_380_);
lean_dec_ref(v___x_380_);
v___x_382_ = l_Lean_Meta_mkEq(v___x_363_, v___x_366_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; uint8_t v___x_384_; lean_object* v___x_385_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
v___x_384_ = 1;
v___x_385_ = l_Lean_Meta_mkForallFVars(v_xs_355_, v_a_383_, v___x_354_, v___x_369_, v___x_369_, v___x_384_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = l_Lean_Meta_mkLambdaFVars(v_xs_355_, v___x_381_, v___x_354_, v___x_369_, v___x_354_, v___x_369_, v___x_384_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_396_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_a_386_);
lean_ctor_set(v___x_392_, 1, v_a_388_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_a_386_);
v_a_397_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_387_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_387_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v___x_381_);
v_a_405_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_385_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_385_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref(v___x_381_);
v_a_413_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_382_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_382_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___boxed(lean_object* v_declNameNonRec_423_, lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v___x_426_, lean_object* v_xs_427_, lean_object* v_body_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
uint8_t v___x_10607__boxed_434_; lean_object* v_res_435_; 
v___x_10607__boxed_434_ = lean_unbox(v___x_426_);
v_res_435_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1(v_declNameNonRec_423_, v___x_424_, v___x_425_, v___x_10607__boxed_434_, v_xs_427_, v_body_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec_ref(v_xs_427_);
return v_res_435_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_436_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__0);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg(){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__1);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___boxed(lean_object* v___dummy_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg();
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
if (lean_obj_tag(v_a_443_) == 0)
{
lean_object* v___x_445_; 
v___x_445_ = l_List_reverse___redArg(v_a_444_);
return v___x_445_;
}
else
{
lean_object* v_head_446_; lean_object* v_tail_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_456_; 
v_head_446_ = lean_ctor_get(v_a_443_, 0);
v_tail_447_ = lean_ctor_get(v_a_443_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_456_ == 0)
{
v___x_449_ = v_a_443_;
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_tail_447_);
lean_inc(v_head_446_);
lean_dec(v_a_443_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = l_Lean_mkLevelParam(v_head_446_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_a_444_);
lean_ctor_set(v___x_449_, 0, v___x_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_a_444_);
v___x_453_ = v_reuseFailAlloc_455_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
v_a_443_ = v_tail_447_;
v_a_444_ = v___x_453_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_instMonadEIO___redArg();
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(lean_object* v_msg_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_toApplicative_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_531_; 
v___x_468_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0, &l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0);
v___x_469_ = l_StateRefT_x27_instMonad___redArg(v___x_468_);
v_toApplicative_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v___x_469_, 1);
lean_dec(v_unused_532_);
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_531_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_toApplicative_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_531_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_toFunctor_474_; lean_object* v_toSeq_475_; lean_object* v_toSeqLeft_476_; lean_object* v_toSeqRight_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_529_; 
v_toFunctor_474_ = lean_ctor_get(v_toApplicative_470_, 0);
v_toSeq_475_ = lean_ctor_get(v_toApplicative_470_, 2);
v_toSeqLeft_476_ = lean_ctor_get(v_toApplicative_470_, 3);
v_toSeqRight_477_ = lean_ctor_get(v_toApplicative_470_, 4);
v_isSharedCheck_529_ = !lean_is_exclusive(v_toApplicative_470_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v_toApplicative_470_, 1);
lean_dec(v_unused_530_);
v___x_479_ = v_toApplicative_470_;
v_isShared_480_ = v_isSharedCheck_529_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_toSeqRight_477_);
lean_inc(v_toSeqLeft_476_);
lean_inc(v_toSeq_475_);
lean_inc(v_toFunctor_474_);
lean_dec(v_toApplicative_470_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_529_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___f_481_; lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___f_486_; lean_object* v___f_487_; lean_object* v___f_488_; lean_object* v___x_490_; 
v___f_481_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__1));
v___f_482_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__2));
lean_inc_ref(v_toFunctor_474_);
v___f_483_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_483_, 0, v_toFunctor_474_);
v___f_484_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_484_, 0, v_toFunctor_474_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___f_483_);
lean_ctor_set(v___x_485_, 1, v___f_484_);
v___f_486_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_486_, 0, v_toSeqRight_477_);
v___f_487_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_487_, 0, v_toSeqLeft_476_);
v___f_488_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_488_, 0, v_toSeq_475_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v___f_486_);
lean_ctor_set(v___x_479_, 3, v___f_487_);
lean_ctor_set(v___x_479_, 2, v___f_488_);
lean_ctor_set(v___x_479_, 1, v___f_481_);
lean_ctor_set(v___x_479_, 0, v___x_485_);
v___x_490_ = v___x_479_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___f_481_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v___f_488_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v___f_487_);
lean_ctor_set(v_reuseFailAlloc_528_, 4, v___f_486_);
v___x_490_ = v_reuseFailAlloc_528_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v___f_482_);
lean_ctor_set(v___x_472_, 0, v___x_490_);
v___x_492_ = v___x_472_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v___f_482_);
v___x_492_ = v_reuseFailAlloc_527_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v_toApplicative_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_525_; 
v___x_493_ = l_StateRefT_x27_instMonad___redArg(v___x_492_);
v_toApplicative_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; 
v_unused_526_ = lean_ctor_get(v___x_493_, 1);
lean_dec(v_unused_526_);
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_525_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_toApplicative_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_525_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_toFunctor_498_; lean_object* v_toSeq_499_; lean_object* v_toSeqLeft_500_; lean_object* v_toSeqRight_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_523_; 
v_toFunctor_498_ = lean_ctor_get(v_toApplicative_494_, 0);
v_toSeq_499_ = lean_ctor_get(v_toApplicative_494_, 2);
v_toSeqLeft_500_ = lean_ctor_get(v_toApplicative_494_, 3);
v_toSeqRight_501_ = lean_ctor_get(v_toApplicative_494_, 4);
v_isSharedCheck_523_ = !lean_is_exclusive(v_toApplicative_494_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v_toApplicative_494_, 1);
lean_dec(v_unused_524_);
v___x_503_ = v_toApplicative_494_;
v_isShared_504_ = v_isSharedCheck_523_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_toSeqRight_501_);
lean_inc(v_toSeqLeft_500_);
lean_inc(v_toSeq_499_);
lean_inc(v_toFunctor_498_);
lean_dec(v_toApplicative_494_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_523_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___f_505_; lean_object* v___f_506_; lean_object* v___f_507_; lean_object* v___f_508_; lean_object* v___x_509_; lean_object* v___f_510_; lean_object* v___f_511_; lean_object* v___f_512_; lean_object* v___x_514_; 
v___f_505_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__3));
v___f_506_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__4));
lean_inc_ref(v_toFunctor_498_);
v___f_507_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_507_, 0, v_toFunctor_498_);
v___f_508_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_508_, 0, v_toFunctor_498_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___f_507_);
lean_ctor_set(v___x_509_, 1, v___f_508_);
v___f_510_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_510_, 0, v_toSeqRight_501_);
v___f_511_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_511_, 0, v_toSeqLeft_500_);
v___f_512_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_512_, 0, v_toSeq_499_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v___f_510_);
lean_ctor_set(v___x_503_, 3, v___f_511_);
lean_ctor_set(v___x_503_, 2, v___f_512_);
lean_ctor_set(v___x_503_, 1, v___f_505_);
lean_ctor_set(v___x_503_, 0, v___x_509_);
v___x_514_ = v___x_503_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___f_505_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v___f_512_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v___f_511_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v___f_510_);
v___x_514_ = v_reuseFailAlloc_522_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_516_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___f_506_);
lean_ctor_set(v___x_496_, 0, v___x_514_);
v___x_516_ = v___x_496_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___f_506_);
v___x_516_ = v_reuseFailAlloc_521_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_9795__overap_519_; lean_object* v___x_520_; 
v___x_517_ = lean_box(0);
v___x_518_ = l_instInhabitedOfMonad___redArg(v___x_516_, v___x_517_);
v___x_9795__overap_519_ = lean_panic_fn_borrowed(v___x_518_, v_msg_462_);
lean_dec(v___x_518_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
v___x_520_ = lean_apply_5(v___x_9795__overap_519_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, lean_box(0));
return v___x_520_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___boxed(lean_object* v_msg_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(v_msg_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_539_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__0));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__2));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_549_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_550_ = lean_unsigned_to_nat(11u);
v___x_551_ = lean_unsigned_to_nat(115u);
v___x_552_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__5));
v___x_553_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__4));
v___x_554_ = l_mkPanicMessageWithDecl(v___x_553_, v___x_552_, v___x_551_, v___x_550_, v___x_549_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(lean_object* v_constName_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_569_; lean_object* v_env_570_; uint8_t v___x_571_; lean_object* v___x_572_; 
v___x_569_ = lean_st_ref_get(v___y_559_);
v_env_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_env_570_);
lean_dec(v___x_569_);
v___x_571_ = 0;
lean_inc(v_constName_555_);
v___x_572_ = l_Lean_Environment_findAsync_x3f(v_env_570_, v_constName_555_, v___x_571_);
if (lean_obj_tag(v___x_572_) == 1)
{
lean_object* v_val_573_; uint8_t v_kind_574_; 
v_val_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v___x_572_, 1);
v_kind_574_ = lean_ctor_get_uint8(v_val_573_, sizeof(void*)*3);
if (v_kind_574_ == 0)
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_573_);
if (lean_obj_tag(v___x_575_) == 1)
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec(v_constName_555_);
v_val_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 0);
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_val_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec_ref(v___x_575_);
v___x_584_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7);
v___x_585_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(v___x_584_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_594_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
if (lean_obj_tag(v_a_586_) == 0)
{
lean_del_object(v___x_588_);
goto v___jp_561_;
}
else
{
lean_object* v_val_590_; lean_object* v___x_592_; 
lean_dec(v_constName_555_);
v_val_590_ = lean_ctor_get(v_a_586_, 0);
lean_inc(v_val_590_);
lean_dec_ref_known(v_a_586_, 1);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v_val_590_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_val_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec(v_constName_555_);
v_a_595_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_585_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_585_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
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
lean_dec(v_val_573_);
goto v___jp_561_;
}
}
else
{
lean_dec(v___x_572_);
goto v___jp_561_;
}
v___jp_561_:
{
lean_object* v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_562_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1);
v___x_563_ = 0;
v___x_564_ = l_Lean_MessageData_ofConstName(v_constName_555_, v___x_563_);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_562_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3);
v___x_567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_567_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___boxed(lean_object* v_constName_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(v_constName_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_609_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg___closed__0);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6___redArg();
return v___x_616_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__5(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__6(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2);
v___x_621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
lean_ctor_set(v___x_621_, 2, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_622_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__6);
v___x_623_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__5);
v___x_624_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__2);
v___x_625_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4);
v___x_626_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
lean_ctor_set(v___x_626_, 2, v___x_623_);
lean_ctor_set(v___x_626_, 3, v___x_624_);
lean_ctor_set(v___x_626_, 4, v___x_624_);
lean_ctor_set(v___x_626_, 5, v___x_624_);
lean_ctor_set(v___x_626_, 6, v___x_624_);
lean_ctor_set(v___x_626_, 7, v___x_622_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2(lean_object* v_declNameNonRec_627_, lean_object* v___f_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_634_; lean_object* v_env_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_env_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_634_ = lean_st_ref_get(v___y_632_);
v_env_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc_ref(v_env_635_);
lean_dec(v___x_634_);
v___x_636_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__0));
lean_inc_n(v_declNameNonRec_627_, 3);
v___x_637_ = l_Lean_Meta_mkEqLikeNameFor(v_env_635_, v_declNameNonRec_627_, v___x_636_);
v___x_638_ = lean_st_ref_get(v___y_632_);
v_env_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc_ref(v_env_639_);
lean_dec(v___x_638_);
v___x_640_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__1));
v___x_641_ = l_Lean_Meta_mkEqLikeNameFor(v_env_639_, v_declNameNonRec_627_, v___x_640_);
v___x_642_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(v_declNameNonRec_627_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v_toConstantVal_644_; lean_object* v_value_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_774_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v_toConstantVal_644_ = lean_ctor_get(v_a_643_, 0);
v_value_645_ = lean_ctor_get(v_a_643_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_a_643_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; lean_object* v_unused_776_; 
v_unused_775_ = lean_ctor_get(v_a_643_, 3);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_a_643_, 2);
lean_dec(v_unused_776_);
v___x_647_ = v_a_643_;
v_isShared_648_ = v_isSharedCheck_774_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_value_645_);
lean_inc(v_toConstantVal_644_);
lean_dec(v_a_643_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_774_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v_levelParams_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_771_; 
v_levelParams_649_ = lean_ctor_get(v_toConstantVal_644_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_toConstantVal_644_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; lean_object* v_unused_773_; 
v_unused_772_ = lean_ctor_get(v_toConstantVal_644_, 2);
lean_dec(v_unused_772_);
v_unused_773_ = lean_ctor_get(v_toConstantVal_644_, 0);
lean_dec(v_unused_773_);
v___x_651_ = v_toConstantVal_644_;
v_isShared_652_ = v_isSharedCheck_771_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_levelParams_649_);
lean_dec(v_toConstantVal_644_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_771_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___f_657_; lean_object* v___x_658_; 
v___x_653_ = lean_box(0);
lean_inc(v_levelParams_649_);
v___x_654_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(v_levelParams_649_, v___x_653_);
v___x_655_ = 0;
v___x_656_ = lean_box(v___x_655_);
lean_inc(v___x_641_);
v___f_657_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___boxed), 11, 4);
lean_closure_set(v___f_657_, 0, v_declNameNonRec_627_);
lean_closure_set(v___f_657_, 1, v___x_654_);
lean_closure_set(v___f_657_, 2, v___x_641_);
lean_closure_set(v___f_657_, 3, v___x_656_);
lean_inc_ref(v_value_645_);
v___x_658_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_645_, v___f_628_, v___x_655_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v_fst_660_; lean_object* v_snd_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_762_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v_fst_660_ = lean_ctor_get(v_a_659_, 0);
v_snd_661_ = lean_ctor_get(v_a_659_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v_a_659_);
if (v_isSharedCheck_762_ == 0)
{
v___x_663_ = v_a_659_;
v_isShared_664_ = v_isSharedCheck_762_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_snd_661_);
lean_inc(v_fst_660_);
lean_dec(v_a_659_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_762_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
lean_inc(v_levelParams_649_);
lean_inc(v___x_641_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 2, v_fst_660_);
lean_ctor_set(v___x_651_, 0, v___x_641_);
v___x_666_ = v___x_651_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_levelParams_649_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_fst_660_);
v___x_666_ = v_reuseFailAlloc_761_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_670_; 
v___x_667_ = lean_box(1);
v___x_668_ = 1;
lean_inc(v___x_641_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 1);
lean_ctor_set(v___x_663_, 1, v___x_653_);
lean_ctor_set(v___x_663_, 0, v___x_641_);
v___x_670_ = v___x_663_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_653_);
v___x_670_ = v_reuseFailAlloc_760_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_672_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 3, v___x_670_);
lean_ctor_set(v___x_647_, 2, v___x_667_);
lean_ctor_set(v___x_647_, 1, v_snd_661_);
lean_ctor_set(v___x_647_, 0, v___x_666_);
v___x_672_ = v___x_647_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_snd_661_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v___x_670_);
v___x_672_ = v_reuseFailAlloc_759_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*4, v___x_668_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
v___x_674_ = l_Lean_addDecl(v___x_673_, v___x_655_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_675_; lean_object* v_env_676_; lean_object* v_nextMacroScope_677_; lean_object* v_ngen_678_; lean_object* v_auxDeclNGen_679_; lean_object* v_traceState_680_; lean_object* v_recordedDeps_681_; lean_object* v_messages_682_; lean_object* v_infoState_683_; lean_object* v_snapshotTasks_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref_known(v___x_674_, 1);
v___x_675_ = lean_st_ref_take(v___y_632_);
v_env_676_ = lean_ctor_get(v___x_675_, 0);
v_nextMacroScope_677_ = lean_ctor_get(v___x_675_, 1);
v_ngen_678_ = lean_ctor_get(v___x_675_, 2);
v_auxDeclNGen_679_ = lean_ctor_get(v___x_675_, 3);
v_traceState_680_ = lean_ctor_get(v___x_675_, 4);
v_recordedDeps_681_ = lean_ctor_get(v___x_675_, 6);
v_messages_682_ = lean_ctor_get(v___x_675_, 7);
v_infoState_683_ = lean_ctor_get(v___x_675_, 8);
v_snapshotTasks_684_ = lean_ctor_get(v___x_675_, 9);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v___x_675_, 5);
lean_dec(v_unused_750_);
v___x_686_ = v___x_675_;
v_isShared_687_ = v_isSharedCheck_749_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_snapshotTasks_684_);
lean_inc(v_infoState_683_);
lean_inc(v_messages_682_);
lean_inc(v_recordedDeps_681_);
lean_inc(v_traceState_680_);
lean_inc(v_auxDeclNGen_679_);
lean_inc(v_ngen_678_);
lean_inc(v_nextMacroScope_677_);
lean_inc(v_env_676_);
lean_dec(v___x_675_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_749_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_688_ = l_Lean_addNoncomputable(v_env_676_, v___x_641_);
v___x_689_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 5, v___x_689_);
lean_ctor_set(v___x_686_, 0, v___x_688_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_nextMacroScope_677_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_ngen_678_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_auxDeclNGen_679_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_traceState_680_);
lean_ctor_set(v_reuseFailAlloc_748_, 5, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_748_, 6, v_recordedDeps_681_);
lean_ctor_set(v_reuseFailAlloc_748_, 7, v_messages_682_);
lean_ctor_set(v_reuseFailAlloc_748_, 8, v_infoState_683_);
lean_ctor_set(v_reuseFailAlloc_748_, 9, v_snapshotTasks_684_);
v___x_691_ = v_reuseFailAlloc_748_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_mctx_694_; lean_object* v_zetaDeltaFVarIds_695_; lean_object* v_postponed_696_; lean_object* v_diag_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_746_; 
v___x_692_ = lean_st_ref_put(v___y_632_, v___x_691_);
v___x_693_ = lean_st_ref_take(v___y_630_);
v_mctx_694_ = lean_ctor_get(v___x_693_, 0);
v_zetaDeltaFVarIds_695_ = lean_ctor_get(v___x_693_, 2);
v_postponed_696_ = lean_ctor_get(v___x_693_, 3);
v_diag_697_ = lean_ctor_get(v___x_693_, 4);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v___x_693_, 1);
lean_dec(v_unused_747_);
v___x_699_ = v___x_693_;
v_isShared_700_ = v_isSharedCheck_746_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_diag_697_);
lean_inc(v_postponed_696_);
lean_inc(v_zetaDeltaFVarIds_695_);
lean_inc(v_mctx_694_);
lean_dec(v___x_693_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_746_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_mctx_694_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_zetaDeltaFVarIds_695_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_postponed_696_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_diag_697_);
v___x_703_ = v_reuseFailAlloc_745_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_st_ref_put(v___y_630_, v___x_703_);
v___x_705_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_645_, v___f_657_, v___x_655_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v_fst_707_; lean_object* v_snd_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_736_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v_fst_707_ = lean_ctor_get(v_a_706_, 0);
v_snd_708_ = lean_ctor_get(v_a_706_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v_a_706_);
if (v_isSharedCheck_736_ == 0)
{
v___x_710_ = v_a_706_;
v_isShared_711_ = v_isSharedCheck_736_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_snd_708_);
lean_inc(v_fst_707_);
lean_dec(v_a_706_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_736_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_inc_n(v___x_637_, 2);
v___x_712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_712_, 0, v___x_637_);
lean_ctor_set(v___x_712_, 1, v_levelParams_649_);
lean_ctor_set(v___x_712_, 2, v_fst_707_);
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 1);
lean_ctor_set(v___x_710_, 1, v___x_653_);
lean_ctor_set(v___x_710_, 0, v___x_637_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_653_);
v___x_714_ = v_reuseFailAlloc_735_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_a_717_; lean_object* v___x_718_; 
v___x_715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_715_, 0, v___x_712_);
lean_ctor_set(v___x_715_, 1, v_snd_708_);
lean_ctor_set(v___x_715_, 2, v___x_714_);
v___x_716_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v___x_715_, v___y_632_);
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref(v___x_716_);
v___x_718_ = l_Lean_addDecl(v_a_717_, v___x_655_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v___x_718_, 0);
lean_dec(v_unused_726_);
v___x_720_ = v___x_718_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_dec(v___x_718_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_637_);
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_637_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v___x_637_);
v_a_727_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_718_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_718_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_levelParams_649_);
lean_dec(v___x_637_);
v_a_737_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_705_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_705_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
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
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v___f_657_);
lean_dec(v_levelParams_649_);
lean_dec_ref(v_value_645_);
lean_dec(v___x_641_);
lean_dec(v___x_637_);
v_a_751_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_674_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_674_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
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
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec_ref(v___f_657_);
lean_del_object(v___x_651_);
lean_dec(v_levelParams_649_);
lean_del_object(v___x_647_);
lean_dec_ref(v_value_645_);
lean_dec(v___x_641_);
lean_dec(v___x_637_);
v_a_763_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_658_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_658_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec(v___x_641_);
lean_dec(v___x_637_);
lean_dec_ref(v___f_628_);
lean_dec(v_declNameNonRec_627_);
v_a_777_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_642_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_642_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___boxed(lean_object* v_declNameNonRec_785_, lean_object* v___f_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2(v_declNameNonRec_785_, v___f_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg___lam__0(lean_object* v___y_793_, uint8_t v_isExporting_794_, lean_object* v___x_795_, lean_object* v___y_796_, lean_object* v___x_797_, lean_object* v_a_x3f_798_){
_start:
{
lean_object* v___x_800_; lean_object* v_env_801_; lean_object* v_nextMacroScope_802_; lean_object* v_ngen_803_; lean_object* v_auxDeclNGen_804_; lean_object* v_traceState_805_; lean_object* v_recordedDeps_806_; lean_object* v_messages_807_; lean_object* v_infoState_808_; lean_object* v_snapshotTasks_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_834_; 
v___x_800_ = lean_st_ref_take(v___y_793_);
v_env_801_ = lean_ctor_get(v___x_800_, 0);
v_nextMacroScope_802_ = lean_ctor_get(v___x_800_, 1);
v_ngen_803_ = lean_ctor_get(v___x_800_, 2);
v_auxDeclNGen_804_ = lean_ctor_get(v___x_800_, 3);
v_traceState_805_ = lean_ctor_get(v___x_800_, 4);
v_recordedDeps_806_ = lean_ctor_get(v___x_800_, 6);
v_messages_807_ = lean_ctor_get(v___x_800_, 7);
v_infoState_808_ = lean_ctor_get(v___x_800_, 8);
v_snapshotTasks_809_ = lean_ctor_get(v___x_800_, 9);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v___x_800_, 5);
lean_dec(v_unused_835_);
v___x_811_ = v___x_800_;
v_isShared_812_ = v_isSharedCheck_834_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_snapshotTasks_809_);
lean_inc(v_infoState_808_);
lean_inc(v_messages_807_);
lean_inc(v_recordedDeps_806_);
lean_inc(v_traceState_805_);
lean_inc(v_auxDeclNGen_804_);
lean_inc(v_ngen_803_);
lean_inc(v_nextMacroScope_802_);
lean_inc(v_env_801_);
lean_dec(v___x_800_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_834_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = l_Lean_Environment_setExporting(v_env_801_, v_isExporting_794_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 5, v___x_795_);
lean_ctor_set(v___x_811_, 0, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_nextMacroScope_802_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_ngen_803_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v_auxDeclNGen_804_);
lean_ctor_set(v_reuseFailAlloc_833_, 4, v_traceState_805_);
lean_ctor_set(v_reuseFailAlloc_833_, 5, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_833_, 6, v_recordedDeps_806_);
lean_ctor_set(v_reuseFailAlloc_833_, 7, v_messages_807_);
lean_ctor_set(v_reuseFailAlloc_833_, 8, v_infoState_808_);
lean_ctor_set(v_reuseFailAlloc_833_, 9, v_snapshotTasks_809_);
v___x_815_ = v_reuseFailAlloc_833_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_mctx_818_; lean_object* v_zetaDeltaFVarIds_819_; lean_object* v_postponed_820_; lean_object* v_diag_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_831_; 
v___x_816_ = lean_st_ref_put(v___y_793_, v___x_815_);
v___x_817_ = lean_st_ref_take(v___y_796_);
v_mctx_818_ = lean_ctor_get(v___x_817_, 0);
v_zetaDeltaFVarIds_819_ = lean_ctor_get(v___x_817_, 2);
v_postponed_820_ = lean_ctor_get(v___x_817_, 3);
v_diag_821_ = lean_ctor_get(v___x_817_, 4);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v___x_817_, 1);
lean_dec(v_unused_832_);
v___x_823_ = v___x_817_;
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_diag_821_);
lean_inc(v_postponed_820_);
lean_inc(v_zetaDeltaFVarIds_819_);
lean_inc(v_mctx_818_);
lean_dec(v___x_817_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_box(0);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v___x_797_);
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_mctx_818_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_zetaDeltaFVarIds_819_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v_postponed_820_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v_diag_821_);
v___x_827_ = v_reuseFailAlloc_830_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_st_ref_put(v___y_796_, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_825_);
return v___x_829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg___lam__0___boxed(lean_object* v___y_836_, lean_object* v_isExporting_837_, lean_object* v___x_838_, lean_object* v___y_839_, lean_object* v___x_840_, lean_object* v_a_x3f_841_, lean_object* v___y_842_){
_start:
{
uint8_t v_isExporting_boxed_843_; lean_object* v_res_844_; 
v_isExporting_boxed_843_ = lean_unbox(v_isExporting_837_);
v_res_844_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg___lam__0(v___y_836_, v_isExporting_boxed_843_, v___x_838_, v___y_839_, v___x_840_, v_a_x3f_841_);
lean_dec(v_a_x3f_841_);
lean_dec(v___y_839_);
lean_dec(v___y_836_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg(lean_object* v_x_845_, uint8_t v_isExporting_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_852_; lean_object* v_env_853_; lean_object* v___x_854_; uint8_t v_isModule_855_; 
v___x_852_ = lean_st_ref_get(v___y_850_);
v_env_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc_ref(v_env_853_);
lean_dec(v___x_852_);
v___x_854_ = l_Lean_Environment_header(v_env_853_);
v_isModule_855_ = lean_ctor_get_uint8(v___x_854_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_854_);
if (v_isModule_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec_ref(v_env_853_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v___y_848_);
lean_inc_ref(v___y_847_);
v___x_856_ = lean_apply_5(v_x_845_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, lean_box(0));
return v___x_856_;
}
else
{
uint8_t v_isExporting_857_; 
v_isExporting_857_ = lean_ctor_get_uint8(v_env_853_, sizeof(void*)*13);
lean_dec_ref(v_env_853_);
if (v_isExporting_846_ == 0)
{
if (v_isExporting_857_ == 0)
{
lean_object* v___x_924_; 
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v___y_848_);
lean_inc_ref(v___y_847_);
v___x_924_ = lean_apply_5(v_x_845_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, lean_box(0));
return v___x_924_;
}
else
{
goto v___jp_858_;
}
}
else
{
if (v_isExporting_857_ == 0)
{
goto v___jp_858_;
}
else
{
lean_object* v___x_925_; 
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v___y_848_);
lean_inc_ref(v___y_847_);
v___x_925_ = lean_apply_5(v_x_845_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, lean_box(0));
return v___x_925_;
}
}
v___jp_858_:
{
lean_object* v___x_859_; lean_object* v_env_860_; lean_object* v_nextMacroScope_861_; lean_object* v_ngen_862_; lean_object* v_auxDeclNGen_863_; lean_object* v_traceState_864_; lean_object* v_recordedDeps_865_; lean_object* v_messages_866_; lean_object* v_infoState_867_; lean_object* v_snapshotTasks_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_922_; 
v___x_859_ = lean_st_ref_take(v___y_850_);
v_env_860_ = lean_ctor_get(v___x_859_, 0);
v_nextMacroScope_861_ = lean_ctor_get(v___x_859_, 1);
v_ngen_862_ = lean_ctor_get(v___x_859_, 2);
v_auxDeclNGen_863_ = lean_ctor_get(v___x_859_, 3);
v_traceState_864_ = lean_ctor_get(v___x_859_, 4);
v_recordedDeps_865_ = lean_ctor_get(v___x_859_, 6);
v_messages_866_ = lean_ctor_get(v___x_859_, 7);
v_infoState_867_ = lean_ctor_get(v___x_859_, 8);
v_snapshotTasks_868_ = lean_ctor_get(v___x_859_, 9);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v___x_859_, 5);
lean_dec(v_unused_923_);
v___x_870_ = v___x_859_;
v_isShared_871_ = v_isSharedCheck_922_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_snapshotTasks_868_);
lean_inc(v_infoState_867_);
lean_inc(v_messages_866_);
lean_inc(v_recordedDeps_865_);
lean_inc(v_traceState_864_);
lean_inc(v_auxDeclNGen_863_);
lean_inc(v_ngen_862_);
lean_inc(v_nextMacroScope_861_);
lean_inc(v_env_860_);
lean_dec(v___x_859_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_922_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_872_ = l_Lean_Environment_setExporting(v_env_860_, v_isExporting_846_);
v___x_873_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 5, v___x_873_);
lean_ctor_set(v___x_870_, 0, v___x_872_);
v___x_875_ = v___x_870_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_nextMacroScope_861_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_ngen_862_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_auxDeclNGen_863_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_traceState_864_);
lean_ctor_set(v_reuseFailAlloc_921_, 5, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_921_, 6, v_recordedDeps_865_);
lean_ctor_set(v_reuseFailAlloc_921_, 7, v_messages_866_);
lean_ctor_set(v_reuseFailAlloc_921_, 8, v_infoState_867_);
lean_ctor_set(v_reuseFailAlloc_921_, 9, v_snapshotTasks_868_);
v___x_875_ = v_reuseFailAlloc_921_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v_mctx_878_; lean_object* v_zetaDeltaFVarIds_879_; lean_object* v_postponed_880_; lean_object* v_diag_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_919_; 
v___x_876_ = lean_st_ref_put(v___y_850_, v___x_875_);
v___x_877_ = lean_st_ref_take(v___y_848_);
v_mctx_878_ = lean_ctor_get(v___x_877_, 0);
v_zetaDeltaFVarIds_879_ = lean_ctor_get(v___x_877_, 2);
v_postponed_880_ = lean_ctor_get(v___x_877_, 3);
v_diag_881_ = lean_ctor_get(v___x_877_, 4);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v___x_877_, 1);
lean_dec(v_unused_920_);
v___x_883_ = v___x_877_;
v_isShared_884_ = v_isSharedCheck_919_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_diag_881_);
lean_inc(v_postponed_880_);
lean_inc(v_zetaDeltaFVarIds_879_);
lean_inc(v_mctx_878_);
lean_dec(v___x_877_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_919_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v___x_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_mctx_878_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_zetaDeltaFVarIds_879_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_postponed_880_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_diag_881_);
v___x_887_ = v_reuseFailAlloc_918_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v_r_889_; 
v___x_888_ = lean_st_ref_put(v___y_848_, v___x_887_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v___y_848_);
lean_inc_ref(v___y_847_);
v_r_889_ = lean_apply_5(v_x_845_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, lean_box(0));
if (lean_obj_tag(v_r_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_906_; 
v_a_890_ = lean_ctor_get(v_r_889_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_r_889_);
if (v_isSharedCheck_906_ == 0)
{
v___x_892_ = v_r_889_;
v_isShared_893_ = v_isSharedCheck_906_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v_r_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_906_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
lean_inc(v_a_890_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 1);
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_905_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
v___x_896_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg___lam__0(v___y_850_, v_isExporting_857_, v___x_873_, v___y_848_, v___x_885_, v___x_895_);
lean_dec_ref(v___x_895_);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v___x_896_, 0);
lean_dec(v_unused_904_);
v___x_898_ = v___x_896_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_dec(v___x_896_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v_a_890_);
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_890_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_907_ = lean_ctor_get(v_r_889_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v_r_889_, 1);
v___x_908_ = lean_box(0);
v___x_909_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg___lam__0(v___y_850_, v_isExporting_857_, v___x_873_, v___y_848_, v___x_885_, v___x_908_);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v___x_909_, 0);
lean_dec(v_unused_917_);
v___x_911_ = v___x_909_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_dec(v___x_909_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set_tag(v___x_911_, 1);
lean_ctor_set(v___x_911_, 0, v_a_907_);
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_907_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg___boxed(lean_object* v_x_926_, lean_object* v_isExporting_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
uint8_t v_isExporting_boxed_933_; lean_object* v_res_934_; 
v_isExporting_boxed_933_ = lean_unbox(v_isExporting_927_);
v_res_934_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg(v_x_926_, v_isExporting_boxed_933_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(lean_object* v_declNameNonRec_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___f_941_; lean_object* v___f_942_; lean_object* v___x_943_; lean_object* v_env_944_; uint8_t v___x_945_; lean_object* v___x_946_; 
lean_inc_n(v_declNameNonRec_935_, 2);
v___f_941_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___boxed), 8, 1);
lean_closure_set(v___f_941_, 0, v_declNameNonRec_935_);
v___f_942_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___boxed), 7, 2);
lean_closure_set(v___f_942_, 0, v_declNameNonRec_935_);
lean_closure_set(v___f_942_, 1, v___f_941_);
v___x_943_ = lean_st_ref_get(v_a_939_);
v_env_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc_ref(v_env_944_);
lean_dec(v___x_943_);
v___x_945_ = l_Lean_Environment_hasExposedBody(v_env_944_, v_declNameNonRec_935_);
v___x_946_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg(v___f_942_, v___x_945_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___boxed(lean_object* v_declNameNonRec_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(v_declNameNonRec_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0(lean_object* v_00_u03b1_954_, lean_object* v_msg_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v_msg_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___boxed(lean_object* v_00_u03b1_962_, lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0(v_00_u03b1_962_, v_msg_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_spec__6(lean_object* v_00_u03b2_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg___boxed(lean_object* v___dummy_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg();
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4(lean_object* v_00_u03b2_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__4);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6(lean_object* v_00_u03b1_978_, lean_object* v_x_979_, uint8_t v_isExporting_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___redArg(v_x_979_, v_isExporting_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6___boxed(lean_object* v_00_u03b1_987_, lean_object* v_x_988_, lean_object* v_isExporting_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v_isExporting_boxed_995_; lean_object* v_res_996_; 
v_isExporting_boxed_995_ = lean_unbox(v_isExporting_989_);
v_res_996_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__6(v_00_u03b1_987_, v_x_988_, v_isExporting_boxed_995_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t v___x_997_, uint8_t v___x_998_, uint8_t v_____do__lift_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
if (v_____do__lift_999_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_box(v___x_997_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_box(v___x_998_);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v_____do__lift_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v___x_4360__boxed_1017_; uint8_t v___x_4361__boxed_1018_; uint8_t v_____do__lift_4362__boxed_1019_; lean_object* v_res_1020_; 
v___x_4360__boxed_1017_ = lean_unbox(v___x_1009_);
v___x_4361__boxed_1018_ = lean_unbox(v___x_1010_);
v_____do__lift_4362__boxed_1019_ = lean_unbox(v_____do__lift_1011_);
v_res_1020_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_4360__boxed_1017_, v___x_4361__boxed_1018_, v_____do__lift_4362__boxed_1019_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1020_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object* v_as_1021_, size_t v_i_1022_, size_t v_stop_1023_){
_start:
{
uint8_t v___x_1024_; 
v___x_1024_ = lean_usize_dec_eq(v_i_1022_, v_stop_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; uint8_t v_kind_1026_; uint8_t v___x_1027_; 
v___x_1025_ = lean_array_uget_borrowed(v_as_1021_, v_i_1022_);
v_kind_1026_ = lean_ctor_get_uint8(v___x_1025_, sizeof(void*)*9);
v___x_1027_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1026_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; 
v___x_1028_ = 1;
return v___x_1028_;
}
else
{
size_t v___x_1029_; size_t v___x_1030_; 
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_add(v_i_1022_, v___x_1029_);
v_i_1022_ = v___x_1030_;
goto _start;
}
}
else
{
uint8_t v___x_1032_; 
v___x_1032_ = 0;
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object* v_as_1033_, lean_object* v_i_1034_, lean_object* v_stop_1035_){
_start:
{
size_t v_i_boxed_1036_; size_t v_stop_boxed_1037_; uint8_t v_res_1038_; lean_object* v_r_1039_; 
v_i_boxed_1036_ = lean_unbox_usize(v_i_1034_);
lean_dec(v_i_1034_);
v_stop_boxed_1037_ = lean_unbox_usize(v_stop_1035_);
lean_dec(v_stop_1035_);
v_res_1038_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_as_1033_, v_i_boxed_1036_, v_stop_boxed_1037_);
lean_dec_ref(v_as_1033_);
v_r_1039_ = lean_box(v_res_1038_);
return v_r_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t v_sz_1040_, size_t v_i_1041_, lean_object* v_bs_1042_){
_start:
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_usize_dec_lt(v_i_1041_, v_sz_1040_);
if (v___x_1043_ == 0)
{
return v_bs_1042_;
}
else
{
lean_object* v_v_1044_; lean_object* v_declName_1045_; lean_object* v___x_1046_; lean_object* v_bs_x27_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
v_v_1044_ = lean_array_uget_borrowed(v_bs_1042_, v_i_1041_);
v_declName_1045_ = lean_ctor_get(v_v_1044_, 3);
lean_inc(v_declName_1045_);
v___x_1046_ = lean_unsigned_to_nat(0u);
v_bs_x27_1047_ = lean_array_uset(v_bs_1042_, v_i_1041_, v___x_1046_);
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_add(v_i_1041_, v___x_1048_);
v___x_1050_ = lean_array_uset(v_bs_x27_1047_, v_i_1041_, v_declName_1045_);
v_i_1041_ = v___x_1049_;
v_bs_1042_ = v___x_1050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object* v_sz_1052_, lean_object* v_i_1053_, lean_object* v_bs_1054_){
_start:
{
size_t v_sz_boxed_1055_; size_t v_i_boxed_1056_; lean_object* v_res_1057_; 
v_sz_boxed_1055_ = lean_unbox_usize(v_sz_1052_);
lean_dec(v_sz_1052_);
v_i_boxed_1056_ = lean_unbox_usize(v_i_1053_);
lean_dec(v_i_1053_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_boxed_1055_, v_i_boxed_1056_, v_bs_1054_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object* v___x_1058_, lean_object* v_declNameNonRec_1059_, lean_object* v_fixedParamPerms_1060_, lean_object* v_fixpointType_1061_, lean_object* v_fixEq_x3f_1062_, uint8_t v_a_1063_, lean_object* v_as_1064_, size_t v_i_1065_, size_t v_stop_1066_, lean_object* v_b_1067_){
_start:
{
uint8_t v___x_1068_; 
v___x_1068_ = lean_usize_dec_eq(v_i_1065_, v_stop_1066_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v_levelParams_1070_; lean_object* v_declName_1071_; lean_object* v_type_1072_; lean_object* v_value_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; size_t v___x_1077_; size_t v___x_1078_; 
v___x_1069_ = lean_array_uget_borrowed(v_as_1064_, v_i_1065_);
v_levelParams_1070_ = lean_ctor_get(v___x_1069_, 1);
v_declName_1071_ = lean_ctor_get(v___x_1069_, 3);
v_type_1072_ = lean_ctor_get(v___x_1069_, 6);
v_value_1073_ = lean_ctor_get(v___x_1069_, 7);
v___x_1074_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
lean_inc(v_fixEq_x3f_1062_);
lean_inc_ref(v_fixpointType_1061_);
lean_inc_ref(v_fixedParamPerms_1060_);
lean_inc(v_declNameNonRec_1059_);
lean_inc_ref(v___x_1058_);
lean_inc_ref(v_value_1073_);
lean_inc_ref(v_type_1072_);
lean_inc(v_levelParams_1070_);
lean_inc_n(v_declName_1071_, 2);
v___x_1075_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1075_, 0, v_declName_1071_);
lean_ctor_set(v___x_1075_, 1, v_levelParams_1070_);
lean_ctor_set(v___x_1075_, 2, v_type_1072_);
lean_ctor_set(v___x_1075_, 3, v_value_1073_);
lean_ctor_set(v___x_1075_, 4, v___x_1058_);
lean_ctor_set(v___x_1075_, 5, v_declNameNonRec_1059_);
lean_ctor_set(v___x_1075_, 6, v_fixedParamPerms_1060_);
lean_ctor_set(v___x_1075_, 7, v_fixpointType_1061_);
lean_ctor_set(v___x_1075_, 8, v_fixEq_x3f_1062_);
v___x_1076_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1074_, v_b_1067_, v_declName_1071_, v___x_1075_, v_a_1063_);
v___x_1077_ = ((size_t)1ULL);
v___x_1078_ = lean_usize_add(v_i_1065_, v___x_1077_);
v_i_1065_ = v___x_1078_;
v_b_1067_ = v___x_1076_;
goto _start;
}
else
{
lean_dec(v_fixEq_x3f_1062_);
lean_dec_ref(v_fixpointType_1061_);
lean_dec_ref(v_fixedParamPerms_1060_);
lean_dec(v_declNameNonRec_1059_);
lean_dec_ref(v___x_1058_);
return v_b_1067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object* v___x_1080_, lean_object* v_declNameNonRec_1081_, lean_object* v_fixedParamPerms_1082_, lean_object* v_fixpointType_1083_, lean_object* v_fixEq_x3f_1084_, lean_object* v_a_1085_, lean_object* v_as_1086_, lean_object* v_i_1087_, lean_object* v_stop_1088_, lean_object* v_b_1089_){
_start:
{
uint8_t v_a_4421__boxed_1090_; size_t v_i_boxed_1091_; size_t v_stop_boxed_1092_; lean_object* v_res_1093_; 
v_a_4421__boxed_1090_ = lean_unbox(v_a_1085_);
v_i_boxed_1091_ = lean_unbox_usize(v_i_1087_);
lean_dec(v_i_1087_);
v_stop_boxed_1092_ = lean_unbox_usize(v_stop_1088_);
lean_dec(v_stop_1088_);
v_res_1093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_1080_, v_declNameNonRec_1081_, v_fixedParamPerms_1082_, v_fixpointType_1083_, v_fixEq_x3f_1084_, v_a_4421__boxed_1090_, v_as_1086_, v_i_boxed_1091_, v_stop_boxed_1092_, v_b_1089_);
lean_dec_ref(v_as_1086_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object* v_as_1094_, size_t v_i_1095_, size_t v_stop_1096_, lean_object* v_b_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
uint8_t v___x_1101_; 
v___x_1101_ = lean_usize_dec_eq(v_i_1095_, v_stop_1096_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v_declName_1103_; lean_object* v___x_1104_; 
v___x_1102_ = lean_array_uget_borrowed(v_as_1094_, v_i_1095_);
v_declName_1103_ = lean_ctor_get(v___x_1102_, 3);
lean_inc(v_declName_1103_);
v___x_1104_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_1103_, v___y_1098_, v___y_1099_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; size_t v___x_1106_; size_t v___x_1107_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v___x_1106_ = ((size_t)1ULL);
v___x_1107_ = lean_usize_add(v_i_1095_, v___x_1106_);
v_i_1095_ = v___x_1107_;
v_b_1097_ = v_a_1105_;
goto _start;
}
else
{
return v___x_1104_;
}
}
else
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_b_1097_);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object* v_as_1110_, lean_object* v_i_1111_, lean_object* v_stop_1112_, lean_object* v_b_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
size_t v_i_boxed_1117_; size_t v_stop_boxed_1118_; lean_object* v_res_1119_; 
v_i_boxed_1117_ = lean_unbox_usize(v_i_1111_);
lean_dec(v_i_1111_);
v_stop_boxed_1118_ = lean_unbox_usize(v_stop_1112_);
lean_dec(v_stop_1112_);
v_res_1119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_1110_, v_i_boxed_1117_, v_stop_boxed_1118_, v_b_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v_as_1110_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t v___x_1120_, lean_object* v_as_1121_, size_t v_i_1122_, size_t v_stop_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_usize_dec_eq(v_i_1122_, v_stop_1123_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v_type_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1134_ = lean_array_uget_borrowed(v_as_1121_, v_i_1122_);
v_type_1135_ = lean_ctor_get(v___x_1134_, 6);
v___x_1136_ = 1;
lean_inc_ref(v_type_1135_);
v___x_1137_ = l_Lean_Meta_isProp(v_type_1135_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1147_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
uint8_t v___x_1142_; 
v___x_1142_ = lean_unbox(v_a_1138_);
lean_dec(v_a_1138_);
if (v___x_1142_ == 0)
{
if (v___x_1120_ == 0)
{
lean_del_object(v___x_1140_);
goto v___jp_1129_;
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_box(v___x_1136_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_del_object(v___x_1140_);
goto v___jp_1129_;
}
}
}
else
{
return v___x_1137_;
}
}
else
{
uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = 0;
v___x_1149_ = lean_box(v___x_1148_);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
v___jp_1129_:
{
size_t v___x_1130_; size_t v___x_1131_; 
v___x_1130_ = ((size_t)1ULL);
v___x_1131_ = lean_usize_add(v_i_1122_, v___x_1130_);
v_i_1122_ = v___x_1131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object* v___x_1151_, lean_object* v_as_1152_, lean_object* v_i_1153_, lean_object* v_stop_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
uint8_t v___x_4468__boxed_1160_; size_t v_i_boxed_1161_; size_t v_stop_boxed_1162_; lean_object* v_res_1163_; 
v___x_4468__boxed_1160_ = lean_unbox(v___x_1151_);
v_i_boxed_1161_ = lean_unbox_usize(v_i_1153_);
lean_dec(v_i_1153_);
v_stop_boxed_1162_ = lean_unbox_usize(v_stop_1154_);
lean_dec(v_stop_1154_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_4468__boxed_1160_, v_as_1152_, v_i_boxed_1161_, v_stop_boxed_1162_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec_ref(v_as_1152_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object* v_preDefs_1164_, lean_object* v_declNameNonRec_1165_, lean_object* v_fixedParamPerms_1166_, lean_object* v_fixpointType_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v_nextMacroScope_1184_; lean_object* v_ngen_1185_; lean_object* v_auxDeclNGen_1186_; lean_object* v_traceState_1187_; lean_object* v_recordedDeps_1188_; lean_object* v_messages_1189_; lean_object* v_infoState_1190_; lean_object* v_snapshotTasks_1191_; lean_object* v___y_1192_; lean_object* v___x_1213_; uint8_t v___y_1215_; size_t v___y_1216_; lean_object* v___y_1217_; lean_object* v_fixEq_x3f_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1235_; uint8_t v___x_1283_; 
v___x_1179_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_array_get_size(v_preDefs_1164_);
v___x_1283_ = lean_nat_dec_lt(v___x_1180_, v___x_1213_);
if (v___x_1283_ == 0)
{
goto v___jp_1264_;
}
else
{
lean_object* v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = lean_box(0);
v___x_1285_ = ((size_t)0ULL);
v___x_1286_ = lean_usize_of_nat(v___x_1213_);
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_1164_, v___x_1285_, v___x_1286_, v___x_1284_, v_a_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_dec_ref_known(v___x_1287_, 1);
goto v___jp_1264_;
}
else
{
lean_dec_ref(v_fixpointType_1167_);
lean_dec_ref(v_fixedParamPerms_1166_);
lean_dec(v_declNameNonRec_1165_);
lean_dec_ref(v_preDefs_1164_);
return v___x_1287_;
}
}
v___jp_1173_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
v___jp_1176_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
v___jp_1181_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v_mctx_1197_; lean_object* v_zetaDeltaFVarIds_1198_; lean_object* v_postponed_1199_; lean_object* v_diag_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1211_; 
v___x_1193_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3);
v___x_1194_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1194_, 0, v___y_1192_);
lean_ctor_set(v___x_1194_, 1, v_nextMacroScope_1184_);
lean_ctor_set(v___x_1194_, 2, v_ngen_1185_);
lean_ctor_set(v___x_1194_, 3, v_auxDeclNGen_1186_);
lean_ctor_set(v___x_1194_, 4, v_traceState_1187_);
lean_ctor_set(v___x_1194_, 5, v___x_1193_);
lean_ctor_set(v___x_1194_, 6, v_recordedDeps_1188_);
lean_ctor_set(v___x_1194_, 7, v_messages_1189_);
lean_ctor_set(v___x_1194_, 8, v_infoState_1190_);
lean_ctor_set(v___x_1194_, 9, v_snapshotTasks_1191_);
v___x_1195_ = lean_st_ref_put(v___y_1183_, v___x_1194_);
v___x_1196_ = lean_st_ref_take(v___y_1182_);
v_mctx_1197_ = lean_ctor_get(v___x_1196_, 0);
v_zetaDeltaFVarIds_1198_ = lean_ctor_get(v___x_1196_, 2);
v_postponed_1199_ = lean_ctor_get(v___x_1196_, 3);
v_diag_1200_ = lean_ctor_get(v___x_1196_, 4);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v___x_1196_, 1);
lean_dec(v_unused_1212_);
v___x_1202_ = v___x_1196_;
v_isShared_1203_ = v_isSharedCheck_1211_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_diag_1200_);
lean_inc(v_postponed_1199_);
lean_inc(v_zetaDeltaFVarIds_1198_);
lean_inc(v_mctx_1197_);
lean_dec(v___x_1196_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1211_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__7);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v___x_1205_);
v___x_1207_ = v___x_1202_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_mctx_1197_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_zetaDeltaFVarIds_1198_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_postponed_1199_);
lean_ctor_set(v_reuseFailAlloc_1210_, 4, v_diag_1200_);
v___x_1207_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_st_ref_put(v___y_1182_, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1204_);
return v___x_1209_;
}
}
}
v___jp_1214_:
{
lean_object* v___x_1221_; lean_object* v_env_1222_; lean_object* v_nextMacroScope_1223_; lean_object* v_ngen_1224_; lean_object* v_auxDeclNGen_1225_; lean_object* v_traceState_1226_; lean_object* v_recordedDeps_1227_; lean_object* v_messages_1228_; lean_object* v_infoState_1229_; lean_object* v_snapshotTasks_1230_; uint8_t v___x_1231_; 
v___x_1221_ = lean_st_ref_take(v___y_1220_);
v_env_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc_ref(v_env_1222_);
v_nextMacroScope_1223_ = lean_ctor_get(v___x_1221_, 1);
lean_inc(v_nextMacroScope_1223_);
v_ngen_1224_ = lean_ctor_get(v___x_1221_, 2);
lean_inc_ref(v_ngen_1224_);
v_auxDeclNGen_1225_ = lean_ctor_get(v___x_1221_, 3);
lean_inc_ref(v_auxDeclNGen_1225_);
v_traceState_1226_ = lean_ctor_get(v___x_1221_, 4);
lean_inc_ref(v_traceState_1226_);
v_recordedDeps_1227_ = lean_ctor_get(v___x_1221_, 6);
lean_inc_ref(v_recordedDeps_1227_);
v_messages_1228_ = lean_ctor_get(v___x_1221_, 7);
lean_inc_ref(v_messages_1228_);
v_infoState_1229_ = lean_ctor_get(v___x_1221_, 8);
lean_inc_ref(v_infoState_1229_);
v_snapshotTasks_1230_ = lean_ctor_get(v___x_1221_, 9);
lean_inc_ref(v_snapshotTasks_1230_);
lean_dec(v___x_1221_);
v___x_1231_ = lean_nat_dec_lt(v___x_1180_, v___x_1213_);
if (v___x_1231_ == 0)
{
lean_dec(v_fixEq_x3f_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v_fixpointType_1167_);
lean_dec_ref(v_fixedParamPerms_1166_);
lean_dec(v_declNameNonRec_1165_);
lean_dec_ref(v_preDefs_1164_);
v___y_1182_ = v___y_1219_;
v___y_1183_ = v___y_1220_;
v_nextMacroScope_1184_ = v_nextMacroScope_1223_;
v_ngen_1185_ = v_ngen_1224_;
v_auxDeclNGen_1186_ = v_auxDeclNGen_1225_;
v_traceState_1187_ = v_traceState_1226_;
v_recordedDeps_1188_ = v_recordedDeps_1227_;
v_messages_1189_ = v_messages_1228_;
v_infoState_1190_ = v_infoState_1229_;
v_snapshotTasks_1191_ = v_snapshotTasks_1230_;
v___y_1192_ = v_env_1222_;
goto v___jp_1181_;
}
else
{
size_t v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_usize_of_nat(v___x_1213_);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___y_1217_, v_declNameNonRec_1165_, v_fixedParamPerms_1166_, v_fixpointType_1167_, v_fixEq_x3f_1218_, v___y_1215_, v_preDefs_1164_, v___y_1216_, v___x_1232_, v_env_1222_);
lean_dec_ref(v_preDefs_1164_);
v___y_1182_ = v___y_1219_;
v___y_1183_ = v___y_1220_;
v_nextMacroScope_1184_ = v_nextMacroScope_1223_;
v_ngen_1185_ = v_ngen_1224_;
v_auxDeclNGen_1186_ = v_auxDeclNGen_1225_;
v_traceState_1187_ = v_traceState_1226_;
v_recordedDeps_1188_ = v_recordedDeps_1227_;
v_messages_1189_ = v_messages_1228_;
v_infoState_1190_ = v_infoState_1229_;
v_snapshotTasks_1191_ = v_snapshotTasks_1230_;
v___y_1192_ = v___x_1233_;
goto v___jp_1181_;
}
}
v___jp_1234_:
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1263_; 
v_a_1236_ = lean_ctor_get(v___y_1235_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___y_1235_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1238_ = v___y_1235_;
v_isShared_1239_ = v_isSharedCheck_1263_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___y_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1263_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
uint8_t v___x_1240_; 
v___x_1240_ = lean_unbox(v_a_1236_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v_declName_1242_; size_t v_sz_1243_; size_t v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1241_ = lean_array_get_borrowed(v___x_1179_, v_preDefs_1164_, v___x_1180_);
v_declName_1242_ = lean_ctor_get(v___x_1241_, 3);
v_sz_1243_ = lean_array_size(v_preDefs_1164_);
v___x_1244_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_1164_);
v___x_1245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_1243_, v___x_1244_, v_preDefs_1164_);
v___x_1246_ = lean_name_eq(v_declNameNonRec_1165_, v_declName_1242_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
lean_inc(v_declNameNonRec_1165_);
v___x_1247_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(v_declNameNonRec_1165_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
if (v_isShared_1239_ == 0)
{
lean_ctor_set_tag(v___x_1238_, 1);
lean_ctor_set(v___x_1238_, 0, v_a_1248_);
v___x_1250_ = v___x_1238_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1248_);
v___x_1250_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_unbox(v_a_1236_);
lean_dec(v_a_1236_);
v___y_1215_ = v___x_1251_;
v___y_1216_ = v___x_1244_;
v___y_1217_ = v___x_1245_;
v_fixEq_x3f_1218_ = v___x_1250_;
v___y_1219_ = v_a_1169_;
v___y_1220_ = v_a_1171_;
goto v___jp_1214_;
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref(v___x_1245_);
lean_del_object(v___x_1238_);
lean_dec(v_a_1236_);
lean_dec_ref(v_fixpointType_1167_);
lean_dec_ref(v_fixedParamPerms_1166_);
lean_dec(v_declNameNonRec_1165_);
lean_dec_ref(v_preDefs_1164_);
v_a_1253_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1247_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1247_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
lean_del_object(v___x_1238_);
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_unbox(v_a_1236_);
lean_dec(v_a_1236_);
v___y_1215_ = v___x_1262_;
v___y_1216_ = v___x_1244_;
v___y_1217_ = v___x_1245_;
v_fixEq_x3f_1218_ = v___x_1261_;
v___y_1219_ = v_a_1169_;
v___y_1220_ = v_a_1171_;
goto v___jp_1214_;
}
}
else
{
lean_del_object(v___x_1238_);
lean_dec(v_a_1236_);
lean_dec_ref(v_fixpointType_1167_);
lean_dec_ref(v_fixedParamPerms_1166_);
lean_dec(v_declNameNonRec_1165_);
lean_dec_ref(v_preDefs_1164_);
goto v___jp_1173_;
}
}
}
v___jp_1264_:
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_nat_dec_lt(v___x_1180_, v___x_1213_);
if (v___x_1265_ == 0)
{
lean_dec_ref(v_fixpointType_1167_);
lean_dec_ref(v_fixedParamPerms_1166_);
lean_dec(v_declNameNonRec_1165_);
lean_dec_ref(v_preDefs_1164_);
goto v___jp_1176_;
}
else
{
if (v___x_1265_ == 0)
{
lean_dec_ref(v_fixpointType_1167_);
lean_dec_ref(v_fixedParamPerms_1166_);
lean_dec(v_declNameNonRec_1165_);
lean_dec_ref(v_preDefs_1164_);
goto v___jp_1176_;
}
else
{
size_t v___x_1266_; size_t v___x_1267_; uint8_t v___x_1268_; 
v___x_1266_ = ((size_t)0ULL);
v___x_1267_ = lean_usize_of_nat(v___x_1213_);
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_preDefs_1164_, v___x_1266_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_dec_ref(v_fixpointType_1167_);
lean_dec_ref(v_fixedParamPerms_1166_);
lean_dec(v_declNameNonRec_1165_);
lean_dec_ref(v_preDefs_1164_);
goto v___jp_1176_;
}
else
{
uint8_t v___x_1269_; 
v___x_1269_ = 0;
if (v___x_1265_ == 0)
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_1268_, v___x_1269_, v___x_1265_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
v___y_1235_ = v___x_1270_;
goto v___jp_1234_;
}
else
{
if (v___x_1265_ == 0)
{
lean_dec_ref(v_fixpointType_1167_);
lean_dec_ref(v_fixedParamPerms_1166_);
lean_dec(v_declNameNonRec_1165_);
lean_dec_ref(v_preDefs_1164_);
goto v___jp_1173_;
}
else
{
lean_object* v___x_1271_; 
v___x_1271_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_1268_, v_preDefs_1164_, v___x_1266_, v___x_1267_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; uint8_t v___x_1273_; lean_object* v___x_1274_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v___x_1273_ = lean_unbox(v_a_1272_);
lean_dec(v_a_1272_);
v___x_1274_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_1268_, v___x_1269_, v___x_1273_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
v___y_1235_ = v___x_1274_;
goto v___jp_1234_;
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec_ref(v_fixpointType_1167_);
lean_dec_ref(v_fixedParamPerms_1166_);
lean_dec(v_declNameNonRec_1165_);
lean_dec_ref(v_preDefs_1164_);
v_a_1275_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1271_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1271_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(lean_object* v_preDefs_1288_, lean_object* v_declNameNonRec_1289_, lean_object* v_fixedParamPerms_1290_, lean_object* v_fixpointType_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_preDefs_1288_, v_declNameNonRec_1289_, v_fixedParamPerms_1290_, v_fixpointType_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object* v_as_1298_, size_t v_i_1299_, size_t v_stop_1300_, lean_object* v_b_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_1298_, v_i_1299_, v_stop_1300_, v_b_1301_, v___y_1304_, v___y_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object* v_as_1308_, lean_object* v_i_1309_, lean_object* v_stop_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
size_t v_i_boxed_1317_; size_t v_stop_boxed_1318_; lean_object* v_res_1319_; 
v_i_boxed_1317_ = lean_unbox_usize(v_i_1309_);
lean_dec(v_i_1309_);
v_stop_boxed_1318_ = lean_unbox_usize(v_stop_1310_);
lean_dec(v_stop_1310_);
v_res_1319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(v_as_1308_, v_i_boxed_1317_, v_stop_boxed_1318_, v_b_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec_ref(v_as_1308_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(lean_object* v_mvarId_1320_, lean_object* v_x_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1320_, v_x_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
v_a_1336_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1327_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1327_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg___boxed(lean_object* v_mvarId_1344_, lean_object* v_x_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1344_, v_x_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(lean_object* v_00_u03b1_1352_, lean_object* v_mvarId_1353_, lean_object* v_x_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1353_, v_x_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(lean_object* v_00_u03b1_1361_, lean_object* v_mvarId_1362_, lean_object* v_x_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(v_00_u03b1_1361_, v_mvarId_1362_, v_x_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
return v_res_1369_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object* v_declName_1370_, lean_object* v_declNameNonRec_1371_, lean_object* v_n_1372_){
_start:
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_name_eq(v_n_1372_, v_declName_1370_);
if (v___x_1373_ == 0)
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_name_eq(v_n_1372_, v_declNameNonRec_1371_);
return v___x_1374_;
}
else
{
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object* v_declName_1375_, lean_object* v_declNameNonRec_1376_, lean_object* v_n_1377_){
_start:
{
uint8_t v_res_1378_; lean_object* v_r_1379_; 
v_res_1378_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(v_declName_1375_, v_declNameNonRec_1376_, v_n_1377_);
lean_dec(v_n_1377_);
lean_dec(v_declNameNonRec_1376_);
lean_dec(v_declName_1375_);
v_r_1379_ = lean_box(v_res_1378_);
return v_r_1379_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5));
v___x_1390_ = l_Lean_MessageData_ofFormat(v___x_1389_);
return v___x_1390_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6);
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object* v_mvarId_1393_, lean_object* v___f_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
lean_inc(v_mvarId_1393_);
v___x_1400_ = l_Lean_MVarId_getType_x27(v_mvarId_1393_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1402_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_1403_ = lean_unsigned_to_nat(3u);
v___x_1404_ = l_Lean_Expr_isAppOfArity(v_a_1401_, v___x_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec(v_a_1401_);
lean_dec_ref(v___f_1394_);
v___x_1405_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3));
v___x_1406_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7);
v___x_1407_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1405_, v_mvarId_1393_, v___x_1406_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
return v___x_1407_;
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1408_ = l_Lean_Expr_appFn_x21(v_a_1401_);
v___x_1409_ = l_Lean_Expr_appArg_x21(v___x_1408_);
lean_dec_ref(v___x_1408_);
v___x_1410_ = l_Lean_Expr_appArg_x21(v_a_1401_);
lean_dec(v_a_1401_);
v___x_1411_ = 0;
v___x_1412_ = l_Lean_Meta_deltaExpand(v___x_1409_, v___f_1394_, v___x_1411_, v___y_1397_, v___y_1398_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = l_Lean_Meta_mkEq(v_a_1413_, v___x_1410_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1393_, v_a_1415_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
return v___x_1416_;
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec(v_mvarId_1393_);
v_a_1417_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1414_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1414_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v___x_1410_);
lean_dec(v_mvarId_1393_);
v_a_1425_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1412_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1412_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v___f_1394_);
lean_dec(v_mvarId_1393_);
v_a_1433_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1400_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1400_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed(lean_object* v_mvarId_1441_, lean_object* v___f_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(v_mvarId_1441_, v___f_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object* v_declName_1449_, lean_object* v_declNameNonRec_1450_, lean_object* v_mvarId_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v___f_1457_; lean_object* v___f_1458_; lean_object* v___x_1459_; 
v___f_1457_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1457_, 0, v_declName_1449_);
lean_closure_set(v___f_1457_, 1, v_declNameNonRec_1450_);
lean_inc(v_mvarId_1451_);
v___f_1458_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1458_, 0, v_mvarId_1451_);
lean_closure_set(v___f_1458_, 1, v___f_1457_);
v___x_1459_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1451_, v___f_1458_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(lean_object* v_declName_1460_, lean_object* v_declNameNonRec_1461_, lean_object* v_mvarId_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_1460_, v_declNameNonRec_1461_, v_mvarId_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(lean_object* v_msg_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = l_Lean_instInhabitedExpr;
v___x_1471_ = lean_panic_fn_borrowed(v___x_1470_, v_msg_1469_);
return v___x_1471_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0));
v___x_1474_ = l_Lean_stringToMessageData(v___x_1473_);
return v___x_1474_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = l_Lean_Expr_bvar___override(v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1486_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9));
v___x_1487_ = lean_unsigned_to_nat(18u);
v___x_1488_ = lean_unsigned_to_nat(1955u);
v___x_1489_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8));
v___x_1490_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7));
v___x_1491_ = l_mkPanicMessageWithDecl(v___x_1490_, v___x_1489_, v___x_1488_, v___x_1487_, v___x_1486_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(lean_object* v_lhs_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2));
v___x_1502_ = lean_unsigned_to_nat(4u);
v___x_1503_ = l_Lean_Expr_isAppOfArity(v_lhs_1495_, v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4));
v___x_1505_ = l_Lean_Expr_isAppOfArity(v_lhs_1495_, v___x_1504_, v___x_1502_);
if (v___x_1505_ == 0)
{
uint8_t v___x_1506_; 
v___x_1506_ = l_Lean_Expr_isApp(v_lhs_1495_);
if (v___x_1506_ == 0)
{
uint8_t v___x_1507_; 
v___x_1507_ = l_Lean_Expr_isProj(v_lhs_1495_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1508_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1);
v___x_1509_ = l_Lean_MessageData_ofExpr(v_lhs_1495_);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_1510_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = l_Lean_Expr_projExpr_x21(v_lhs_1495_);
lean_inc(v_a_1499_);
lean_inc_ref(v_a_1498_);
lean_inc(v_a_1497_);
lean_inc_ref(v_a_1496_);
lean_inc_ref(v___x_1512_);
v___x_1513_ = lean_infer_type(v___x_1512_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; lean_object* v___y_1518_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3));
v___x_1516_ = 0;
if (lean_obj_tag(v_lhs_1495_) == 11)
{
lean_object* v_typeName_1528_; lean_object* v_idx_1529_; lean_object* v_struct_1530_; lean_object* v___x_1531_; size_t v___x_1532_; size_t v___x_1533_; uint8_t v___x_1534_; 
v_typeName_1528_ = lean_ctor_get(v_lhs_1495_, 0);
v_idx_1529_ = lean_ctor_get(v_lhs_1495_, 1);
v_struct_1530_ = lean_ctor_get(v_lhs_1495_, 2);
v___x_1531_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
v___x_1532_ = lean_ptr_addr(v_struct_1530_);
v___x_1533_ = lean_ptr_addr(v___x_1531_);
v___x_1534_ = lean_usize_dec_eq(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_inc(v_idx_1529_);
lean_inc(v_typeName_1528_);
lean_dec_ref_known(v_lhs_1495_, 3);
v___x_1535_ = l_Lean_Expr_proj___override(v_typeName_1528_, v_idx_1529_, v___x_1531_);
v___y_1518_ = v___x_1535_;
goto v___jp_1517_;
}
else
{
v___y_1518_ = v_lhs_1495_;
goto v___jp_1517_;
}
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec_ref(v_lhs_1495_);
v___x_1536_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10);
v___x_1537_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(v___x_1536_);
v___y_1518_ = v___x_1537_;
goto v___jp_1517_;
}
v___jp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = l_Lean_mkLambda(v___x_1515_, v___x_1516_, v_a_1514_, v___y_1518_);
v___x_1520_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1512_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v___x_1522_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5));
v___x_1523_ = lean_unsigned_to_nat(2u);
v___x_1524_ = lean_mk_empty_array_with_capacity(v___x_1523_);
v___x_1525_ = lean_array_push(v___x_1524_, v___x_1519_);
v___x_1526_ = lean_array_push(v___x_1525_, v_a_1521_);
v___x_1527_ = l_Lean_Meta_mkAppM(v___x_1522_, v___x_1526_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1527_;
}
else
{
lean_dec_ref(v___x_1519_);
return v___x_1520_;
}
}
}
else
{
lean_dec_ref(v___x_1512_);
lean_dec_ref(v_lhs_1495_);
return v___x_1513_;
}
}
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = l_Lean_Expr_appFn_x21(v_lhs_1495_);
v___x_1539_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1538_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v___x_1541_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12));
v___x_1542_ = l_Lean_Expr_appArg_x21(v_lhs_1495_);
lean_dec_ref(v_lhs_1495_);
v___x_1543_ = lean_unsigned_to_nat(2u);
v___x_1544_ = lean_mk_empty_array_with_capacity(v___x_1543_);
v___x_1545_ = lean_array_push(v___x_1544_, v_a_1540_);
v___x_1546_ = lean_array_push(v___x_1545_, v___x_1542_);
v___x_1547_ = l_Lean_Meta_mkAppM(v___x_1541_, v___x_1546_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1547_;
}
else
{
lean_dec_ref(v_lhs_1495_);
return v___x_1539_;
}
}
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v_dummy_1552_; lean_object* v_nargs_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1548_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2));
v___x_1549_ = l_Lean_Expr_getAppFn(v_lhs_1495_);
v___x_1550_ = l_Lean_Expr_constLevels_x21(v___x_1549_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l_Lean_mkConst(v___x_1548_, v___x_1550_);
v_dummy_1552_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_1553_ = l_Lean_Expr_getAppNumArgs(v_lhs_1495_);
lean_inc(v_nargs_1553_);
v___x_1554_ = lean_mk_array(v_nargs_1553_, v_dummy_1552_);
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_nat_sub(v_nargs_1553_, v___x_1555_);
lean_dec(v_nargs_1553_);
v___x_1557_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_1495_, v___x_1554_, v___x_1556_);
v___x_1558_ = l_Lean_mkAppN(v___x_1551_, v___x_1557_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_dummy_1564_; lean_object* v_nargs_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1560_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4));
v___x_1561_ = l_Lean_Expr_getAppFn(v_lhs_1495_);
v___x_1562_ = l_Lean_Expr_constLevels_x21(v___x_1561_);
lean_dec_ref(v___x_1561_);
v___x_1563_ = l_Lean_mkConst(v___x_1560_, v___x_1562_);
v_dummy_1564_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_1565_ = l_Lean_Expr_getAppNumArgs(v_lhs_1495_);
lean_inc(v_nargs_1565_);
v___x_1566_ = lean_mk_array(v_nargs_1565_, v_dummy_1564_);
v___x_1567_ = lean_unsigned_to_nat(1u);
v___x_1568_ = lean_nat_sub(v_nargs_1565_, v___x_1567_);
lean_dec(v_nargs_1565_);
v___x_1569_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_1495_, v___x_1566_, v___x_1568_);
v___x_1570_ = l_Lean_mkAppN(v___x_1563_, v___x_1569_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
return v___x_1571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(lean_object* v_lhs_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v_lhs_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(lean_object* v_msg_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___f_1586_; lean_object* v___x_1515__overap_1587_; lean_object* v___x_1588_; 
v___f_1586_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0));
v___x_1515__overap_1587_ = lean_panic_fn_borrowed(v___f_1586_, v_msg_1580_);
lean_inc(v___y_1584_);
lean_inc_ref(v___y_1583_);
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1581_);
v___x_1588_ = lean_apply_5(v___x_1515__overap_1587_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, lean_box(0));
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(lean_object* v_msg_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v_msg_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1596_, lean_object* v_x_1597_, lean_object* v_x_1598_, lean_object* v_x_1599_){
_start:
{
lean_object* v_ks_1600_; lean_object* v_vs_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1625_; 
v_ks_1600_ = lean_ctor_get(v_x_1596_, 0);
v_vs_1601_ = lean_ctor_get(v_x_1596_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_x_1596_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1603_ = v_x_1596_;
v_isShared_1604_ = v_isSharedCheck_1625_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_vs_1601_);
lean_inc(v_ks_1600_);
lean_dec(v_x_1596_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1625_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = lean_array_get_size(v_ks_1600_);
v___x_1606_ = lean_nat_dec_lt(v_x_1597_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
lean_dec(v_x_1597_);
v___x_1607_ = lean_array_push(v_ks_1600_, v_x_1598_);
v___x_1608_ = lean_array_push(v_vs_1601_, v_x_1599_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1608_);
lean_ctor_set(v___x_1603_, 0, v___x_1607_);
v___x_1610_ = v___x_1603_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
else
{
lean_object* v_k_x27_1612_; uint8_t v___x_1613_; 
v_k_x27_1612_ = lean_array_fget_borrowed(v_ks_1600_, v_x_1597_);
v___x_1613_ = l_Lean_instBEqMVarId_beq(v_x_1598_, v_k_x27_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1615_; 
if (v_isShared_1604_ == 0)
{
v___x_1615_ = v___x_1603_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_ks_1600_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_vs_1601_);
v___x_1615_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_unsigned_to_nat(1u);
v___x_1617_ = lean_nat_add(v_x_1597_, v___x_1616_);
lean_dec(v_x_1597_);
v_x_1596_ = v___x_1615_;
v_x_1597_ = v___x_1617_;
goto _start;
}
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1620_ = lean_array_fset(v_ks_1600_, v_x_1597_, v_x_1598_);
v___x_1621_ = lean_array_fset(v_vs_1601_, v_x_1597_, v_x_1599_);
lean_dec(v_x_1597_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1621_);
lean_ctor_set(v___x_1603_, 0, v___x_1620_);
v___x_1623_ = v___x_1603_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_1626_, lean_object* v_k_1627_, lean_object* v_v_1628_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_1626_, v___x_1629_, v_k_1627_, v_v_1628_);
return v___x_1630_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1632_, size_t v_x_1633_, size_t v_x_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_){
_start:
{
if (lean_obj_tag(v_x_1632_) == 0)
{
lean_object* v_es_1637_; size_t v___x_1638_; size_t v___x_1639_; lean_object* v_j_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v_es_1637_ = lean_ctor_get(v_x_1632_, 0);
v___x_1638_ = ((size_t)31ULL);
v___x_1639_ = lean_usize_land(v_x_1633_, v___x_1638_);
v_j_1640_ = lean_usize_to_nat(v___x_1639_);
v___x_1641_ = lean_array_get_size(v_es_1637_);
v___x_1642_ = lean_nat_dec_lt(v_j_1640_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_dec(v_j_1640_);
lean_dec(v_x_1636_);
lean_dec(v_x_1635_);
return v_x_1632_;
}
else
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1681_; 
lean_inc_ref(v_es_1637_);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_x_1632_);
if (v_isSharedCheck_1681_ == 0)
{
lean_object* v_unused_1682_; 
v_unused_1682_ = lean_ctor_get(v_x_1632_, 0);
lean_dec(v_unused_1682_);
v___x_1644_ = v_x_1632_;
v_isShared_1645_ = v_isSharedCheck_1681_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v_x_1632_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1681_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_v_1646_; lean_object* v___x_1647_; lean_object* v_xs_x27_1648_; lean_object* v___y_1650_; 
v_v_1646_ = lean_array_fget(v_es_1637_, v_j_1640_);
v___x_1647_ = lean_box(0);
v_xs_x27_1648_ = lean_array_fset(v_es_1637_, v_j_1640_, v___x_1647_);
switch(lean_obj_tag(v_v_1646_))
{
case 0:
{
lean_object* v_key_1655_; lean_object* v_val_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1666_; 
v_key_1655_ = lean_ctor_get(v_v_1646_, 0);
v_val_1656_ = lean_ctor_get(v_v_1646_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_v_1646_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1658_ = v_v_1646_;
v_isShared_1659_ = v_isSharedCheck_1666_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_val_1656_);
lean_inc(v_key_1655_);
lean_dec(v_v_1646_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1666_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
uint8_t v___x_1660_; 
v___x_1660_ = l_Lean_instBEqMVarId_beq(v_x_1635_, v_key_1655_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_del_object(v___x_1658_);
v___x_1661_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1655_, v_val_1656_, v_x_1635_, v_x_1636_);
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
v___y_1650_ = v___x_1662_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1664_; 
lean_dec(v_val_1656_);
lean_dec(v_key_1655_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 1, v_x_1636_);
lean_ctor_set(v___x_1658_, 0, v_x_1635_);
v___x_1664_ = v___x_1658_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_x_1635_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_x_1636_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
v___y_1650_ = v___x_1664_;
goto v___jp_1649_;
}
}
}
}
case 1:
{
lean_object* v_node_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1679_; 
v_node_1667_ = lean_ctor_get(v_v_1646_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_v_1646_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1669_ = v_v_1646_;
v_isShared_1670_ = v_isSharedCheck_1679_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_node_1667_);
lean_dec(v_v_1646_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1679_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
size_t v___x_1671_; size_t v___x_1672_; size_t v___x_1673_; size_t v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1671_ = ((size_t)5ULL);
v___x_1672_ = lean_usize_shift_right(v_x_1633_, v___x_1671_);
v___x_1673_ = ((size_t)1ULL);
v___x_1674_ = lean_usize_add(v_x_1634_, v___x_1673_);
v___x_1675_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_node_1667_, v___x_1672_, v___x_1674_, v_x_1635_, v_x_1636_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___x_1675_);
v___x_1677_ = v___x_1669_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
v___y_1650_ = v___x_1677_;
goto v___jp_1649_;
}
}
}
default: 
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v_x_1635_);
lean_ctor_set(v___x_1680_, 1, v_x_1636_);
v___y_1650_ = v___x_1680_;
goto v___jp_1649_;
}
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_array_fset(v_xs_x27_1648_, v_j_1640_, v___y_1650_);
lean_dec(v_j_1640_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1651_);
v___x_1653_ = v___x_1644_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
else
{
lean_object* v_ks_1683_; lean_object* v_vs_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1702_; 
v_ks_1683_ = lean_ctor_get(v_x_1632_, 0);
v_vs_1684_ = lean_ctor_get(v_x_1632_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_x_1632_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1686_ = v_x_1632_;
v_isShared_1687_ = v_isSharedCheck_1702_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_vs_1684_);
lean_inc(v_ks_1683_);
lean_dec(v_x_1632_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1702_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_ks_1683_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_vs_1684_);
v___x_1689_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v_newNode_1690_; size_t v___x_1691_; uint8_t v___x_1692_; 
v_newNode_1690_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v___x_1689_, v_x_1635_, v_x_1636_);
v___x_1691_ = ((size_t)7ULL);
v___x_1692_ = lean_usize_dec_le(v___x_1691_, v_x_1634_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1690_);
v___x_1694_ = lean_unsigned_to_nat(4u);
v___x_1695_ = lean_nat_dec_lt(v___x_1693_, v___x_1694_);
lean_dec(v___x_1693_);
if (v___x_1695_ == 0)
{
lean_object* v_ks_1696_; lean_object* v_vs_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_ks_1696_ = lean_ctor_get(v_newNode_1690_, 0);
lean_inc_ref(v_ks_1696_);
v_vs_1697_ = lean_ctor_get(v_newNode_1690_, 1);
lean_inc_ref(v_vs_1697_);
lean_dec_ref(v_newNode_1690_);
v___x_1698_ = lean_unsigned_to_nat(0u);
v___x_1699_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_1700_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_1634_, v_ks_1696_, v_vs_1697_, v___x_1698_, v___x_1699_);
lean_dec_ref(v_vs_1697_);
lean_dec_ref(v_ks_1696_);
return v___x_1700_;
}
else
{
return v_newNode_1690_;
}
}
else
{
return v_newNode_1690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_1703_, lean_object* v_keys_1704_, lean_object* v_vals_1705_, lean_object* v_i_1706_, lean_object* v_entries_1707_){
_start:
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_array_get_size(v_keys_1704_);
v___x_1709_ = lean_nat_dec_lt(v_i_1706_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_dec(v_i_1706_);
return v_entries_1707_;
}
else
{
lean_object* v_k_1710_; lean_object* v_v_1711_; uint64_t v___x_1712_; size_t v_h_1713_; size_t v___x_1714_; lean_object* v___x_1715_; size_t v___x_1716_; size_t v___x_1717_; size_t v___x_1718_; size_t v_h_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_k_1710_ = lean_array_fget_borrowed(v_keys_1704_, v_i_1706_);
v_v_1711_ = lean_array_fget_borrowed(v_vals_1705_, v_i_1706_);
v___x_1712_ = l_Lean_instHashableMVarId_hash(v_k_1710_);
v_h_1713_ = lean_uint64_to_usize(v___x_1712_);
v___x_1714_ = ((size_t)5ULL);
v___x_1715_ = lean_unsigned_to_nat(1u);
v___x_1716_ = ((size_t)1ULL);
v___x_1717_ = lean_usize_sub(v_depth_1703_, v___x_1716_);
v___x_1718_ = lean_usize_mul(v___x_1714_, v___x_1717_);
v_h_1719_ = lean_usize_shift_right(v_h_1713_, v___x_1718_);
v___x_1720_ = lean_nat_add(v_i_1706_, v___x_1715_);
lean_dec(v_i_1706_);
lean_inc(v_v_1711_);
lean_inc(v_k_1710_);
v___x_1721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_entries_1707_, v_h_1719_, v_depth_1703_, v_k_1710_, v_v_1711_);
v_i_1706_ = v___x_1720_;
v_entries_1707_ = v___x_1721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_1723_, lean_object* v_keys_1724_, lean_object* v_vals_1725_, lean_object* v_i_1726_, lean_object* v_entries_1727_){
_start:
{
size_t v_depth_boxed_1728_; lean_object* v_res_1729_; 
v_depth_boxed_1728_ = lean_unbox_usize(v_depth_1723_);
lean_dec(v_depth_1723_);
v_res_1729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_1728_, v_keys_1724_, v_vals_1725_, v_i_1726_, v_entries_1727_);
lean_dec_ref(v_vals_1725_);
lean_dec_ref(v_keys_1724_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_){
_start:
{
size_t v_x_2102__boxed_1735_; size_t v_x_2103__boxed_1736_; lean_object* v_res_1737_; 
v_x_2102__boxed_1735_ = lean_unbox_usize(v_x_1731_);
lean_dec(v_x_1731_);
v_x_2103__boxed_1736_ = lean_unbox_usize(v_x_1732_);
lean_dec(v_x_1732_);
v_res_1737_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1730_, v_x_2102__boxed_1735_, v_x_2103__boxed_1736_, v_x_1733_, v_x_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(lean_object* v_x_1738_, lean_object* v_x_1739_, lean_object* v_x_1740_){
_start:
{
uint64_t v___x_1741_; size_t v___x_1742_; size_t v___x_1743_; lean_object* v___x_1744_; 
v___x_1741_ = l_Lean_instHashableMVarId_hash(v_x_1739_);
v___x_1742_ = lean_uint64_to_usize(v___x_1741_);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1738_, v___x_1742_, v___x_1743_, v_x_1739_, v_x_1740_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(lean_object* v_mvarId_1745_, lean_object* v_val_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1749_; lean_object* v_mctx_1750_; lean_object* v_cache_1751_; lean_object* v_zetaDeltaFVarIds_1752_; lean_object* v_postponed_1753_; lean_object* v_diag_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1783_; 
v___x_1749_ = lean_st_ref_take(v___y_1747_);
v_mctx_1750_ = lean_ctor_get(v___x_1749_, 0);
v_cache_1751_ = lean_ctor_get(v___x_1749_, 1);
v_zetaDeltaFVarIds_1752_ = lean_ctor_get(v___x_1749_, 2);
v_postponed_1753_ = lean_ctor_get(v___x_1749_, 3);
v_diag_1754_ = lean_ctor_get(v___x_1749_, 4);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1756_ = v___x_1749_;
v_isShared_1757_ = v_isSharedCheck_1783_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_diag_1754_);
lean_inc(v_postponed_1753_);
lean_inc(v_zetaDeltaFVarIds_1752_);
lean_inc(v_cache_1751_);
lean_inc(v_mctx_1750_);
lean_dec(v___x_1749_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1783_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_depth_1758_; lean_object* v_levelAssignDepth_1759_; lean_object* v_lmvarCounter_1760_; lean_object* v_mvarCounter_1761_; lean_object* v_lDecls_1762_; lean_object* v_decls_1763_; lean_object* v_userNames_1764_; lean_object* v_lAssignment_1765_; lean_object* v_eAssignment_1766_; lean_object* v_dAssignment_1767_; lean_object* v_instanceTypedMVars_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1782_; 
v_depth_1758_ = lean_ctor_get(v_mctx_1750_, 0);
v_levelAssignDepth_1759_ = lean_ctor_get(v_mctx_1750_, 1);
v_lmvarCounter_1760_ = lean_ctor_get(v_mctx_1750_, 2);
v_mvarCounter_1761_ = lean_ctor_get(v_mctx_1750_, 3);
v_lDecls_1762_ = lean_ctor_get(v_mctx_1750_, 4);
v_decls_1763_ = lean_ctor_get(v_mctx_1750_, 5);
v_userNames_1764_ = lean_ctor_get(v_mctx_1750_, 6);
v_lAssignment_1765_ = lean_ctor_get(v_mctx_1750_, 7);
v_eAssignment_1766_ = lean_ctor_get(v_mctx_1750_, 8);
v_dAssignment_1767_ = lean_ctor_get(v_mctx_1750_, 9);
v_instanceTypedMVars_1768_ = lean_ctor_get(v_mctx_1750_, 10);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_mctx_1750_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1770_ = v_mctx_1750_;
v_isShared_1771_ = v_isSharedCheck_1782_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_instanceTypedMVars_1768_);
lean_inc(v_dAssignment_1767_);
lean_inc(v_eAssignment_1766_);
lean_inc(v_lAssignment_1765_);
lean_inc(v_userNames_1764_);
lean_inc(v_decls_1763_);
lean_inc(v_lDecls_1762_);
lean_inc(v_mvarCounter_1761_);
lean_inc(v_lmvarCounter_1760_);
lean_inc(v_levelAssignDepth_1759_);
lean_inc(v_depth_1758_);
lean_dec(v_mctx_1750_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1782_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1772_ = lean_box(0);
v___x_1773_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_1766_, v_mvarId_1745_, v_val_1746_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 8, v___x_1773_);
v___x_1775_ = v___x_1770_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_depth_1758_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_levelAssignDepth_1759_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_lmvarCounter_1760_);
lean_ctor_set(v_reuseFailAlloc_1781_, 3, v_mvarCounter_1761_);
lean_ctor_set(v_reuseFailAlloc_1781_, 4, v_lDecls_1762_);
lean_ctor_set(v_reuseFailAlloc_1781_, 5, v_decls_1763_);
lean_ctor_set(v_reuseFailAlloc_1781_, 6, v_userNames_1764_);
lean_ctor_set(v_reuseFailAlloc_1781_, 7, v_lAssignment_1765_);
lean_ctor_set(v_reuseFailAlloc_1781_, 8, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1781_, 9, v_dAssignment_1767_);
lean_ctor_set(v_reuseFailAlloc_1781_, 10, v_instanceTypedMVars_1768_);
v___x_1775_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1775_);
v___x_1777_ = v___x_1756_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_cache_1751_);
lean_ctor_set(v_reuseFailAlloc_1780_, 2, v_zetaDeltaFVarIds_1752_);
lean_ctor_set(v_reuseFailAlloc_1780_, 3, v_postponed_1753_);
lean_ctor_set(v_reuseFailAlloc_1780_, 4, v_diag_1754_);
v___x_1777_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_st_ref_put(v___y_1747_, v___x_1777_);
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1772_);
return v___x_1779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object* v_mvarId_1784_, lean_object* v_val_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1784_, v_val_1785_, v___y_1786_);
lean_dec(v___y_1786_);
return v_res_1788_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1791_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1792_ = lean_unsigned_to_nat(41u);
v___x_1793_ = lean_unsigned_to_nat(113u);
v___x_1794_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_1795_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1796_ = l_mkPanicMessageWithDecl(v___x_1795_, v___x_1794_, v___x_1793_, v___x_1792_, v___x_1791_);
return v___x_1796_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1797_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1798_ = lean_unsigned_to_nat(51u);
v___x_1799_ = lean_unsigned_to_nat(115u);
v___x_1800_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_1801_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1802_ = l_mkPanicMessageWithDecl(v___x_1801_, v___x_1800_, v___x_1799_, v___x_1798_, v___x_1797_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object* v_mvarId_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
lean_inc(v_mvarId_1803_);
v___x_1809_ = l_Lean_MVarId_getType_x27(v_mvarId_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_1812_ = lean_unsigned_to_nat(3u);
v___x_1813_ = l_Lean_Expr_isAppOfArity(v_a_1810_, v___x_1811_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec(v_a_1810_);
lean_dec(v_mvarId_1803_);
v___x_1814_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2);
v___x_1815_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_1814_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1816_ = l_Lean_Expr_appFn_x21(v_a_1810_);
v___x_1817_ = l_Lean_Expr_appArg_x21(v___x_1816_);
lean_dec_ref(v___x_1816_);
v___x_1818_ = l_Lean_Expr_appArg_x21(v_a_1810_);
lean_dec(v_a_1810_);
v___x_1819_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1817_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1821_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc_n(v_a_1820_, 2);
lean_dec_ref_known(v___x_1819_, 1);
lean_inc(v___y_1807_);
lean_inc_ref(v___y_1806_);
lean_inc(v___y_1805_);
lean_inc_ref(v___y_1804_);
v___x_1821_ = lean_infer_type(v_a_1820_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; uint8_t v___x_1823_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1821_, 1);
v___x_1823_ = l_Lean_Expr_isAppOfArity(v_a_1822_, v___x_1811_, v___x_1812_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v_a_1822_);
lean_dec(v_a_1820_);
lean_dec_ref(v___x_1818_);
lean_dec(v_mvarId_1803_);
v___x_1824_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
v___x_1825_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_1824_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = l_Lean_Expr_appArg_x21(v_a_1822_);
lean_dec(v_a_1822_);
v___x_1827_ = l_Lean_Meta_mkEq(v___x_1826_, v___x_1818_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1829_ = lean_box(0);
v___x_1830_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1828_, v___x_1829_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc_n(v_a_1831_, 2);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = l_Lean_Meta_mkEqTrans(v_a_1820_, v_a_1831_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v___y_1804_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1842_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
v___x_1834_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1803_, v_a_1833_, v___y_1805_);
lean_dec(v___y_1805_);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v___x_1834_, 0);
lean_dec(v_unused_1843_);
v___x_1836_ = v___x_1834_;
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
else
{
lean_dec(v___x_1834_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = l_Lean_Expr_mvarId_x21(v_a_1831_);
lean_dec(v_a_1831_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_a_1831_);
lean_dec(v___y_1805_);
lean_dec(v_mvarId_1803_);
v_a_1844_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1832_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1832_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_a_1820_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_mvarId_1803_);
v_a_1852_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1830_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1830_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_a_1820_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_mvarId_1803_);
v_a_1860_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1827_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1827_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec(v_a_1820_);
lean_dec_ref(v___x_1818_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_mvarId_1803_);
v_a_1868_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1821_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1821_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v___x_1818_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_mvarId_1803_);
v_a_1876_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1819_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1819_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_mvarId_1803_);
v_a_1884_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1809_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1809_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object* v_mvarId_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object* v_mvarId_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___f_1905_; lean_object* v___x_1906_; 
lean_inc(v_mvarId_1899_);
v___f_1905_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1905_, 0, v_mvarId_1899_);
v___x_1906_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1899_, v___f_1905_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object* v_mvarId_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object* v_mvarId_1914_, lean_object* v_val_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1914_, v_val_1915_, v___y_1917_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object* v_mvarId_1922_, lean_object* v_val_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_1922_, v_val_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object* v_00_u03b2_1930_, lean_object* v_x_1931_, lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_1931_, v_x_1932_, v_x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1935_, lean_object* v_x_1936_, size_t v_x_1937_, size_t v_x_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1936_, v_x_1937_, v_x_1938_, v_x_1939_, v_x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_, lean_object* v_x_1947_){
_start:
{
size_t v_x_2576__boxed_1948_; size_t v_x_2577__boxed_1949_; lean_object* v_res_1950_; 
v_x_2576__boxed_1948_ = lean_unbox_usize(v_x_1944_);
lean_dec(v_x_1944_);
v_x_2577__boxed_1949_ = lean_unbox_usize(v_x_1945_);
lean_dec(v_x_1945_);
v_res_1950_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_1942_, v_x_1943_, v_x_2576__boxed_1948_, v_x_2577__boxed_1949_, v_x_1946_, v_x_1947_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1951_, lean_object* v_n_1952_, lean_object* v_k_1953_, lean_object* v_v_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1952_, v_k_1953_, v_v_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1956_, size_t v_depth_1957_, lean_object* v_keys_1958_, lean_object* v_vals_1959_, lean_object* v_heq_1960_, lean_object* v_i_1961_, lean_object* v_entries_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1957_, v_keys_1958_, v_vals_1959_, v_i_1961_, v_entries_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1964_, lean_object* v_depth_1965_, lean_object* v_keys_1966_, lean_object* v_vals_1967_, lean_object* v_heq_1968_, lean_object* v_i_1969_, lean_object* v_entries_1970_){
_start:
{
size_t v_depth_boxed_1971_; lean_object* v_res_1972_; 
v_depth_boxed_1971_ = lean_unbox_usize(v_depth_1965_);
lean_dec(v_depth_1965_);
v_res_1972_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1964_, v_depth_boxed_1971_, v_keys_1966_, v_vals_1967_, v_heq_1968_, v_i_1969_, v_entries_1970_);
lean_dec_ref(v_vals_1967_);
lean_dec_ref(v_keys_1966_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1974_, v_x_1975_, v_x_1976_, v_x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0(lean_object* v_declNameNonRec_1979_, lean_object* v_numFixed_1980_, lean_object* v_x_1981_){
_start:
{
uint8_t v___x_1982_; 
v___x_1982_ = l_Lean_Expr_isAppOfArity(v_x_1981_, v_declNameNonRec_1979_, v_numFixed_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0___boxed(lean_object* v_declNameNonRec_1983_, lean_object* v_numFixed_1984_, lean_object* v_x_1985_){
_start:
{
uint8_t v_res_1986_; lean_object* v_r_1987_; 
v_res_1986_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0(v_declNameNonRec_1983_, v_numFixed_1984_, v_x_1985_);
lean_dec_ref(v_x_1985_);
lean_dec(v_declNameNonRec_1983_);
v_r_1987_ = lean_box(v_res_1986_);
return v_r_1987_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1989_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1990_ = lean_unsigned_to_nat(41u);
v___x_1991_ = lean_unsigned_to_nat(128u);
v___x_1992_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__0));
v___x_1993_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1994_ = l_mkPanicMessageWithDecl(v___x_1993_, v___x_1992_, v___x_1991_, v___x_1990_, v___x_1989_);
return v___x_1994_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1995_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1996_ = lean_unsigned_to_nat(51u);
v___x_1997_ = lean_unsigned_to_nat(134u);
v___x_1998_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__0));
v___x_1999_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_2000_ = l_mkPanicMessageWithDecl(v___x_1999_, v___x_1998_, v___x_1997_, v___x_1996_, v___x_1995_);
return v___x_2000_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__5));
v___x_2006_ = l_Lean_stringToMessageData(v___x_2005_);
return v___x_2006_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__7));
v___x_2009_ = l_Lean_stringToMessageData(v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1(lean_object* v_mvarId_2010_, lean_object* v___f_2011_, lean_object* v_fixEq_2012_, lean_object* v_declNameNonRec_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___x_2019_; 
lean_inc(v_mvarId_2010_);
v___x_2019_ = l_Lean_MVarId_getType_x27(v_mvarId_2010_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_2022_ = lean_unsigned_to_nat(3u);
v___x_2023_ = l_Lean_Expr_isAppOfArity(v_a_2020_, v___x_2021_, v___x_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec(v_a_2020_);
lean_dec(v_declNameNonRec_2013_);
lean_dec(v_fixEq_2012_);
lean_dec(v_mvarId_2010_);
v___x_2024_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1);
v___x_2025_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_2024_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
return v___x_2025_;
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2026_ = l_Lean_Expr_appFn_x21(v_a_2020_);
v___x_2027_ = l_Lean_Expr_appArg_x21(v___x_2026_);
lean_dec_ref(v___x_2026_);
v___x_2028_ = lean_find_expr(v___f_2011_, v___x_2027_);
if (lean_obj_tag(v___x_2028_) == 1)
{
lean_object* v_val_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_dec(v_declNameNonRec_2013_);
v_val_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_n(v_val_2029_, 2);
lean_dec_ref_known(v___x_2028_, 1);
v___x_2030_ = l_Lean_Expr_appArg_x21(v_a_2020_);
lean_dec(v_a_2020_);
lean_inc(v___y_2017_);
lean_inc_ref(v___y_2016_);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2014_);
v___x_2031_ = lean_infer_type(v_val_2029_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = lean_box(0);
lean_inc(v_val_2029_);
v___x_2034_ = l_Lean_Meta_kabstract(v___x_2027_, v_val_2029_, v___x_2033_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v_dummy_2042_; lean_object* v_nargs_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3));
v___x_2037_ = 0;
v___x_2038_ = l_Lean_mkLambda(v___x_2036_, v___x_2037_, v_a_2032_, v_a_2035_);
v___x_2039_ = l_Lean_Expr_getAppFn(v_val_2029_);
v___x_2040_ = l_Lean_Expr_constLevels_x21(v___x_2039_);
lean_dec_ref(v___x_2039_);
v___x_2041_ = l_Lean_mkConst(v_fixEq_2012_, v___x_2040_);
v_dummy_2042_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_2043_ = l_Lean_Expr_getAppNumArgs(v_val_2029_);
lean_inc(v_nargs_2043_);
v___x_2044_ = lean_mk_array(v_nargs_2043_, v_dummy_2042_);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_sub(v_nargs_2043_, v___x_2045_);
lean_dec(v_nargs_2043_);
v___x_2047_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_2029_, v___x_2044_, v___x_2046_);
v___x_2048_ = l_Lean_mkAppN(v___x_2041_, v___x_2047_);
lean_dec_ref(v___x_2047_);
v___x_2049_ = l_Lean_Meta_mkCongrArg(v___x_2038_, v___x_2048_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc_n(v_a_2050_, 2);
lean_dec_ref_known(v___x_2049_, 1);
lean_inc(v___y_2017_);
lean_inc_ref(v___y_2016_);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2014_);
v___x_2051_ = lean_infer_type(v_a_2050_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; uint8_t v___x_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2053_ = l_Lean_Expr_isAppOfArity(v_a_2052_, v___x_2021_, v___x_2022_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec(v_a_2052_);
lean_dec(v_a_2050_);
lean_dec_ref(v___x_2030_);
lean_dec(v_mvarId_2010_);
v___x_2054_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2);
v___x_2055_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_2054_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = l_Lean_Expr_appArg_x21(v_a_2052_);
lean_dec(v_a_2052_);
v___x_2057_ = l_Lean_Expr_headBeta(v___x_2056_);
v___x_2058_ = l_Lean_Meta_mkEq(v___x_2057_, v___x_2030_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = lean_box(0);
v___x_2061_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2059_, v___x_2060_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_n(v_a_2062_, 2);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = l_Lean_Meta_mkEqTrans(v_a_2050_, v_a_2062_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec_ref(v___y_2014_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2073_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2065_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_2010_, v_a_2064_, v___y_2015_);
lean_dec(v___y_2015_);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v___x_2065_, 0);
lean_dec(v_unused_2074_);
v___x_2067_ = v___x_2065_;
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v___x_2065_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2069_ = l_Lean_Expr_mvarId_x21(v_a_2062_);
lean_dec(v_a_2062_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2069_);
v___x_2071_ = v___x_2067_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_2062_);
lean_dec(v___y_2015_);
lean_dec(v_mvarId_2010_);
v_a_2075_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2063_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2063_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_a_2050_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v_mvarId_2010_);
v_a_2083_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2061_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2061_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v_a_2050_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v_mvarId_2010_);
v_a_2091_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2058_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2058_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
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
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_a_2050_);
lean_dec_ref(v___x_2030_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v_mvarId_2010_);
v_a_2099_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2051_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2051_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v___x_2030_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v_mvarId_2010_);
v_a_2107_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2049_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2049_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec(v_a_2032_);
lean_dec_ref(v___x_2030_);
lean_dec(v_val_2029_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v_fixEq_2012_);
lean_dec(v_mvarId_2010_);
v_a_2115_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2034_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2034_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec_ref(v___x_2030_);
lean_dec(v_val_2029_);
lean_dec_ref(v___x_2027_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v_fixEq_2012_);
lean_dec(v_mvarId_2010_);
v_a_2123_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2031_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2031_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
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
lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec(v___x_2028_);
lean_dec_ref(v___x_2027_);
lean_dec(v_a_2020_);
lean_dec(v_fixEq_2012_);
v___x_2131_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__4));
v___x_2132_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6);
v___x_2133_ = 0;
v___x_2134_ = l_Lean_MessageData_ofConstName(v_declNameNonRec_2013_, v___x_2133_);
v___x_2135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2132_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8);
v___x_2137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2135_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
v___x_2139_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2131_, v_mvarId_2010_, v___x_2138_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
return v___x_2139_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v_declNameNonRec_2013_);
lean_dec(v_fixEq_2012_);
lean_dec(v_mvarId_2010_);
v_a_2140_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2019_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2019_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___boxed(lean_object* v_mvarId_2148_, lean_object* v___f_2149_, lean_object* v_fixEq_2150_, lean_object* v_declNameNonRec_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1(v_mvarId_2148_, v___f_2149_, v_fixEq_2150_, v_declNameNonRec_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec_ref(v___f_2149_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(lean_object* v_declNameNonRec_2158_, lean_object* v_fixEq_2159_, lean_object* v_numFixed_2160_, lean_object* v_mvarId_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___f_2167_; lean_object* v___f_2168_; lean_object* v___x_2169_; 
lean_inc(v_declNameNonRec_2158_);
v___f_2167_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2167_, 0, v_declNameNonRec_2158_);
lean_closure_set(v___f_2167_, 1, v_numFixed_2160_);
lean_inc(v_mvarId_2161_);
v___f_2168_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___boxed), 9, 4);
lean_closure_set(v___f_2168_, 0, v_mvarId_2161_);
lean_closure_set(v___f_2168_, 1, v___f_2167_);
lean_closure_set(v___f_2168_, 2, v_fixEq_2159_);
lean_closure_set(v___f_2168_, 3, v_declNameNonRec_2158_);
v___x_2169_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_2161_, v___f_2168_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___boxed(lean_object* v_declNameNonRec_2170_, lean_object* v_fixEq_2171_, lean_object* v_numFixed_2172_, lean_object* v_mvarId_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(v_declNameNonRec_2170_, v_fixEq_2171_, v_numFixed_2172_, v_mvarId_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(lean_object* v_e_2180_, lean_object* v___y_2181_){
_start:
{
uint8_t v___x_2183_; 
v___x_2183_ = l_Lean_Expr_hasMVar(v_e_2180_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v_e_2180_);
return v___x_2184_;
}
else
{
lean_object* v___x_2185_; lean_object* v_mctx_2186_; lean_object* v___x_2187_; lean_object* v_fst_2188_; lean_object* v_snd_2189_; lean_object* v___x_2190_; lean_object* v_cache_2191_; lean_object* v_zetaDeltaFVarIds_2192_; lean_object* v_postponed_2193_; lean_object* v_diag_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2203_; 
v___x_2185_ = lean_st_ref_get(v___y_2181_);
v_mctx_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc_ref(v_mctx_2186_);
lean_dec(v___x_2185_);
v___x_2187_ = l_Lean_instantiateMVarsCore(v_mctx_2186_, v_e_2180_);
v_fst_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_fst_2188_);
v_snd_2189_ = lean_ctor_get(v___x_2187_, 1);
lean_inc(v_snd_2189_);
lean_dec_ref(v___x_2187_);
v___x_2190_ = lean_st_ref_take(v___y_2181_);
v_cache_2191_ = lean_ctor_get(v___x_2190_, 1);
v_zetaDeltaFVarIds_2192_ = lean_ctor_get(v___x_2190_, 2);
v_postponed_2193_ = lean_ctor_get(v___x_2190_, 3);
v_diag_2194_ = lean_ctor_get(v___x_2190_, 4);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; 
v_unused_2204_ = lean_ctor_get(v___x_2190_, 0);
lean_dec(v_unused_2204_);
v___x_2196_ = v___x_2190_;
v_isShared_2197_ = v_isSharedCheck_2203_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_diag_2194_);
lean_inc(v_postponed_2193_);
lean_inc(v_zetaDeltaFVarIds_2192_);
lean_inc(v_cache_2191_);
lean_dec(v___x_2190_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2203_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v_snd_2189_);
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_snd_2189_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_cache_2191_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_zetaDeltaFVarIds_2192_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_postponed_2193_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v_diag_2194_);
v___x_2199_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_st_ref_put(v___y_2181_, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v_fst_2188_);
return v___x_2201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg___boxed(lean_object* v_e_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_e_2205_, v___y_2206_);
lean_dec(v___y_2206_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object* v_e_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_e_2209_, v___y_2211_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___boxed(lean_object* v_e_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_e_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_2223_, lean_object* v_opt_2224_){
_start:
{
lean_object* v_name_2225_; lean_object* v_defValue_2226_; lean_object* v_map_2227_; lean_object* v___x_2228_; 
v_name_2225_ = lean_ctor_get(v_opt_2224_, 0);
v_defValue_2226_ = lean_ctor_get(v_opt_2224_, 1);
v_map_2227_ = lean_ctor_get(v_opts_2223_, 0);
v___x_2228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2227_, v_name_2225_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_inc(v_defValue_2226_);
return v_defValue_2226_;
}
else
{
lean_object* v_val_2229_; 
v_val_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v___x_2228_, 1);
if (lean_obj_tag(v_val_2229_) == 3)
{
lean_object* v_v_2230_; 
v_v_2230_ = lean_ctor_get(v_val_2229_, 0);
lean_inc(v_v_2230_);
lean_dec_ref_known(v_val_2229_, 1);
return v_v_2230_;
}
else
{
lean_dec(v_val_2229_);
lean_inc(v_defValue_2226_);
return v_defValue_2226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_2231_, lean_object* v_opt_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_2231_, v_opt_2232_);
lean_dec_ref(v_opt_2232_);
lean_dec_ref(v_opts_2231_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(lean_object* v_k_2234_, uint8_t v_allowLevelAssignments_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2235_, v_k_2234_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
v_a_2250_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2241_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2241_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg___boxed(lean_object* v_k_2258_, lean_object* v_allowLevelAssignments_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2265_; lean_object* v_res_2266_; 
v_allowLevelAssignments_boxed_2265_ = lean_unbox(v_allowLevelAssignments_2259_);
v_res_2266_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_k_2258_, v_allowLevelAssignments_boxed_2265_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object* v_00_u03b1_2267_, lean_object* v_k_2268_, uint8_t v_allowLevelAssignments_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_k_2268_, v_allowLevelAssignments_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object* v_00_u03b1_2276_, lean_object* v_k_2277_, lean_object* v_allowLevelAssignments_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2284_; lean_object* v_res_2285_; 
v_allowLevelAssignments_boxed_2284_ = lean_unbox(v_allowLevelAssignments_2278_);
v_res_2285_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v_00_u03b1_2276_, v_k_2277_, v_allowLevelAssignments_boxed_2284_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object* v___x_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_toCold_2295_; lean_object* v_options_2296_; uint8_t v_hasTrace_2297_; 
v_toCold_2295_ = lean_ctor_get(v___y_2292_, 0);
v_options_2296_ = lean_ctor_get(v_toCold_2295_, 2);
v_hasTrace_2297_ = lean_ctor_get_uint8(v_options_2296_, sizeof(void*)*1);
if (v_hasTrace_2297_ == 0)
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_dec(v___x_2289_);
v___x_2298_ = lean_box(v_hasTrace_2297_);
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
return v___x_2299_;
}
else
{
lean_object* v_inheritedTraceOptions_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_inheritedTraceOptions_2300_ = lean_ctor_get(v_toCold_2295_, 11);
v___x_2301_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_2302_ = l_Lean_Name_append(v___x_2301_, v___x_2289_);
v___x_2303_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2300_, v_options_2296_, v___x_2302_);
lean_dec(v___x_2302_);
v___x_2304_ = lean_box(v___x_2303_);
v___x_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v___x_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(lean_object* v_o_2313_, lean_object* v_k_2314_, uint8_t v_v_2315_){
_start:
{
lean_object* v_map_2316_; uint8_t v_hasTrace_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2331_; 
v_map_2316_ = lean_ctor_get(v_o_2313_, 0);
v_hasTrace_2317_ = lean_ctor_get_uint8(v_o_2313_, sizeof(void*)*1);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_o_2313_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2319_ = v_o_2313_;
v_isShared_2320_ = v_isSharedCheck_2331_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_map_2316_);
lean_dec(v_o_2313_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2331_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2321_, 0, v_v_2315_);
lean_inc(v_k_2314_);
v___x_2322_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2314_, v___x_2321_, v_map_2316_);
if (v_hasTrace_2317_ == 0)
{
lean_object* v___x_2323_; uint8_t v___x_2324_; lean_object* v___x_2326_; 
v___x_2323_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_2324_ = l_Lean_Name_isPrefixOf(v___x_2323_, v_k_2314_);
lean_dec(v_k_2314_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2322_);
v___x_2326_ = v___x_2319_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2322_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*1, v___x_2324_);
return v___x_2326_;
}
}
else
{
lean_object* v___x_2329_; 
lean_dec(v_k_2314_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2322_);
v___x_2329_ = v___x_2319_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2322_);
lean_ctor_set_uint8(v_reuseFailAlloc_2330_, sizeof(void*)*1, v_hasTrace_2317_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3___boxed(lean_object* v_o_2332_, lean_object* v_k_2333_, lean_object* v_v_2334_){
_start:
{
uint8_t v_v_boxed_2335_; lean_object* v_res_2336_; 
v_v_boxed_2335_ = lean_unbox(v_v_2334_);
v_res_2336_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(v_o_2332_, v_k_2333_, v_v_boxed_2335_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_2337_, lean_object* v_opt_2338_, uint8_t v_val_2339_){
_start:
{
lean_object* v_name_2340_; lean_object* v___x_2341_; 
v_name_2340_ = lean_ctor_get(v_opt_2338_, 0);
lean_inc(v_name_2340_);
lean_dec_ref(v_opt_2338_);
v___x_2341_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(v_opts_2337_, v_name_2340_, v_val_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_2342_, lean_object* v_opt_2343_, lean_object* v_val_2344_){
_start:
{
uint8_t v_val_boxed_2345_; lean_object* v_res_2346_; 
v_val_boxed_2345_ = lean_unbox(v_val_2344_);
v_res_2346_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_2342_, v_opt_2343_, v_val_boxed_2345_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object* v_mvarId_2347_, uint8_t v___x_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___y_2355_; uint16_t v___y_2356_; lean_object* v_fileName_2357_; lean_object* v_fileMap_2358_; lean_object* v_currNamespace_2359_; lean_object* v_openDecls_2360_; lean_object* v_initHeartbeats_2361_; lean_object* v_maxHeartbeats_2362_; lean_object* v_quotContext_2363_; lean_object* v_currMacroScope_2364_; lean_object* v_cancelTk_x3f_2365_; lean_object* v_inheritedTraceOptions_2366_; lean_object* v_currRecDepth_2367_; lean_object* v_ref_2368_; uint8_t v_suppressElabErrors_2369_; uint8_t v_checkDeprecated_2370_; uint8_t v_isRecordingDeps_2371_; lean_object* v___y_2372_; lean_object* v_toCold_2378_; lean_object* v_currRecDepth_2379_; lean_object* v_ref_2380_; uint8_t v_suppressElabErrors_2381_; uint8_t v_checkDeprecated_2382_; uint8_t v_isRecordingDeps_2383_; lean_object* v_fileName_2384_; lean_object* v_fileMap_2385_; lean_object* v_options_2386_; lean_object* v_currNamespace_2387_; lean_object* v_openDecls_2388_; lean_object* v_initHeartbeats_2389_; lean_object* v_maxHeartbeats_2390_; lean_object* v_quotContext_2391_; lean_object* v_currMacroScope_2392_; lean_object* v_cancelTk_x3f_2393_; lean_object* v_inheritedTraceOptions_2394_; lean_object* v___y_2396_; uint16_t v___y_2397_; uint8_t v___y_2398_; lean_object* v___y_2421_; 
v_toCold_2378_ = lean_ctor_get(v___y_2351_, 0);
v_currRecDepth_2379_ = lean_ctor_get(v___y_2351_, 1);
v_ref_2380_ = lean_ctor_get(v___y_2351_, 2);
v_suppressElabErrors_2381_ = lean_ctor_get_uint8(v___y_2351_, sizeof(void*)*3 + 2);
v_checkDeprecated_2382_ = lean_ctor_get_uint8(v___y_2351_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2383_ = lean_ctor_get_uint8(v___y_2351_, sizeof(void*)*3 + 4);
v_fileName_2384_ = lean_ctor_get(v_toCold_2378_, 0);
v_fileMap_2385_ = lean_ctor_get(v_toCold_2378_, 1);
v_options_2386_ = lean_ctor_get(v_toCold_2378_, 2);
v_currNamespace_2387_ = lean_ctor_get(v_toCold_2378_, 4);
v_openDecls_2388_ = lean_ctor_get(v_toCold_2378_, 5);
v_initHeartbeats_2389_ = lean_ctor_get(v_toCold_2378_, 6);
v_maxHeartbeats_2390_ = lean_ctor_get(v_toCold_2378_, 7);
v_quotContext_2391_ = lean_ctor_get(v_toCold_2378_, 8);
v_currMacroScope_2392_ = lean_ctor_get(v_toCold_2378_, 9);
v_cancelTk_x3f_2393_ = lean_ctor_get(v_toCold_2378_, 10);
v_inheritedTraceOptions_2394_ = lean_ctor_get(v_toCold_2378_, 11);
if (v_isRecordingDeps_2383_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = l_Lean_Meta_smartUnfolding;
lean_inc_ref(v_options_2386_);
v___x_2432_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_options_2386_, v___x_2431_, v_isRecordingDeps_2383_);
v___y_2421_ = v___x_2432_;
goto v___jp_2420_;
}
else
{
lean_object* v___x_2433_; 
lean_inc_ref(v_options_2386_);
v___x_2433_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2386_);
v___y_2421_ = v___x_2433_;
goto v___jp_2420_;
}
v___jp_2354_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2373_ = l_Lean_maxRecDepth;
v___x_2374_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___y_2355_, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2375_, 0, v_fileName_2357_);
lean_ctor_set(v___x_2375_, 1, v_fileMap_2358_);
lean_ctor_set(v___x_2375_, 2, v___y_2355_);
lean_ctor_set(v___x_2375_, 3, v___x_2374_);
lean_ctor_set(v___x_2375_, 4, v_currNamespace_2359_);
lean_ctor_set(v___x_2375_, 5, v_openDecls_2360_);
lean_ctor_set(v___x_2375_, 6, v_initHeartbeats_2361_);
lean_ctor_set(v___x_2375_, 7, v_maxHeartbeats_2362_);
lean_ctor_set(v___x_2375_, 8, v_quotContext_2363_);
lean_ctor_set(v___x_2375_, 9, v_currMacroScope_2364_);
lean_ctor_set(v___x_2375_, 10, v_cancelTk_x3f_2365_);
lean_ctor_set(v___x_2375_, 11, v_inheritedTraceOptions_2366_);
lean_inc(v_ref_2368_);
lean_inc(v_currRecDepth_2367_);
v___x_2376_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set(v___x_2376_, 1, v_currRecDepth_2367_);
lean_ctor_set(v___x_2376_, 2, v_ref_2368_);
lean_ctor_set_uint16(v___x_2376_, sizeof(void*)*3, v___y_2356_);
lean_ctor_set_uint8(v___x_2376_, sizeof(void*)*3 + 2, v_suppressElabErrors_2369_);
lean_ctor_set_uint8(v___x_2376_, sizeof(void*)*3 + 3, v_checkDeprecated_2370_);
lean_ctor_set_uint8(v___x_2376_, sizeof(void*)*3 + 4, v_isRecordingDeps_2371_);
v___x_2377_ = l_Lean_MVarId_refl(v_mvarId_2347_, v___x_2348_, v___y_2349_, v___y_2350_, v___x_2376_, v___y_2372_);
lean_dec_ref_known(v___x_2376_, 3);
return v___x_2377_;
}
v___jp_2395_:
{
lean_object* v___x_2399_; lean_object* v_env_2400_; lean_object* v_nextMacroScope_2401_; lean_object* v_ngen_2402_; lean_object* v_auxDeclNGen_2403_; lean_object* v_traceState_2404_; lean_object* v_recordedDeps_2405_; lean_object* v_messages_2406_; lean_object* v_infoState_2407_; lean_object* v_snapshotTasks_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2418_; 
v___x_2399_ = lean_st_ref_take(v___y_2352_);
v_env_2400_ = lean_ctor_get(v___x_2399_, 0);
v_nextMacroScope_2401_ = lean_ctor_get(v___x_2399_, 1);
v_ngen_2402_ = lean_ctor_get(v___x_2399_, 2);
v_auxDeclNGen_2403_ = lean_ctor_get(v___x_2399_, 3);
v_traceState_2404_ = lean_ctor_get(v___x_2399_, 4);
v_recordedDeps_2405_ = lean_ctor_get(v___x_2399_, 6);
v_messages_2406_ = lean_ctor_get(v___x_2399_, 7);
v_infoState_2407_ = lean_ctor_get(v___x_2399_, 8);
v_snapshotTasks_2408_ = lean_ctor_get(v___x_2399_, 9);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2418_ == 0)
{
lean_object* v_unused_2419_; 
v_unused_2419_ = lean_ctor_get(v___x_2399_, 5);
lean_dec(v_unused_2419_);
v___x_2410_ = v___x_2399_;
v_isShared_2411_ = v_isSharedCheck_2418_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_snapshotTasks_2408_);
lean_inc(v_infoState_2407_);
lean_inc(v_messages_2406_);
lean_inc(v_recordedDeps_2405_);
lean_inc(v_traceState_2404_);
lean_inc(v_auxDeclNGen_2403_);
lean_inc(v_ngen_2402_);
lean_inc(v_nextMacroScope_2401_);
lean_inc(v_env_2400_);
lean_dec(v___x_2399_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2418_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2412_ = l_Lean_Kernel_enableDiag(v_env_2400_, v___y_2398_);
v___x_2413_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 5, v___x_2413_);
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2415_ = v___x_2410_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_nextMacroScope_2401_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v_ngen_2402_);
lean_ctor_set(v_reuseFailAlloc_2417_, 3, v_auxDeclNGen_2403_);
lean_ctor_set(v_reuseFailAlloc_2417_, 4, v_traceState_2404_);
lean_ctor_set(v_reuseFailAlloc_2417_, 5, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2417_, 6, v_recordedDeps_2405_);
lean_ctor_set(v_reuseFailAlloc_2417_, 7, v_messages_2406_);
lean_ctor_set(v_reuseFailAlloc_2417_, 8, v_infoState_2407_);
lean_ctor_set(v_reuseFailAlloc_2417_, 9, v_snapshotTasks_2408_);
v___x_2415_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_st_ref_put(v___y_2352_, v___x_2415_);
lean_inc_ref(v_inheritedTraceOptions_2394_);
lean_inc(v_cancelTk_x3f_2393_);
lean_inc(v_currMacroScope_2392_);
lean_inc(v_quotContext_2391_);
lean_inc(v_maxHeartbeats_2390_);
lean_inc(v_initHeartbeats_2389_);
lean_inc(v_openDecls_2388_);
lean_inc(v_currNamespace_2387_);
lean_inc_ref(v_fileMap_2385_);
lean_inc_ref(v_fileName_2384_);
v___y_2355_ = v___y_2396_;
v___y_2356_ = v___y_2397_;
v_fileName_2357_ = v_fileName_2384_;
v_fileMap_2358_ = v_fileMap_2385_;
v_currNamespace_2359_ = v_currNamespace_2387_;
v_openDecls_2360_ = v_openDecls_2388_;
v_initHeartbeats_2361_ = v_initHeartbeats_2389_;
v_maxHeartbeats_2362_ = v_maxHeartbeats_2390_;
v_quotContext_2363_ = v_quotContext_2391_;
v_currMacroScope_2364_ = v_currMacroScope_2392_;
v_cancelTk_x3f_2365_ = v_cancelTk_x3f_2393_;
v_inheritedTraceOptions_2366_ = v_inheritedTraceOptions_2394_;
v_currRecDepth_2367_ = v_currRecDepth_2379_;
v_ref_2368_ = v_ref_2380_;
v_suppressElabErrors_2369_ = v_suppressElabErrors_2381_;
v_checkDeprecated_2370_ = v_checkDeprecated_2382_;
v_isRecordingDeps_2371_ = v_isRecordingDeps_2383_;
v___y_2372_ = v___y_2352_;
goto v___jp_2354_;
}
}
}
v___jp_2420_:
{
uint16_t v___x_2422_; lean_object* v___x_2423_; lean_object* v_env_2424_; uint8_t v___x_2425_; uint16_t v___x_2426_; uint16_t v___x_2427_; uint16_t v___x_2428_; uint8_t v___x_2429_; 
v___x_2422_ = l_Lean_OptionFlags_ofOptions(v___y_2421_);
v___x_2423_ = lean_st_ref_get(v___y_2352_);
v_env_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc_ref(v_env_2424_);
lean_dec(v___x_2423_);
v___x_2425_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2424_);
lean_dec_ref(v_env_2424_);
v___x_2426_ = 512;
v___x_2427_ = lean_uint16_land(v___x_2422_, v___x_2426_);
v___x_2428_ = 0;
v___x_2429_ = lean_uint16_dec_eq(v___x_2427_, v___x_2428_);
if (v___x_2429_ == 0)
{
if (v___x_2425_ == 0)
{
v___y_2396_ = v___y_2421_;
v___y_2397_ = v___x_2422_;
v___y_2398_ = v___x_2348_;
goto v___jp_2395_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2394_);
lean_inc(v_cancelTk_x3f_2393_);
lean_inc(v_currMacroScope_2392_);
lean_inc(v_quotContext_2391_);
lean_inc(v_maxHeartbeats_2390_);
lean_inc(v_initHeartbeats_2389_);
lean_inc(v_openDecls_2388_);
lean_inc(v_currNamespace_2387_);
lean_inc_ref(v_fileMap_2385_);
lean_inc_ref(v_fileName_2384_);
v___y_2355_ = v___y_2421_;
v___y_2356_ = v___x_2422_;
v_fileName_2357_ = v_fileName_2384_;
v_fileMap_2358_ = v_fileMap_2385_;
v_currNamespace_2359_ = v_currNamespace_2387_;
v_openDecls_2360_ = v_openDecls_2388_;
v_initHeartbeats_2361_ = v_initHeartbeats_2389_;
v_maxHeartbeats_2362_ = v_maxHeartbeats_2390_;
v_quotContext_2363_ = v_quotContext_2391_;
v_currMacroScope_2364_ = v_currMacroScope_2392_;
v_cancelTk_x3f_2365_ = v_cancelTk_x3f_2393_;
v_inheritedTraceOptions_2366_ = v_inheritedTraceOptions_2394_;
v_currRecDepth_2367_ = v_currRecDepth_2379_;
v_ref_2368_ = v_ref_2380_;
v_suppressElabErrors_2369_ = v_suppressElabErrors_2381_;
v_checkDeprecated_2370_ = v_checkDeprecated_2382_;
v_isRecordingDeps_2371_ = v_isRecordingDeps_2383_;
v___y_2372_ = v___y_2352_;
goto v___jp_2354_;
}
}
else
{
if (v___x_2425_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2394_);
lean_inc(v_cancelTk_x3f_2393_);
lean_inc(v_currMacroScope_2392_);
lean_inc(v_quotContext_2391_);
lean_inc(v_maxHeartbeats_2390_);
lean_inc(v_initHeartbeats_2389_);
lean_inc(v_openDecls_2388_);
lean_inc(v_currNamespace_2387_);
lean_inc_ref(v_fileMap_2385_);
lean_inc_ref(v_fileName_2384_);
v___y_2355_ = v___y_2421_;
v___y_2356_ = v___x_2422_;
v_fileName_2357_ = v_fileName_2384_;
v_fileMap_2358_ = v_fileMap_2385_;
v_currNamespace_2359_ = v_currNamespace_2387_;
v_openDecls_2360_ = v_openDecls_2388_;
v_initHeartbeats_2361_ = v_initHeartbeats_2389_;
v_maxHeartbeats_2362_ = v_maxHeartbeats_2390_;
v_quotContext_2363_ = v_quotContext_2391_;
v_currMacroScope_2364_ = v_currMacroScope_2392_;
v_cancelTk_x3f_2365_ = v_cancelTk_x3f_2393_;
v_inheritedTraceOptions_2366_ = v_inheritedTraceOptions_2394_;
v_currRecDepth_2367_ = v_currRecDepth_2379_;
v_ref_2368_ = v_ref_2380_;
v_suppressElabErrors_2369_ = v_suppressElabErrors_2381_;
v_checkDeprecated_2370_ = v_checkDeprecated_2382_;
v_isRecordingDeps_2371_ = v_isRecordingDeps_2383_;
v___y_2372_ = v___y_2352_;
goto v___jp_2354_;
}
else
{
uint8_t v___x_2430_; 
v___x_2430_ = 0;
v___y_2396_ = v___y_2421_;
v___y_2397_ = v___x_2422_;
v___y_2398_ = v___x_2430_;
goto v___jp_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object* v_mvarId_2434_, lean_object* v___x_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
uint8_t v___x_10259__boxed_2441_; lean_object* v_res_2442_; 
v___x_10259__boxed_2441_ = lean_unbox(v___x_2435_);
v_res_2442_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_mvarId_2434_, v___x_10259__boxed_2441_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
return v_res_2442_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2443_; double v___x_2444_; 
v___x_2443_ = lean_unsigned_to_nat(0u);
v___x_2444_ = lean_float_of_nat(v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object* v_cls_2448_, lean_object* v_msg_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_ref_2455_; lean_object* v___x_2456_; lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2502_; 
v_ref_2455_ = lean_ctor_get(v___y_2452_, 2);
v___x_2456_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msg_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2502_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2502_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v_traceState_2462_; lean_object* v_env_2463_; lean_object* v_nextMacroScope_2464_; lean_object* v_ngen_2465_; lean_object* v_auxDeclNGen_2466_; lean_object* v_cache_2467_; lean_object* v_recordedDeps_2468_; lean_object* v_messages_2469_; lean_object* v_infoState_2470_; lean_object* v_snapshotTasks_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2501_; 
v___x_2461_ = lean_st_ref_take(v___y_2453_);
v_traceState_2462_ = lean_ctor_get(v___x_2461_, 4);
v_env_2463_ = lean_ctor_get(v___x_2461_, 0);
v_nextMacroScope_2464_ = lean_ctor_get(v___x_2461_, 1);
v_ngen_2465_ = lean_ctor_get(v___x_2461_, 2);
v_auxDeclNGen_2466_ = lean_ctor_get(v___x_2461_, 3);
v_cache_2467_ = lean_ctor_get(v___x_2461_, 5);
v_recordedDeps_2468_ = lean_ctor_get(v___x_2461_, 6);
v_messages_2469_ = lean_ctor_get(v___x_2461_, 7);
v_infoState_2470_ = lean_ctor_get(v___x_2461_, 8);
v_snapshotTasks_2471_ = lean_ctor_get(v___x_2461_, 9);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2473_ = v___x_2461_;
v_isShared_2474_ = v_isSharedCheck_2501_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_snapshotTasks_2471_);
lean_inc(v_infoState_2470_);
lean_inc(v_messages_2469_);
lean_inc(v_recordedDeps_2468_);
lean_inc(v_cache_2467_);
lean_inc(v_traceState_2462_);
lean_inc(v_auxDeclNGen_2466_);
lean_inc(v_ngen_2465_);
lean_inc(v_nextMacroScope_2464_);
lean_inc(v_env_2463_);
lean_dec(v___x_2461_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2501_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
uint64_t v_tid_2475_; lean_object* v_traces_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2500_; 
v_tid_2475_ = lean_ctor_get_uint64(v_traceState_2462_, sizeof(void*)*1);
v_traces_2476_ = lean_ctor_get(v_traceState_2462_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_traceState_2462_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2478_ = v_traceState_2462_;
v_isShared_2479_ = v_isSharedCheck_2500_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_traces_2476_);
lean_dec(v_traceState_2462_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2500_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; double v___x_2482_; uint8_t v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2480_ = lean_box(0);
v___x_2481_ = lean_box(0);
v___x_2482_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0);
v___x_2483_ = 0;
v___x_2484_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__1));
v___x_2485_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2485_, 0, v_cls_2448_);
lean_ctor_set(v___x_2485_, 1, v___x_2481_);
lean_ctor_set(v___x_2485_, 2, v___x_2484_);
lean_ctor_set_float(v___x_2485_, sizeof(void*)*3, v___x_2482_);
lean_ctor_set_float(v___x_2485_, sizeof(void*)*3 + 8, v___x_2482_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*3 + 16, v___x_2483_);
v___x_2486_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__2));
v___x_2487_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v_a_2457_);
lean_ctor_set(v___x_2487_, 2, v___x_2486_);
lean_inc(v_ref_2455_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v_ref_2455_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = l_Lean_PersistentArray_push___redArg(v_traces_2476_, v___x_2488_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v___x_2489_);
v___x_2491_ = v___x_2478_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2489_);
lean_ctor_set_uint64(v_reuseFailAlloc_2499_, sizeof(void*)*1, v_tid_2475_);
v___x_2491_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2493_; 
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 4, v___x_2491_);
v___x_2493_ = v___x_2473_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_env_2463_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_nextMacroScope_2464_);
lean_ctor_set(v_reuseFailAlloc_2498_, 2, v_ngen_2465_);
lean_ctor_set(v_reuseFailAlloc_2498_, 3, v_auxDeclNGen_2466_);
lean_ctor_set(v_reuseFailAlloc_2498_, 4, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2498_, 5, v_cache_2467_);
lean_ctor_set(v_reuseFailAlloc_2498_, 6, v_recordedDeps_2468_);
lean_ctor_set(v_reuseFailAlloc_2498_, 7, v_messages_2469_);
lean_ctor_set(v_reuseFailAlloc_2498_, 8, v_infoState_2470_);
lean_ctor_set(v_reuseFailAlloc_2498_, 9, v_snapshotTasks_2471_);
v___x_2493_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2494_ = lean_st_ref_put(v___y_2453_, v___x_2493_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2480_);
v___x_2496_ = v___x_2459_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2480_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_cls_2503_, lean_object* v_msg_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_cls_2503_, v_msg_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v_res_2510_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0));
v___x_2513_ = l_Lean_stringToMessageData(v___x_2512_);
return v___x_2513_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2));
v___x_2516_ = l_Lean_stringToMessageData(v___x_2515_);
return v___x_2516_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4));
v___x_2519_ = l_Lean_stringToMessageData(v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object* v_a_2520_, lean_object* v___x_2521_, lean_object* v___f_2522_, lean_object* v_fixEq_x3f_2523_, lean_object* v_declName_2524_, lean_object* v___x_2525_, lean_object* v___x_2526_, lean_object* v_fixedParamPerms_2527_, lean_object* v_declNameNonRec_2528_, lean_object* v_____r_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v_mvarId_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; 
if (lean_obj_tag(v_fixEq_x3f_2523_) == 1)
{
lean_object* v_val_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2679_; 
v_val_2624_ = lean_ctor_get(v_fixEq_x3f_2523_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_fixEq_x3f_2523_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2626_ = v_fixEq_x3f_2523_;
v_isShared_2627_ = v_isSharedCheck_2679_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_val_2624_);
lean_dec(v_fixEq_x3f_2523_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2679_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; 
v___x_2628_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_2524_, v___x_2525_, v___x_2526_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___x_2646_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
lean_inc_ref(v___f_2522_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
v___x_2646_ = lean_apply_5(v___f_2522_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, lean_box(0));
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; uint8_t v___x_2648_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v___x_2648_ = lean_unbox(v_a_2647_);
lean_dec(v_a_2647_);
if (v___x_2648_ == 0)
{
lean_del_object(v___x_2626_);
v___y_2631_ = v___y_2530_;
v___y_2632_ = v___y_2531_;
v___y_2633_ = v___y_2532_;
v___y_2634_ = v___y_2533_;
goto v___jp_2630_;
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5);
lean_inc(v_a_2629_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v_a_2629_);
v___x_2651_ = v___x_2626_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2629_);
v___x_2651_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2649_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
lean_inc(v___x_2521_);
v___x_2653_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2521_, v___x_2652_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_dec_ref_known(v___x_2653_, 1);
v___y_2631_ = v___y_2530_;
v___y_2632_ = v___y_2531_;
v___y_2633_ = v___y_2532_;
v___y_2634_ = v___y_2533_;
goto v___jp_2630_;
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v_a_2629_);
lean_dec(v_val_2624_);
lean_dec(v_declNameNonRec_2528_);
lean_dec_ref(v_fixedParamPerms_2527_);
lean_dec_ref(v___f_2522_);
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2520_);
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec(v_a_2629_);
lean_del_object(v___x_2626_);
lean_dec(v_val_2624_);
lean_dec(v_declNameNonRec_2528_);
lean_dec_ref(v_fixedParamPerms_2527_);
lean_dec_ref(v___f_2522_);
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2520_);
v_a_2663_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2646_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2646_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
v___jp_2630_:
{
lean_object* v_numFixed_2635_; lean_object* v___x_2636_; 
v_numFixed_2635_ = lean_ctor_get(v_fixedParamPerms_2527_, 0);
lean_inc(v_numFixed_2635_);
lean_dec_ref(v_fixedParamPerms_2527_);
v___x_2636_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(v_declNameNonRec_2528_, v_val_2624_, v_numFixed_2635_, v_a_2629_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2636_, 1);
v_mvarId_2596_ = v_a_2637_;
v___y_2597_ = v___y_2631_;
v___y_2598_ = v___y_2632_;
v___y_2599_ = v___y_2633_;
v___y_2600_ = v___y_2634_;
goto v___jp_2595_;
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec_ref(v___f_2522_);
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2520_);
v_a_2638_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2636_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2636_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_del_object(v___x_2626_);
lean_dec(v_val_2624_);
lean_dec(v_declNameNonRec_2528_);
lean_dec_ref(v_fixedParamPerms_2527_);
lean_dec_ref(v___f_2522_);
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2520_);
v_a_2671_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2628_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2628_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
else
{
lean_object* v___x_2680_; 
lean_dec_ref(v_fixedParamPerms_2527_);
lean_dec(v___x_2525_);
lean_dec(v_fixEq_x3f_2523_);
v___x_2680_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_2524_, v_declNameNonRec_2528_, v___x_2526_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___x_2697_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
lean_inc_ref(v___f_2522_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
v___x_2697_ = lean_apply_5(v___f_2522_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, lean_box(0));
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; uint8_t v___x_2699_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = lean_unbox(v_a_2698_);
lean_dec(v_a_2698_);
if (v___x_2699_ == 0)
{
v___y_2683_ = v___y_2530_;
v___y_2684_ = v___y_2531_;
v___y_2685_ = v___y_2532_;
v___y_2686_ = v___y_2533_;
goto v___jp_2682_;
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2700_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5);
lean_inc(v_a_2681_);
v___x_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2701_, 0, v_a_2681_);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
lean_inc(v___x_2521_);
v___x_2703_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2521_, v___x_2702_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_dec_ref_known(v___x_2703_, 1);
v___y_2683_ = v___y_2530_;
v___y_2684_ = v___y_2531_;
v___y_2685_ = v___y_2532_;
v___y_2686_ = v___y_2533_;
goto v___jp_2682_;
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_a_2681_);
lean_dec_ref(v___f_2522_);
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2520_);
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec(v_a_2681_);
lean_dec_ref(v___f_2522_);
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2520_);
v_a_2712_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2697_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2697_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
v___jp_2682_:
{
lean_object* v___x_2687_; 
v___x_2687_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_a_2681_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2687_, 1);
v_mvarId_2596_ = v_a_2688_;
v___y_2597_ = v___y_2683_;
v___y_2598_ = v___y_2684_;
v___y_2599_ = v___y_2685_;
v___y_2600_ = v___y_2686_;
goto v___jp_2595_;
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec_ref(v___f_2522_);
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2520_);
v_a_2689_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2687_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2687_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v___f_2522_);
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2520_);
v_a_2720_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2680_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2680_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
v___jp_2535_:
{
if (lean_obj_tag(v___y_2540_) == 0)
{
lean_object* v_toCold_2541_; lean_object* v_options_2542_; uint8_t v_hasTrace_2543_; 
lean_dec_ref_known(v___y_2540_, 1);
v_toCold_2541_ = lean_ctor_get(v___y_2539_, 0);
v_options_2542_ = lean_ctor_get(v_toCold_2541_, 2);
v_hasTrace_2543_ = lean_ctor_get_uint8(v_options_2542_, sizeof(void*)*1);
if (v_hasTrace_2543_ == 0)
{
lean_object* v___x_2544_; 
lean_dec(v___x_2521_);
v___x_2544_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2520_, v___y_2536_);
return v___x_2544_;
}
else
{
lean_object* v_inheritedTraceOptions_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v_inheritedTraceOptions_2545_ = lean_ctor_get(v_toCold_2541_, 11);
v___x_2546_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
lean_inc(v___x_2521_);
v___x_2547_ = l_Lean_Name_append(v___x_2546_, v___x_2521_);
v___x_2548_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2545_, v_options_2542_, v___x_2547_);
lean_dec(v___x_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; 
lean_dec(v___x_2521_);
v___x_2549_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2520_, v___y_2536_);
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1);
v___x_2551_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2521_, v___x_2550_, v___y_2538_, v___y_2536_, v___y_2539_, v___y_2537_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v___x_2552_; 
lean_dec_ref_known(v___x_2551_, 1);
v___x_2552_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2520_, v___y_2536_);
return v___x_2552_;
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref(v_a_2520_);
v_a_2553_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2551_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2551_);
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
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2520_);
v_a_2561_ = lean_ctor_get(v___y_2540_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___y_2540_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___y_2540_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___y_2540_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
v___jp_2569_:
{
lean_object* v___x_2575_; uint8_t v_transparency_2576_; uint8_t v___x_2577_; uint8_t v___x_2578_; uint8_t v___x_2579_; 
v___x_2575_ = l_Lean_Meta_Context_config(v___y_2571_);
v_transparency_2576_ = lean_ctor_get_uint8(v___x_2575_, 9);
lean_dec_ref(v___x_2575_);
v___x_2577_ = 0;
v___x_2578_ = 1;
v___x_2579_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2576_, v___x_2577_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; 
v___x_2580_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v___y_2573_, v___x_2578_, v___y_2571_, v___y_2574_, v___y_2572_, v___y_2570_);
v___y_2536_ = v___y_2574_;
v___y_2537_ = v___y_2570_;
v___y_2538_ = v___y_2571_;
v___y_2539_ = v___y_2572_;
v___y_2540_ = v___x_2580_;
goto v___jp_2535_;
}
else
{
lean_object* v_keyedConfig_2581_; uint8_t v_trackZetaDelta_2582_; lean_object* v_zetaDeltaSet_2583_; lean_object* v_lctx_2584_; lean_object* v_localInstances_2585_; lean_object* v_defEqCtx_x3f_2586_; lean_object* v_synthPendingDepth_2587_; lean_object* v_customCanUnfoldPredicate_x3f_2588_; uint8_t v_univApprox_2589_; uint8_t v_inTypeClassResolution_2590_; uint8_t v_cacheInferType_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_keyedConfig_2581_ = lean_ctor_get(v___y_2571_, 0);
v_trackZetaDelta_2582_ = lean_ctor_get_uint8(v___y_2571_, sizeof(void*)*7);
v_zetaDeltaSet_2583_ = lean_ctor_get(v___y_2571_, 1);
v_lctx_2584_ = lean_ctor_get(v___y_2571_, 2);
v_localInstances_2585_ = lean_ctor_get(v___y_2571_, 3);
v_defEqCtx_x3f_2586_ = lean_ctor_get(v___y_2571_, 4);
v_synthPendingDepth_2587_ = lean_ctor_get(v___y_2571_, 5);
v_customCanUnfoldPredicate_x3f_2588_ = lean_ctor_get(v___y_2571_, 6);
v_univApprox_2589_ = lean_ctor_get_uint8(v___y_2571_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2590_ = lean_ctor_get_uint8(v___y_2571_, sizeof(void*)*7 + 2);
v_cacheInferType_2591_ = lean_ctor_get_uint8(v___y_2571_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2581_);
v___x_2592_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2577_, v_keyedConfig_2581_);
lean_inc(v_customCanUnfoldPredicate_x3f_2588_);
lean_inc(v_synthPendingDepth_2587_);
lean_inc(v_defEqCtx_x3f_2586_);
lean_inc_ref(v_localInstances_2585_);
lean_inc_ref(v_lctx_2584_);
lean_inc(v_zetaDeltaSet_2583_);
v___x_2593_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v_zetaDeltaSet_2583_);
lean_ctor_set(v___x_2593_, 2, v_lctx_2584_);
lean_ctor_set(v___x_2593_, 3, v_localInstances_2585_);
lean_ctor_set(v___x_2593_, 4, v_defEqCtx_x3f_2586_);
lean_ctor_set(v___x_2593_, 5, v_synthPendingDepth_2587_);
lean_ctor_set(v___x_2593_, 6, v_customCanUnfoldPredicate_x3f_2588_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*7, v_trackZetaDelta_2582_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*7 + 1, v_univApprox_2589_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2590_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*7 + 3, v_cacheInferType_2591_);
v___x_2594_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v___y_2573_, v___x_2578_, v___x_2593_, v___y_2574_, v___y_2572_, v___y_2570_);
lean_dec_ref_known(v___x_2593_, 7);
v___y_2536_ = v___y_2574_;
v___y_2537_ = v___y_2570_;
v___y_2538_ = v___y_2571_;
v___y_2539_ = v___y_2572_;
v___y_2540_ = v___x_2594_;
goto v___jp_2535_;
}
}
v___jp_2595_:
{
lean_object* v___x_2601_; 
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2599_);
lean_inc(v___y_2598_);
lean_inc_ref(v___y_2597_);
v___x_2601_ = lean_apply_5(v___f_2522_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, lean_box(0));
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; uint8_t v___x_2603_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2603_ = lean_unbox(v_a_2602_);
lean_dec(v_a_2602_);
if (v___x_2603_ == 0)
{
v___y_2570_ = v___y_2600_;
v___y_2571_ = v___y_2597_;
v___y_2572_ = v___y_2599_;
v___y_2573_ = v_mvarId_2596_;
v___y_2574_ = v___y_2598_;
goto v___jp_2569_;
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2604_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3);
lean_inc(v_mvarId_2596_);
v___x_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2605_, 0, v_mvarId_2596_);
v___x_2606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
lean_inc(v___x_2521_);
v___x_2607_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2521_, v___x_2606_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_dec_ref_known(v___x_2607_, 1);
v___y_2570_ = v___y_2600_;
v___y_2571_ = v___y_2597_;
v___y_2572_ = v___y_2599_;
v___y_2573_ = v_mvarId_2596_;
v___y_2574_ = v___y_2598_;
goto v___jp_2569_;
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v_mvarId_2596_);
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2520_);
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec(v_mvarId_2596_);
lean_dec(v___x_2521_);
lean_dec_ref(v_a_2520_);
v_a_2616_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2601_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2601_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object* v_a_2728_, lean_object* v___x_2729_, lean_object* v___f_2730_, lean_object* v_fixEq_x3f_2731_, lean_object* v_declName_2732_, lean_object* v___x_2733_, lean_object* v___x_2734_, lean_object* v_fixedParamPerms_2735_, lean_object* v_declNameNonRec_2736_, lean_object* v_____r_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2728_, v___x_2729_, v___f_2730_, v_fixEq_x3f_2731_, v_declName_2732_, v___x_2733_, v___x_2734_, v_fixedParamPerms_2735_, v_declNameNonRec_2736_, v_____r_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
return v_res_2743_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__0));
v___x_2746_ = l_Lean_stringToMessageData(v___x_2745_);
return v___x_2746_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__2));
v___x_2749_ = l_Lean_stringToMessageData(v___x_2748_);
return v___x_2749_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__8));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(lean_object* v_declName_2761_, lean_object* v_a_2762_, lean_object* v___x_2763_, lean_object* v_fixEq_x3f_2764_, lean_object* v_fixedParamPerms_2765_, lean_object* v_declNameNonRec_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___y_2773_; lean_object* v_a_2774_; lean_object* v___y_2786_; lean_object* v___x_2788_; 
lean_inc(v___x_2763_);
v___x_2788_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2762_, v___x_2763_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___f_2792_; lean_object* v___x_2793_; lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2817_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = l_Lean_Expr_mvarId_x21(v_a_2789_);
v___x_2791_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6));
v___f_2792_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__7));
v___x_2793_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_2791_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2817_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2817_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
uint8_t v___x_2798_; 
v___x_2798_ = lean_unbox(v_a_2794_);
lean_dec(v_a_2794_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_del_object(v___x_2796_);
v___x_2799_ = lean_box(0);
lean_inc(v_declName_2761_);
v___x_2800_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2789_, v___x_2791_, v___f_2792_, v_fixEq_x3f_2764_, v_declName_2761_, v___x_2763_, v___x_2790_, v_fixedParamPerms_2765_, v_declNameNonRec_2766_, v___x_2799_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
v___y_2786_ = v___x_2800_;
goto v___jp_2785_;
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2801_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9);
lean_inc(v___x_2790_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set_tag(v___x_2796_, 1);
lean_ctor_set(v___x_2796_, 0, v___x_2790_);
v___x_2803_ = v___x_2796_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2790_);
v___x_2803_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2801_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2791_, v___x_2804_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
lean_inc(v_declName_2761_);
v___x_2807_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2789_, v___x_2791_, v___f_2792_, v_fixEq_x3f_2764_, v_declName_2761_, v___x_2763_, v___x_2790_, v_fixedParamPerms_2765_, v_declNameNonRec_2766_, v_a_2806_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
v___y_2786_ = v___x_2807_;
goto v___jp_2785_;
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v___x_2790_);
lean_dec(v_a_2789_);
lean_dec(v_declNameNonRec_2766_);
lean_dec_ref(v_fixedParamPerms_2765_);
lean_dec(v_fixEq_x3f_2764_);
lean_dec(v___x_2763_);
v_a_2808_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2805_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2805_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
lean_inc(v_a_2808_);
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
v___y_2773_ = v___x_2813_;
v_a_2774_ = v_a_2808_;
goto v___jp_2772_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2818_; 
lean_dec(v_declNameNonRec_2766_);
lean_dec_ref(v_fixedParamPerms_2765_);
lean_dec(v_fixEq_x3f_2764_);
lean_dec(v___x_2763_);
v_a_2818_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2818_);
v___y_2773_ = v___x_2788_;
v_a_2774_ = v_a_2818_;
goto v___jp_2772_;
}
v___jp_2772_:
{
uint8_t v___x_2775_; 
v___x_2775_ = l_Lean_Exception_isInterrupt(v_a_2774_);
if (v___x_2775_ == 0)
{
uint8_t v___x_2776_; 
lean_inc_ref(v_a_2774_);
v___x_2776_ = l_Lean_Exception_isRuntime(v_a_2774_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_dec_ref(v___y_2773_);
v___x_2777_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1);
v___x_2778_ = l_Lean_MessageData_ofConstName(v_declName_2761_, v___x_2776_);
v___x_2779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3);
v___x_2781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2779_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = l_Lean_Exception_toMessageData(v_a_2774_);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2781_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_2783_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
return v___x_2784_;
}
else
{
lean_dec_ref(v_a_2774_);
lean_dec(v_declName_2761_);
return v___y_2773_;
}
}
else
{
lean_dec_ref(v_a_2774_);
lean_dec(v_declName_2761_);
return v___y_2773_;
}
}
v___jp_2785_:
{
if (lean_obj_tag(v___y_2786_) == 0)
{
lean_dec(v_declName_2761_);
return v___y_2786_;
}
else
{
lean_object* v_a_2787_; 
v_a_2787_ = lean_ctor_get(v___y_2786_, 0);
lean_inc(v_a_2787_);
v___y_2773_ = v___y_2786_;
v_a_2774_ = v_a_2787_;
goto v___jp_2772_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed(lean_object* v_declName_2819_, lean_object* v_a_2820_, lean_object* v___x_2821_, lean_object* v_fixEq_x3f_2822_, lean_object* v_fixedParamPerms_2823_, lean_object* v_declNameNonRec_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(v_declName_2819_, v_a_2820_, v___x_2821_, v_fixEq_x3f_2822_, v_fixedParamPerms_2823_, v_declNameNonRec_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4(lean_object* v_levelParams_2831_, lean_object* v_declName_2832_, lean_object* v_fixEq_x3f_2833_, lean_object* v_fixedParamPerms_2834_, lean_object* v_declNameNonRec_2835_, lean_object* v_name_2836_, lean_object* v_xs_2837_, lean_object* v_body_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v___x_2844_; lean_object* v_us_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2844_ = lean_box(0);
lean_inc(v_levelParams_2831_);
v_us_2845_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(v_levelParams_2831_, v___x_2844_);
lean_inc(v_declName_2832_);
v___x_2846_ = l_Lean_mkConst(v_declName_2832_, v_us_2845_);
v___x_2847_ = l_Lean_mkAppN(v___x_2846_, v_xs_2837_);
v___x_2848_ = l_Lean_Meta_mkEq(v___x_2847_, v_body_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2850_; lean_object* v___f_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc_n(v_a_2849_, 2);
lean_dec_ref_known(v___x_2848_, 1);
v___x_2850_ = lean_box(0);
v___f_2851_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed), 11, 6);
lean_closure_set(v___f_2851_, 0, v_declName_2832_);
lean_closure_set(v___f_2851_, 1, v_a_2849_);
lean_closure_set(v___f_2851_, 2, v___x_2850_);
lean_closure_set(v___f_2851_, 3, v_fixEq_x3f_2833_);
lean_closure_set(v___f_2851_, 4, v_fixedParamPerms_2834_);
lean_closure_set(v___f_2851_, 5, v_declNameNonRec_2835_);
v___x_2852_ = 0;
v___x_2853_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v___f_2851_, v___x_2852_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; uint8_t v___x_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v___x_2855_ = 1;
v___x_2856_ = 1;
v___x_2857_ = l_Lean_Meta_mkForallFVars(v_xs_2837_, v_a_2849_, v___x_2852_, v___x_2855_, v___x_2855_, v___x_2856_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v___x_2859_ = l_Lean_Meta_letToHave(v_a_2858_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2861_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v___x_2861_ = l_Lean_Meta_mkLambdaFVars(v_xs_2837_, v_a_2854_, v___x_2852_, v___x_2855_, v___x_2852_, v___x_2855_, v___x_2856_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v_a_2867_; lean_object* v___x_2868_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
lean_inc(v_name_2836_);
v___x_2863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2863_, 0, v_name_2836_);
lean_ctor_set(v___x_2863_, 1, v_levelParams_2831_);
lean_ctor_set(v___x_2863_, 2, v_a_2860_);
v___x_2864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2864_, 0, v_name_2836_);
lean_ctor_set(v___x_2864_, 1, v___x_2844_);
v___x_2865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v_a_2862_);
lean_ctor_set(v___x_2865_, 2, v___x_2864_);
v___x_2866_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v___x_2865_, v___y_2842_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
v___x_2868_ = l_Lean_addDecl(v_a_2867_, v___x_2852_, v___y_2841_, v___y_2842_);
return v___x_2868_;
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec(v_a_2860_);
lean_dec(v_name_2836_);
lean_dec(v_levelParams_2831_);
v_a_2869_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2861_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2861_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec(v_a_2854_);
lean_dec(v_name_2836_);
lean_dec(v_levelParams_2831_);
v_a_2877_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2859_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2859_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v_a_2854_);
lean_dec(v_name_2836_);
lean_dec(v_levelParams_2831_);
v_a_2885_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2857_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2857_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec(v_a_2849_);
lean_dec(v_name_2836_);
lean_dec(v_levelParams_2831_);
v_a_2893_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2853_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2853_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec(v_name_2836_);
lean_dec(v_declNameNonRec_2835_);
lean_dec_ref(v_fixedParamPerms_2834_);
lean_dec(v_fixEq_x3f_2833_);
lean_dec(v_declName_2832_);
lean_dec(v_levelParams_2831_);
v_a_2901_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2848_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2848_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4___boxed(lean_object* v_levelParams_2909_, lean_object* v_declName_2910_, lean_object* v_fixEq_x3f_2911_, lean_object* v_fixedParamPerms_2912_, lean_object* v_declNameNonRec_2913_, lean_object* v_name_2914_, lean_object* v_xs_2915_, lean_object* v_body_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4(v_levelParams_2909_, v_declName_2910_, v_fixEq_x3f_2911_, v_fixedParamPerms_2912_, v_declNameNonRec_2913_, v_name_2914_, v_xs_2915_, v_body_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v_xs_2915_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object* v_declName_2923_, lean_object* v_info_2924_, lean_object* v_name_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v_toCold_2931_; lean_object* v_levelParams_2932_; lean_object* v_value_2933_; lean_object* v_declNameNonRec_2934_; lean_object* v_fixedParamPerms_2935_; lean_object* v_fixEq_x3f_2936_; lean_object* v_currRecDepth_2937_; lean_object* v_ref_2938_; uint8_t v_suppressElabErrors_2939_; uint8_t v_checkDeprecated_2940_; uint8_t v_isRecordingDeps_2941_; lean_object* v_fileName_2942_; lean_object* v_fileMap_2943_; lean_object* v_options_2944_; lean_object* v_currNamespace_2945_; lean_object* v_openDecls_2946_; lean_object* v_initHeartbeats_2947_; lean_object* v_maxHeartbeats_2948_; lean_object* v_quotContext_2949_; lean_object* v_currMacroScope_2950_; lean_object* v_cancelTk_x3f_2951_; lean_object* v_inheritedTraceOptions_2952_; lean_object* v___f_2953_; uint8_t v___x_2954_; uint16_t v___y_2956_; lean_object* v___y_2957_; lean_object* v_fileName_2958_; lean_object* v_fileMap_2959_; lean_object* v_currNamespace_2960_; lean_object* v_openDecls_2961_; lean_object* v_initHeartbeats_2962_; lean_object* v_maxHeartbeats_2963_; lean_object* v_quotContext_2964_; lean_object* v_currMacroScope_2965_; lean_object* v_cancelTk_x3f_2966_; lean_object* v_inheritedTraceOptions_2967_; lean_object* v_currRecDepth_2968_; lean_object* v_ref_2969_; uint8_t v_suppressElabErrors_2970_; uint8_t v_checkDeprecated_2971_; uint8_t v_isRecordingDeps_2972_; lean_object* v___y_2973_; uint8_t v___y_2980_; uint16_t v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_3005_; 
v_toCold_2931_ = lean_ctor_get(v_a_2928_, 0);
v_levelParams_2932_ = lean_ctor_get(v_info_2924_, 1);
lean_inc(v_levelParams_2932_);
v_value_2933_ = lean_ctor_get(v_info_2924_, 3);
lean_inc_ref(v_value_2933_);
v_declNameNonRec_2934_ = lean_ctor_get(v_info_2924_, 5);
lean_inc(v_declNameNonRec_2934_);
v_fixedParamPerms_2935_ = lean_ctor_get(v_info_2924_, 6);
lean_inc_ref(v_fixedParamPerms_2935_);
v_fixEq_x3f_2936_ = lean_ctor_get(v_info_2924_, 8);
lean_inc(v_fixEq_x3f_2936_);
lean_dec_ref(v_info_2924_);
v_currRecDepth_2937_ = lean_ctor_get(v_a_2928_, 1);
v_ref_2938_ = lean_ctor_get(v_a_2928_, 2);
v_suppressElabErrors_2939_ = lean_ctor_get_uint8(v_a_2928_, sizeof(void*)*3 + 2);
v_checkDeprecated_2940_ = lean_ctor_get_uint8(v_a_2928_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2941_ = lean_ctor_get_uint8(v_a_2928_, sizeof(void*)*3 + 4);
v_fileName_2942_ = lean_ctor_get(v_toCold_2931_, 0);
v_fileMap_2943_ = lean_ctor_get(v_toCold_2931_, 1);
v_options_2944_ = lean_ctor_get(v_toCold_2931_, 2);
v_currNamespace_2945_ = lean_ctor_get(v_toCold_2931_, 4);
v_openDecls_2946_ = lean_ctor_get(v_toCold_2931_, 5);
v_initHeartbeats_2947_ = lean_ctor_get(v_toCold_2931_, 6);
v_maxHeartbeats_2948_ = lean_ctor_get(v_toCold_2931_, 7);
v_quotContext_2949_ = lean_ctor_get(v_toCold_2931_, 8);
v_currMacroScope_2950_ = lean_ctor_get(v_toCold_2931_, 9);
v_cancelTk_x3f_2951_ = lean_ctor_get(v_toCold_2931_, 10);
v_inheritedTraceOptions_2952_ = lean_ctor_get(v_toCold_2931_, 11);
v___f_2953_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4___boxed), 13, 6);
lean_closure_set(v___f_2953_, 0, v_levelParams_2932_);
lean_closure_set(v___f_2953_, 1, v_declName_2923_);
lean_closure_set(v___f_2953_, 2, v_fixEq_x3f_2936_);
lean_closure_set(v___f_2953_, 3, v_fixedParamPerms_2935_);
lean_closure_set(v___f_2953_, 4, v_declNameNonRec_2934_);
lean_closure_set(v___f_2953_, 5, v_name_2925_);
v___x_2954_ = 0;
if (v_isRecordingDeps_2941_ == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_2944_);
v___x_3016_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_options_2944_, v___x_3015_, v_isRecordingDeps_2941_);
v___y_3005_ = v___x_3016_;
goto v___jp_3004_;
}
else
{
lean_object* v___x_3017_; 
lean_inc_ref(v_options_2944_);
v___x_3017_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2944_);
v___y_3005_ = v___x_3017_;
goto v___jp_3004_;
}
v___jp_2955_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2974_ = l_Lean_maxRecDepth;
v___x_2975_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___y_2957_, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2976_, 0, v_fileName_2958_);
lean_ctor_set(v___x_2976_, 1, v_fileMap_2959_);
lean_ctor_set(v___x_2976_, 2, v___y_2957_);
lean_ctor_set(v___x_2976_, 3, v___x_2975_);
lean_ctor_set(v___x_2976_, 4, v_currNamespace_2960_);
lean_ctor_set(v___x_2976_, 5, v_openDecls_2961_);
lean_ctor_set(v___x_2976_, 6, v_initHeartbeats_2962_);
lean_ctor_set(v___x_2976_, 7, v_maxHeartbeats_2963_);
lean_ctor_set(v___x_2976_, 8, v_quotContext_2964_);
lean_ctor_set(v___x_2976_, 9, v_currMacroScope_2965_);
lean_ctor_set(v___x_2976_, 10, v_cancelTk_x3f_2966_);
lean_ctor_set(v___x_2976_, 11, v_inheritedTraceOptions_2967_);
lean_inc(v_ref_2969_);
lean_inc(v_currRecDepth_2968_);
v___x_2977_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
lean_ctor_set(v___x_2977_, 1, v_currRecDepth_2968_);
lean_ctor_set(v___x_2977_, 2, v_ref_2969_);
lean_ctor_set_uint16(v___x_2977_, sizeof(void*)*3, v___y_2956_);
lean_ctor_set_uint8(v___x_2977_, sizeof(void*)*3 + 2, v_suppressElabErrors_2970_);
lean_ctor_set_uint8(v___x_2977_, sizeof(void*)*3 + 3, v_checkDeprecated_2971_);
lean_ctor_set_uint8(v___x_2977_, sizeof(void*)*3 + 4, v_isRecordingDeps_2972_);
v___x_2978_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_2933_, v___f_2953_, v___x_2954_, v_a_2926_, v_a_2927_, v___x_2977_, v___y_2973_);
lean_dec_ref_known(v___x_2977_, 3);
return v___x_2978_;
}
v___jp_2979_:
{
lean_object* v___x_2983_; lean_object* v_env_2984_; lean_object* v_nextMacroScope_2985_; lean_object* v_ngen_2986_; lean_object* v_auxDeclNGen_2987_; lean_object* v_traceState_2988_; lean_object* v_recordedDeps_2989_; lean_object* v_messages_2990_; lean_object* v_infoState_2991_; lean_object* v_snapshotTasks_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3002_; 
v___x_2983_ = lean_st_ref_take(v_a_2929_);
v_env_2984_ = lean_ctor_get(v___x_2983_, 0);
v_nextMacroScope_2985_ = lean_ctor_get(v___x_2983_, 1);
v_ngen_2986_ = lean_ctor_get(v___x_2983_, 2);
v_auxDeclNGen_2987_ = lean_ctor_get(v___x_2983_, 3);
v_traceState_2988_ = lean_ctor_get(v___x_2983_, 4);
v_recordedDeps_2989_ = lean_ctor_get(v___x_2983_, 6);
v_messages_2990_ = lean_ctor_get(v___x_2983_, 7);
v_infoState_2991_ = lean_ctor_get(v___x_2983_, 8);
v_snapshotTasks_2992_ = lean_ctor_get(v___x_2983_, 9);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3002_ == 0)
{
lean_object* v_unused_3003_; 
v_unused_3003_ = lean_ctor_get(v___x_2983_, 5);
lean_dec(v_unused_3003_);
v___x_2994_ = v___x_2983_;
v_isShared_2995_ = v_isSharedCheck_3002_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_snapshotTasks_2992_);
lean_inc(v_infoState_2991_);
lean_inc(v_messages_2990_);
lean_inc(v_recordedDeps_2989_);
lean_inc(v_traceState_2988_);
lean_inc(v_auxDeclNGen_2987_);
lean_inc(v_ngen_2986_);
lean_inc(v_nextMacroScope_2985_);
lean_inc(v_env_2984_);
lean_dec(v___x_2983_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3002_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2999_; 
v___x_2996_ = l_Lean_Kernel_enableDiag(v_env_2984_, v___y_2980_);
v___x_2997_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__3);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 5, v___x_2997_);
lean_ctor_set(v___x_2994_, 0, v___x_2996_);
v___x_2999_ = v___x_2994_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2996_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_nextMacroScope_2985_);
lean_ctor_set(v_reuseFailAlloc_3001_, 2, v_ngen_2986_);
lean_ctor_set(v_reuseFailAlloc_3001_, 3, v_auxDeclNGen_2987_);
lean_ctor_set(v_reuseFailAlloc_3001_, 4, v_traceState_2988_);
lean_ctor_set(v_reuseFailAlloc_3001_, 5, v___x_2997_);
lean_ctor_set(v_reuseFailAlloc_3001_, 6, v_recordedDeps_2989_);
lean_ctor_set(v_reuseFailAlloc_3001_, 7, v_messages_2990_);
lean_ctor_set(v_reuseFailAlloc_3001_, 8, v_infoState_2991_);
lean_ctor_set(v_reuseFailAlloc_3001_, 9, v_snapshotTasks_2992_);
v___x_2999_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_st_ref_put(v_a_2929_, v___x_2999_);
lean_inc_ref(v_inheritedTraceOptions_2952_);
lean_inc(v_cancelTk_x3f_2951_);
lean_inc(v_currMacroScope_2950_);
lean_inc(v_quotContext_2949_);
lean_inc(v_maxHeartbeats_2948_);
lean_inc(v_initHeartbeats_2947_);
lean_inc(v_openDecls_2946_);
lean_inc(v_currNamespace_2945_);
lean_inc_ref(v_fileMap_2943_);
lean_inc_ref(v_fileName_2942_);
v___y_2956_ = v___y_2981_;
v___y_2957_ = v___y_2982_;
v_fileName_2958_ = v_fileName_2942_;
v_fileMap_2959_ = v_fileMap_2943_;
v_currNamespace_2960_ = v_currNamespace_2945_;
v_openDecls_2961_ = v_openDecls_2946_;
v_initHeartbeats_2962_ = v_initHeartbeats_2947_;
v_maxHeartbeats_2963_ = v_maxHeartbeats_2948_;
v_quotContext_2964_ = v_quotContext_2949_;
v_currMacroScope_2965_ = v_currMacroScope_2950_;
v_cancelTk_x3f_2966_ = v_cancelTk_x3f_2951_;
v_inheritedTraceOptions_2967_ = v_inheritedTraceOptions_2952_;
v_currRecDepth_2968_ = v_currRecDepth_2937_;
v_ref_2969_ = v_ref_2938_;
v_suppressElabErrors_2970_ = v_suppressElabErrors_2939_;
v_checkDeprecated_2971_ = v_checkDeprecated_2940_;
v_isRecordingDeps_2972_ = v_isRecordingDeps_2941_;
v___y_2973_ = v_a_2929_;
goto v___jp_2955_;
}
}
}
v___jp_3004_:
{
uint16_t v___x_3006_; lean_object* v___x_3007_; lean_object* v_env_3008_; uint8_t v___x_3009_; uint16_t v___x_3010_; uint16_t v___x_3011_; uint16_t v___x_3012_; uint8_t v___x_3013_; 
v___x_3006_ = l_Lean_OptionFlags_ofOptions(v___y_3005_);
v___x_3007_ = lean_st_ref_get(v_a_2929_);
v_env_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc_ref(v_env_3008_);
lean_dec(v___x_3007_);
v___x_3009_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3008_);
lean_dec_ref(v_env_3008_);
v___x_3010_ = 512;
v___x_3011_ = lean_uint16_land(v___x_3006_, v___x_3010_);
v___x_3012_ = 0;
v___x_3013_ = lean_uint16_dec_eq(v___x_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
if (v___x_3009_ == 0)
{
uint8_t v___x_3014_; 
v___x_3014_ = 1;
v___y_2980_ = v___x_3014_;
v___y_2981_ = v___x_3006_;
v___y_2982_ = v___y_3005_;
goto v___jp_2979_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2952_);
lean_inc(v_cancelTk_x3f_2951_);
lean_inc(v_currMacroScope_2950_);
lean_inc(v_quotContext_2949_);
lean_inc(v_maxHeartbeats_2948_);
lean_inc(v_initHeartbeats_2947_);
lean_inc(v_openDecls_2946_);
lean_inc(v_currNamespace_2945_);
lean_inc_ref(v_fileMap_2943_);
lean_inc_ref(v_fileName_2942_);
v___y_2956_ = v___x_3006_;
v___y_2957_ = v___y_3005_;
v_fileName_2958_ = v_fileName_2942_;
v_fileMap_2959_ = v_fileMap_2943_;
v_currNamespace_2960_ = v_currNamespace_2945_;
v_openDecls_2961_ = v_openDecls_2946_;
v_initHeartbeats_2962_ = v_initHeartbeats_2947_;
v_maxHeartbeats_2963_ = v_maxHeartbeats_2948_;
v_quotContext_2964_ = v_quotContext_2949_;
v_currMacroScope_2965_ = v_currMacroScope_2950_;
v_cancelTk_x3f_2966_ = v_cancelTk_x3f_2951_;
v_inheritedTraceOptions_2967_ = v_inheritedTraceOptions_2952_;
v_currRecDepth_2968_ = v_currRecDepth_2937_;
v_ref_2969_ = v_ref_2938_;
v_suppressElabErrors_2970_ = v_suppressElabErrors_2939_;
v_checkDeprecated_2971_ = v_checkDeprecated_2940_;
v_isRecordingDeps_2972_ = v_isRecordingDeps_2941_;
v___y_2973_ = v_a_2929_;
goto v___jp_2955_;
}
}
else
{
if (v___x_3009_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2952_);
lean_inc(v_cancelTk_x3f_2951_);
lean_inc(v_currMacroScope_2950_);
lean_inc(v_quotContext_2949_);
lean_inc(v_maxHeartbeats_2948_);
lean_inc(v_initHeartbeats_2947_);
lean_inc(v_openDecls_2946_);
lean_inc(v_currNamespace_2945_);
lean_inc_ref(v_fileMap_2943_);
lean_inc_ref(v_fileName_2942_);
v___y_2956_ = v___x_3006_;
v___y_2957_ = v___y_3005_;
v_fileName_2958_ = v_fileName_2942_;
v_fileMap_2959_ = v_fileMap_2943_;
v_currNamespace_2960_ = v_currNamespace_2945_;
v_openDecls_2961_ = v_openDecls_2946_;
v_initHeartbeats_2962_ = v_initHeartbeats_2947_;
v_maxHeartbeats_2963_ = v_maxHeartbeats_2948_;
v_quotContext_2964_ = v_quotContext_2949_;
v_currMacroScope_2965_ = v_currMacroScope_2950_;
v_cancelTk_x3f_2966_ = v_cancelTk_x3f_2951_;
v_inheritedTraceOptions_2967_ = v_inheritedTraceOptions_2952_;
v_currRecDepth_2968_ = v_currRecDepth_2937_;
v_ref_2969_ = v_ref_2938_;
v_suppressElabErrors_2970_ = v_suppressElabErrors_2939_;
v_checkDeprecated_2971_ = v_checkDeprecated_2940_;
v_isRecordingDeps_2972_ = v_isRecordingDeps_2941_;
v___y_2973_ = v_a_2929_;
goto v___jp_2955_;
}
else
{
v___y_2980_ = v___x_2954_;
v___y_2981_ = v___x_3006_;
v___y_2982_ = v___y_3005_;
goto v___jp_2979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3018_, lean_object* v_info_3019_, lean_object* v_name_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_3018_, v_info_3019_, v_name_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* v_declName_3027_, lean_object* v_info_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v___x_3034_; lean_object* v_env_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3034_ = lean_st_ref_get(v_a_3032_);
v_env_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc_ref(v_env_3035_);
lean_dec(v___x_3034_);
v___x_3036_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc_n(v_declName_3027_, 2);
v___x_3037_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3035_, v_declName_3027_, v___x_3036_);
lean_inc_n(v___x_3037_, 2);
v___x_3038_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3038_, 0, v_declName_3027_);
lean_closure_set(v___x_3038_, 1, v_info_3028_);
lean_closure_set(v___x_3038_, 2, v___x_3037_);
v___x_3039_ = l_Lean_Meta_realizeConst(v_declName_3027_, v___x_3037_, v___x_3038_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3046_ == 0)
{
lean_object* v_unused_3047_; 
v_unused_3047_ = lean_ctor_get(v___x_3039_, 0);
lean_dec(v_unused_3047_);
v___x_3041_ = v___x_3039_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_dec(v___x_3039_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3037_);
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3037_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v___x_3037_);
v_a_3048_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3039_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3039_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object* v_declName_3056_, lean_object* v_info_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_3056_, v_info_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* v_declName_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v___x_3070_; lean_object* v_env_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v_env_3075_; uint8_t v___x_3076_; uint8_t v___x_3077_; 
v___x_3070_ = lean_st_ref_get(v_a_3068_);
v_env_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc_ref(v_env_3071_);
lean_dec(v___x_3070_);
v___x_3072_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3064_);
v___x_3073_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3071_, v_declName_3064_, v___x_3072_);
v___x_3074_ = lean_st_ref_get(v_a_3068_);
v_env_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc_ref_n(v_env_3075_, 2);
lean_dec(v___x_3074_);
v___x_3076_ = 1;
lean_inc(v___x_3073_);
v___x_3077_ = l_Lean_Environment_contains(v_env_3075_, v___x_3073_, v___x_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; lean_object* v_toEnvExtension_3079_; lean_object* v_asyncMode_3080_; uint8_t v___x_3081_; lean_object* v___x_3082_; 
lean_dec(v___x_3073_);
v___x_3078_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
v_toEnvExtension_3079_ = lean_ctor_get(v___x_3078_, 0);
v_asyncMode_3080_ = lean_ctor_get(v_toEnvExtension_3079_, 2);
v___x_3081_ = 0;
lean_inc(v_declName_3064_);
v___x_3082_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3078_, v_env_3075_, v_declName_3064_, v_asyncMode_3080_, v___x_3081_);
if (lean_obj_tag(v___x_3082_) == 1)
{
lean_object* v_val_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3107_; 
v_val_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3107_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_val_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3107_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; 
v___x_3087_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_3064_, v_val_3083_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3098_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3090_ = v___x_3087_;
v_isShared_3091_ = v_isSharedCheck_3098_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3087_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3098_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v_a_3088_);
v___x_3093_ = v___x_3085_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3095_; 
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3093_);
v___x_3095_ = v___x_3090_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_del_object(v___x_3085_);
v_a_3099_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3087_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3087_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
else
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_dec(v___x_3082_);
lean_dec(v_declName_3064_);
v___x_3108_ = lean_box(0);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
lean_dec_ref(v_env_3075_);
lean_dec(v_declName_3064_);
v___x_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3073_);
v___x_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
return v___x_3111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object* v_declName_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_);
lean_dec(v_a_3116_);
lean_dec_ref(v_a_3115_);
lean_dec(v_a_3114_);
lean_dec_ref(v_a_3113_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_));
v___x_3122_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
return v_res_3124_;
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
res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_();
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
