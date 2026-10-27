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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(lean_object* v_thm_154_, lean_object* v___y_155_){
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
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg___boxed(lean_object* v_thm_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v_thm_173_, v___y_174_);
lean_dec(v___y_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4(lean_object* v_thm_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v_thm_177_, v___y_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___boxed(lean_object* v_thm_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4(v_thm_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(lean_object* v___y_191_, uint8_t v_isExporting_192_, lean_object* v___x_193_, lean_object* v___y_194_, lean_object* v___x_195_, lean_object* v_a_x3f_196_){
_start:
{
lean_object* v___x_198_; lean_object* v_env_199_; lean_object* v_nextMacroScope_200_; lean_object* v_ngen_201_; lean_object* v_auxDeclNGen_202_; lean_object* v_traceState_203_; lean_object* v_recordedDeps_204_; lean_object* v_messages_205_; lean_object* v_infoState_206_; lean_object* v_snapshotTasks_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_232_; 
v___x_198_ = lean_st_ref_take(v___y_191_);
v_env_199_ = lean_ctor_get(v___x_198_, 0);
v_nextMacroScope_200_ = lean_ctor_get(v___x_198_, 1);
v_ngen_201_ = lean_ctor_get(v___x_198_, 2);
v_auxDeclNGen_202_ = lean_ctor_get(v___x_198_, 3);
v_traceState_203_ = lean_ctor_get(v___x_198_, 4);
v_recordedDeps_204_ = lean_ctor_get(v___x_198_, 6);
v_messages_205_ = lean_ctor_get(v___x_198_, 7);
v_infoState_206_ = lean_ctor_get(v___x_198_, 8);
v_snapshotTasks_207_ = lean_ctor_get(v___x_198_, 9);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v___x_198_, 5);
lean_dec(v_unused_233_);
v___x_209_ = v___x_198_;
v_isShared_210_ = v_isSharedCheck_232_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_snapshotTasks_207_);
lean_inc(v_infoState_206_);
lean_inc(v_messages_205_);
lean_inc(v_recordedDeps_204_);
lean_inc(v_traceState_203_);
lean_inc(v_auxDeclNGen_202_);
lean_inc(v_ngen_201_);
lean_inc(v_nextMacroScope_200_);
lean_inc(v_env_199_);
lean_dec(v___x_198_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_232_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = l_Lean_Environment_setExporting(v_env_199_, v_isExporting_192_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 5, v___x_193_);
lean_ctor_set(v___x_209_, 0, v___x_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_nextMacroScope_200_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_ngen_201_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_auxDeclNGen_202_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_traceState_203_);
lean_ctor_set(v_reuseFailAlloc_231_, 5, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_231_, 6, v_recordedDeps_204_);
lean_ctor_set(v_reuseFailAlloc_231_, 7, v_messages_205_);
lean_ctor_set(v_reuseFailAlloc_231_, 8, v_infoState_206_);
lean_ctor_set(v_reuseFailAlloc_231_, 9, v_snapshotTasks_207_);
v___x_213_ = v_reuseFailAlloc_231_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_mctx_216_; lean_object* v_zetaDeltaFVarIds_217_; lean_object* v_postponed_218_; lean_object* v_diag_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_229_; 
v___x_214_ = lean_st_ref_put(v___y_191_, v___x_213_);
v___x_215_ = lean_st_ref_take(v___y_194_);
v_mctx_216_ = lean_ctor_get(v___x_215_, 0);
v_zetaDeltaFVarIds_217_ = lean_ctor_get(v___x_215_, 2);
v_postponed_218_ = lean_ctor_get(v___x_215_, 3);
v_diag_219_ = lean_ctor_get(v___x_215_, 4);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; 
v_unused_230_ = lean_ctor_get(v___x_215_, 1);
lean_dec(v_unused_230_);
v___x_221_ = v___x_215_;
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_diag_219_);
lean_inc(v_postponed_218_);
lean_inc(v_zetaDeltaFVarIds_217_);
lean_inc(v_mctx_216_);
lean_dec(v___x_215_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_box(0);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v___x_195_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_mctx_216_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_zetaDeltaFVarIds_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_postponed_218_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_diag_219_);
v___x_225_ = v_reuseFailAlloc_228_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_st_ref_put(v___y_194_, v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_223_);
return v___x_227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0___boxed(lean_object* v___y_234_, lean_object* v_isExporting_235_, lean_object* v___x_236_, lean_object* v___y_237_, lean_object* v___x_238_, lean_object* v_a_x3f_239_, lean_object* v___y_240_){
_start:
{
uint8_t v_isExporting_boxed_241_; lean_object* v_res_242_; 
v_isExporting_boxed_241_ = lean_unbox(v_isExporting_235_);
v_res_242_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(v___y_234_, v_isExporting_boxed_241_, v___x_236_, v___y_237_, v___x_238_, v_a_x3f_239_);
lean_dec(v_a_x3f_239_);
lean_dec(v___y_237_);
lean_dec(v___y_234_);
return v_res_242_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_243_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1);
v___x_249_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
lean_ctor_set(v___x_249_, 2, v___x_248_);
lean_ctor_set(v___x_249_, 3, v___x_248_);
lean_ctor_set(v___x_249_, 4, v___x_248_);
lean_ctor_set(v___x_249_, 5, v___x_248_);
lean_ctor_set(v___x_249_, 6, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(lean_object* v_x_250_, uint8_t v_isExporting_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; lean_object* v_env_258_; lean_object* v___x_259_; uint8_t v_isModule_260_; 
v___x_257_ = lean_st_ref_get(v___y_255_);
v_env_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc_ref(v_env_258_);
lean_dec(v___x_257_);
v___x_259_ = l_Lean_Environment_header(v_env_258_);
v_isModule_260_ = lean_ctor_get_uint8(v___x_259_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_259_);
if (v_isModule_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec_ref(v_env_258_);
lean_inc(v___y_255_);
lean_inc_ref(v___y_254_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
v___x_261_ = lean_apply_5(v_x_250_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, lean_box(0));
return v___x_261_;
}
else
{
uint8_t v_isExporting_262_; 
v_isExporting_262_ = lean_ctor_get_uint8(v_env_258_, sizeof(void*)*13);
lean_dec_ref(v_env_258_);
if (v_isExporting_251_ == 0)
{
if (v_isExporting_262_ == 0)
{
lean_object* v___x_329_; 
lean_inc(v___y_255_);
lean_inc_ref(v___y_254_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
v___x_329_ = lean_apply_5(v_x_250_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, lean_box(0));
return v___x_329_;
}
else
{
goto v___jp_263_;
}
}
else
{
if (v_isExporting_262_ == 0)
{
goto v___jp_263_;
}
else
{
lean_object* v___x_330_; 
lean_inc(v___y_255_);
lean_inc_ref(v___y_254_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
v___x_330_ = lean_apply_5(v_x_250_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, lean_box(0));
return v___x_330_;
}
}
v___jp_263_:
{
lean_object* v___x_264_; lean_object* v_env_265_; lean_object* v_nextMacroScope_266_; lean_object* v_ngen_267_; lean_object* v_auxDeclNGen_268_; lean_object* v_traceState_269_; lean_object* v_recordedDeps_270_; lean_object* v_messages_271_; lean_object* v_infoState_272_; lean_object* v_snapshotTasks_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_327_; 
v___x_264_ = lean_st_ref_take(v___y_255_);
v_env_265_ = lean_ctor_get(v___x_264_, 0);
v_nextMacroScope_266_ = lean_ctor_get(v___x_264_, 1);
v_ngen_267_ = lean_ctor_get(v___x_264_, 2);
v_auxDeclNGen_268_ = lean_ctor_get(v___x_264_, 3);
v_traceState_269_ = lean_ctor_get(v___x_264_, 4);
v_recordedDeps_270_ = lean_ctor_get(v___x_264_, 6);
v_messages_271_ = lean_ctor_get(v___x_264_, 7);
v_infoState_272_ = lean_ctor_get(v___x_264_, 8);
v_snapshotTasks_273_ = lean_ctor_get(v___x_264_, 9);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v___x_264_, 5);
lean_dec(v_unused_328_);
v___x_275_ = v___x_264_;
v_isShared_276_ = v_isSharedCheck_327_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_snapshotTasks_273_);
lean_inc(v_infoState_272_);
lean_inc(v_messages_271_);
lean_inc(v_recordedDeps_270_);
lean_inc(v_traceState_269_);
lean_inc(v_auxDeclNGen_268_);
lean_inc(v_ngen_267_);
lean_inc(v_nextMacroScope_266_);
lean_inc(v_env_265_);
lean_dec(v___x_264_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_327_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_277_ = l_Lean_Environment_setExporting(v_env_265_, v_isExporting_251_);
v___x_278_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 5, v___x_278_);
lean_ctor_set(v___x_275_, 0, v___x_277_);
v___x_280_ = v___x_275_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_nextMacroScope_266_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_ngen_267_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_auxDeclNGen_268_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_traceState_269_);
lean_ctor_set(v_reuseFailAlloc_326_, 5, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_326_, 6, v_recordedDeps_270_);
lean_ctor_set(v_reuseFailAlloc_326_, 7, v_messages_271_);
lean_ctor_set(v_reuseFailAlloc_326_, 8, v_infoState_272_);
lean_ctor_set(v_reuseFailAlloc_326_, 9, v_snapshotTasks_273_);
v___x_280_ = v_reuseFailAlloc_326_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_mctx_283_; lean_object* v_zetaDeltaFVarIds_284_; lean_object* v_postponed_285_; lean_object* v_diag_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_324_; 
v___x_281_ = lean_st_ref_put(v___y_255_, v___x_280_);
v___x_282_ = lean_st_ref_take(v___y_253_);
v_mctx_283_ = lean_ctor_get(v___x_282_, 0);
v_zetaDeltaFVarIds_284_ = lean_ctor_get(v___x_282_, 2);
v_postponed_285_ = lean_ctor_get(v___x_282_, 3);
v_diag_286_ = lean_ctor_get(v___x_282_, 4);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; 
v_unused_325_ = lean_ctor_get(v___x_282_, 1);
lean_dec(v_unused_325_);
v___x_288_ = v___x_282_;
v_isShared_289_ = v_isSharedCheck_324_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_diag_286_);
lean_inc(v_postponed_285_);
lean_inc(v_zetaDeltaFVarIds_284_);
lean_inc(v_mctx_283_);
lean_dec(v___x_282_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_324_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_290_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_mctx_283_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v_zetaDeltaFVarIds_284_);
lean_ctor_set(v_reuseFailAlloc_323_, 3, v_postponed_285_);
lean_ctor_set(v_reuseFailAlloc_323_, 4, v_diag_286_);
v___x_292_ = v_reuseFailAlloc_323_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; lean_object* v_r_294_; 
v___x_293_ = lean_st_ref_put(v___y_253_, v___x_292_);
lean_inc(v___y_255_);
lean_inc_ref(v___y_254_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
v_r_294_ = lean_apply_5(v_x_250_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, lean_box(0));
if (lean_obj_tag(v_r_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_311_; 
v_a_295_ = lean_ctor_get(v_r_294_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_r_294_);
if (v_isSharedCheck_311_ == 0)
{
v___x_297_ = v_r_294_;
v_isShared_298_ = v_isSharedCheck_311_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v_r_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_311_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
lean_inc(v_a_295_);
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 1);
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_310_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v___x_301_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(v___y_255_, v_isExporting_262_, v___x_278_, v___y_253_, v___x_290_, v___x_300_);
lean_dec_ref(v___x_300_);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v___x_301_, 0);
lean_dec(v_unused_309_);
v___x_303_ = v___x_301_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_dec(v___x_301_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v_a_295_);
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_295_);
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
else
{
lean_object* v_a_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_312_ = lean_ctor_get(v_r_294_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v_r_294_, 1);
v___x_313_ = lean_box(0);
v___x_314_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(v___y_255_, v_isExporting_262_, v___x_278_, v___y_253_, v___x_290_, v___x_313_);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v___x_314_, 0);
lean_dec(v_unused_322_);
v___x_316_ = v___x_314_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_dec(v___x_314_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 1);
lean_ctor_set(v___x_316_, 0, v_a_312_);
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_312_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___boxed(lean_object* v_x_331_, lean_object* v_isExporting_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
uint8_t v_isExporting_boxed_338_; lean_object* v_res_339_; 
v_isExporting_boxed_338_ = lean_unbox(v_isExporting_332_);
v_res_339_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v_x_331_, v_isExporting_boxed_338_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5(lean_object* v_00_u03b1_340_, lean_object* v_x_341_, uint8_t v_isExporting_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v_x_341_, v_isExporting_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___boxed(lean_object* v_00_u03b1_349_, lean_object* v_x_350_, lean_object* v_isExporting_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
uint8_t v_isExporting_boxed_357_; lean_object* v_res_358_; 
v_isExporting_boxed_357_ = lean_unbox(v_isExporting_351_);
v_res_358_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5(v_00_u03b1_349_, v_x_350_, v_isExporting_boxed_357_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(lean_object* v_msgData_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; lean_object* v_env_366_; uint8_t v___x_367_; lean_object* v_env_368_; lean_object* v___x_369_; lean_object* v_toCold_370_; lean_object* v_mctx_371_; lean_object* v_lctx_372_; lean_object* v_options_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_365_ = lean_st_ref_get(v___y_363_);
v_env_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_366_);
lean_dec(v___x_365_);
v___x_367_ = 0;
v_env_368_ = l_Lean_Environment_setRecordingDeps(v_env_366_, v___x_367_);
v___x_369_ = lean_st_ref_get(v___y_361_);
v_toCold_370_ = lean_ctor_get(v___y_362_, 0);
v_mctx_371_ = lean_ctor_get(v___x_369_, 0);
lean_inc_ref(v_mctx_371_);
lean_dec(v___x_369_);
v_lctx_372_ = lean_ctor_get(v___y_360_, 2);
v_options_373_ = lean_ctor_get(v_toCold_370_, 2);
lean_inc_ref(v_options_373_);
lean_inc_ref(v_lctx_372_);
v___x_374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_374_, 0, v_env_368_);
lean_ctor_set(v___x_374_, 1, v_mctx_371_);
lean_ctor_set(v___x_374_, 2, v_lctx_372_);
lean_ctor_set(v___x_374_, 3, v_options_373_);
v___x_375_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v_msgData_359_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0___boxed(lean_object* v_msgData_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msgData_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_ref_390_; lean_object* v___x_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_400_; 
v_ref_390_ = lean_ctor_get(v___y_387_, 2);
v___x_391_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msg_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_400_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
lean_inc(v_ref_390_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_ref_390_);
lean_ctor_set(v___x_396_, 1, v_a_392_);
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 1);
lean_ctor_set(v___x_394_, 0, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg___boxed(lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_407_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__5));
v___x_421_ = l_Lean_stringToMessageData(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__7));
v___x_424_ = l_Lean_stringToMessageData(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0(lean_object* v_declNameNonRec_425_, lean_object* v_xs_426_, lean_object* v_body_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2));
v___x_478_ = lean_unsigned_to_nat(4u);
v___x_479_ = l_Lean_Expr_isAppOfArity(v_body_427_, v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4));
v___x_481_ = l_Lean_Expr_isAppOfArity(v_body_427_, v___x_480_, v___x_478_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
v___x_482_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6);
v___x_483_ = l_Lean_MessageData_ofConstName(v_declNameNonRec_425_, v___x_481_);
v___x_484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = l_Lean_indentExpr(v_body_427_);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_488_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
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
else
{
lean_dec(v_declNameNonRec_425_);
goto v___jp_433_;
}
}
else
{
lean_dec(v_declNameNonRec_425_);
goto v___jp_433_;
}
v___jp_433_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = l_Lean_Expr_appFn_x21(v_body_427_);
lean_dec_ref(v_body_427_);
v___x_435_ = l_Lean_Expr_appArg_x21(v___x_434_);
lean_dec_ref(v___x_434_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
lean_inc_ref(v___x_435_);
v___x_436_ = lean_infer_type(v___x_435_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; uint8_t v___x_438_; uint8_t v___x_439_; uint8_t v___x_440_; lean_object* v___x_441_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_436_, 1);
v___x_438_ = 0;
v___x_439_ = 1;
v___x_440_ = 1;
v___x_441_ = l_Lean_Meta_mkForallFVars(v_xs_426_, v_a_437_, v___x_438_, v___x_439_, v___x_439_, v___x_440_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_443_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v___x_443_ = l_Lean_Meta_mkLambdaFVars(v_xs_426_, v___x_435_, v___x_438_, v___x_439_, v___x_438_, v___x_439_, v___x_440_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_452_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_452_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_a_442_);
lean_ctor_set(v___x_448_, 1, v_a_444_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_448_);
v___x_450_ = v___x_446_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_a_442_);
v_a_453_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_443_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_443_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v___x_435_);
v_a_461_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_441_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_441_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v___x_435_);
v_a_469_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_436_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_436_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___boxed(lean_object* v_declNameNonRec_498_, lean_object* v_xs_499_, lean_object* v_body_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0(v_declNameNonRec_498_, v_xs_499_, v_body_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec_ref(v_xs_499_);
return v_res_506_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0(void){
_start:
{
lean_object* v___x_507_; lean_object* v_dummy_508_; 
v___x_507_ = lean_box(0);
v_dummy_508_ = l_Lean_Expr_sort___override(v___x_507_);
return v_dummy_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1(lean_object* v_declNameNonRec_519_, lean_object* v___x_520_, lean_object* v___x_521_, uint8_t v___x_522_, lean_object* v_xs_523_, lean_object* v_body_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; uint8_t v___x_537_; lean_object* v___y_539_; 
lean_inc(v___x_520_);
v___x_530_ = l_Lean_mkConst(v_declNameNonRec_519_, v___x_520_);
v___x_531_ = l_Lean_mkAppN(v___x_530_, v_xs_523_);
v___x_532_ = l_Lean_mkConst(v___x_521_, v___x_520_);
v___x_533_ = l_Lean_mkAppN(v___x_532_, v_xs_523_);
lean_inc_ref(v___x_531_);
v___x_534_ = l_Lean_Expr_app___override(v___x_533_, v___x_531_);
v___x_535_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2));
v___x_536_ = l_Lean_Expr_isAppOf(v_body_524_, v___x_535_);
v___x_537_ = 1;
if (v___x_536_ == 0)
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2));
v___y_539_ = v___x_589_;
goto v___jp_538_;
}
else
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4));
v___y_539_ = v___x_590_;
goto v___jp_538_;
}
v___jp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_dummy_543_; lean_object* v_nargs_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_540_ = l_Lean_Expr_getAppFn(v_body_524_);
v___x_541_ = l_Lean_Expr_constLevels_x21(v___x_540_);
lean_dec_ref(v___x_540_);
lean_inc(v___y_539_);
v___x_542_ = l_Lean_mkConst(v___y_539_, v___x_541_);
v_dummy_543_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_544_ = l_Lean_Expr_getAppNumArgs(v_body_524_);
lean_inc(v_nargs_544_);
v___x_545_ = lean_mk_array(v_nargs_544_, v_dummy_543_);
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = lean_nat_sub(v_nargs_544_, v___x_546_);
lean_dec(v_nargs_544_);
v___x_548_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_body_524_, v___x_545_, v___x_547_);
v___x_549_ = l_Lean_mkAppN(v___x_542_, v___x_548_);
lean_dec_ref(v___x_548_);
v___x_550_ = l_Lean_Meta_mkEq(v___x_531_, v___x_534_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; uint8_t v___x_552_; lean_object* v___x_553_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = 1;
v___x_553_ = l_Lean_Meta_mkForallFVars(v_xs_523_, v_a_551_, v___x_522_, v___x_537_, v___x_537_, v___x_552_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = l_Lean_Meta_mkLambdaFVars(v_xs_523_, v___x_549_, v___x_522_, v___x_537_, v___x_522_, v___x_537_, v___x_552_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_564_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_564_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v_a_554_);
lean_ctor_set(v___x_560_, 1, v_a_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec(v_a_554_);
v_a_565_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_555_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_555_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
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
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref(v___x_549_);
v_a_573_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_553_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_553_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v___x_549_);
v_a_581_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_550_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_550_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___boxed(lean_object* v_declNameNonRec_591_, lean_object* v___x_592_, lean_object* v___x_593_, lean_object* v___x_594_, lean_object* v_xs_595_, lean_object* v_body_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
uint8_t v___x_10215__boxed_602_; lean_object* v_res_603_; 
v___x_10215__boxed_602_ = lean_unbox(v___x_594_);
v_res_603_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1(v_declNameNonRec_591_, v___x_592_, v___x_593_, v___x_10215__boxed_602_, v_xs_595_, v_body_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v_xs_595_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
if (lean_obj_tag(v_a_604_) == 0)
{
lean_object* v___x_606_; 
v___x_606_ = l_List_reverse___redArg(v_a_605_);
return v___x_606_;
}
else
{
lean_object* v_head_607_; lean_object* v_tail_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_617_; 
v_head_607_ = lean_ctor_get(v_a_604_, 0);
v_tail_608_ = lean_ctor_get(v_a_604_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_617_ == 0)
{
v___x_610_ = v_a_604_;
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_tail_608_);
lean_inc(v_head_607_);
lean_dec(v_a_604_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = l_Lean_mkLevelParam(v_head_607_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 1, v_a_605_);
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_a_605_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
v_a_604_ = v_tail_608_;
v_a_605_ = v___x_614_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_instMonadEIO___redArg();
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(lean_object* v_msg_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_toApplicative_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_692_; 
v___x_629_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0, &l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0);
v___x_630_ = l_StateRefT_x27_instMonad___redArg(v___x_629_);
v_toApplicative_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v___x_630_, 1);
lean_dec(v_unused_693_);
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_692_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_toApplicative_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_692_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_toFunctor_635_; lean_object* v_toSeq_636_; lean_object* v_toSeqLeft_637_; lean_object* v_toSeqRight_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_690_; 
v_toFunctor_635_ = lean_ctor_get(v_toApplicative_631_, 0);
v_toSeq_636_ = lean_ctor_get(v_toApplicative_631_, 2);
v_toSeqLeft_637_ = lean_ctor_get(v_toApplicative_631_, 3);
v_toSeqRight_638_ = lean_ctor_get(v_toApplicative_631_, 4);
v_isSharedCheck_690_ = !lean_is_exclusive(v_toApplicative_631_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; 
v_unused_691_ = lean_ctor_get(v_toApplicative_631_, 1);
lean_dec(v_unused_691_);
v___x_640_ = v_toApplicative_631_;
v_isShared_641_ = v_isSharedCheck_690_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_toSeqRight_638_);
lean_inc(v_toSeqLeft_637_);
lean_inc(v_toSeq_636_);
lean_inc(v_toFunctor_635_);
lean_dec(v_toApplicative_631_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_690_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___f_642_; lean_object* v___f_643_; lean_object* v___f_644_; lean_object* v___f_645_; lean_object* v___x_646_; lean_object* v___f_647_; lean_object* v___f_648_; lean_object* v___f_649_; lean_object* v___x_651_; 
v___f_642_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__1));
v___f_643_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__2));
lean_inc_ref(v_toFunctor_635_);
v___f_644_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_644_, 0, v_toFunctor_635_);
v___f_645_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_645_, 0, v_toFunctor_635_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___f_644_);
lean_ctor_set(v___x_646_, 1, v___f_645_);
v___f_647_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_647_, 0, v_toSeqRight_638_);
v___f_648_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_648_, 0, v_toSeqLeft_637_);
v___f_649_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_649_, 0, v_toSeq_636_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v___f_647_);
lean_ctor_set(v___x_640_, 3, v___f_648_);
lean_ctor_set(v___x_640_, 2, v___f_649_);
lean_ctor_set(v___x_640_, 1, v___f_642_);
lean_ctor_set(v___x_640_, 0, v___x_646_);
v___x_651_ = v___x_640_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___f_642_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v___f_649_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v___f_648_);
lean_ctor_set(v_reuseFailAlloc_689_, 4, v___f_647_);
v___x_651_ = v_reuseFailAlloc_689_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___f_643_);
lean_ctor_set(v___x_633_, 0, v___x_651_);
v___x_653_ = v___x_633_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___f_643_);
v___x_653_ = v_reuseFailAlloc_688_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; lean_object* v_toApplicative_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_686_; 
v___x_654_ = l_StateRefT_x27_instMonad___redArg(v___x_653_);
v_toApplicative_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v___x_654_, 1);
lean_dec(v_unused_687_);
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_686_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_toApplicative_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_686_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_toFunctor_659_; lean_object* v_toSeq_660_; lean_object* v_toSeqLeft_661_; lean_object* v_toSeqRight_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_684_; 
v_toFunctor_659_ = lean_ctor_get(v_toApplicative_655_, 0);
v_toSeq_660_ = lean_ctor_get(v_toApplicative_655_, 2);
v_toSeqLeft_661_ = lean_ctor_get(v_toApplicative_655_, 3);
v_toSeqRight_662_ = lean_ctor_get(v_toApplicative_655_, 4);
v_isSharedCheck_684_ = !lean_is_exclusive(v_toApplicative_655_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v_toApplicative_655_, 1);
lean_dec(v_unused_685_);
v___x_664_ = v_toApplicative_655_;
v_isShared_665_ = v_isSharedCheck_684_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_toSeqRight_662_);
lean_inc(v_toSeqLeft_661_);
lean_inc(v_toSeq_660_);
lean_inc(v_toFunctor_659_);
lean_dec(v_toApplicative_655_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_684_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___f_666_; lean_object* v___f_667_; lean_object* v___f_668_; lean_object* v___f_669_; lean_object* v___x_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___x_675_; 
v___f_666_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__3));
v___f_667_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__4));
lean_inc_ref(v_toFunctor_659_);
v___f_668_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_668_, 0, v_toFunctor_659_);
v___f_669_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_669_, 0, v_toFunctor_659_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___f_668_);
lean_ctor_set(v___x_670_, 1, v___f_669_);
v___f_671_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_671_, 0, v_toSeqRight_662_);
v___f_672_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_672_, 0, v_toSeqLeft_661_);
v___f_673_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_673_, 0, v_toSeq_660_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v___f_671_);
lean_ctor_set(v___x_664_, 3, v___f_672_);
lean_ctor_set(v___x_664_, 2, v___f_673_);
lean_ctor_set(v___x_664_, 1, v___f_666_);
lean_ctor_set(v___x_664_, 0, v___x_670_);
v___x_675_ = v___x_664_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___f_666_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v___f_673_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v___f_672_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v___f_671_);
v___x_675_ = v_reuseFailAlloc_683_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___f_667_);
lean_ctor_set(v___x_657_, 0, v___x_675_);
v___x_677_ = v___x_657_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___f_667_);
v___x_677_ = v_reuseFailAlloc_682_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_9212__overap_680_; lean_object* v___x_681_; 
v___x_678_ = lean_box(0);
v___x_679_ = l_instInhabitedOfMonad___redArg(v___x_677_, v___x_678_);
v___x_9212__overap_680_ = lean_panic_fn_borrowed(v___x_679_, v_msg_623_);
lean_dec(v___x_679_);
lean_inc(v___y_627_);
lean_inc_ref(v___y_626_);
lean_inc(v___y_625_);
lean_inc_ref(v___y_624_);
v___x_681_ = lean_apply_5(v___x_9212__overap_680_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, lean_box(0));
return v___x_681_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___boxed(lean_object* v_msg_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(v_msg_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_700_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__0));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__2));
v___x_706_ = l_Lean_stringToMessageData(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_710_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_711_ = lean_unsigned_to_nat(11u);
v___x_712_ = lean_unsigned_to_nat(115u);
v___x_713_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__5));
v___x_714_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__4));
v___x_715_ = l_mkPanicMessageWithDecl(v___x_714_, v___x_713_, v___x_712_, v___x_711_, v___x_710_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(lean_object* v_constName_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_730_; lean_object* v_env_731_; uint8_t v___x_732_; lean_object* v___x_733_; 
v___x_730_ = lean_st_ref_get(v___y_720_);
v_env_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_ref(v_env_731_);
lean_dec(v___x_730_);
v___x_732_ = 0;
lean_inc(v_constName_716_);
v___x_733_ = l_Lean_Environment_findAsync_x3f(v_env_731_, v_constName_716_, v___x_732_);
if (lean_obj_tag(v___x_733_) == 1)
{
lean_object* v_val_734_; uint8_t v_kind_735_; 
v_val_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_val_734_);
lean_dec_ref_known(v___x_733_, 1);
v_kind_735_ = lean_ctor_get_uint8(v_val_734_, sizeof(void*)*3);
if (v_kind_735_ == 0)
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_734_);
if (lean_obj_tag(v___x_736_) == 1)
{
lean_object* v_val_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_constName_716_);
v_val_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_val_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 0);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_val_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec_ref(v___x_736_);
v___x_745_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7);
v___x_746_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(v___x_745_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_755_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
if (lean_obj_tag(v_a_747_) == 0)
{
lean_del_object(v___x_749_);
goto v___jp_722_;
}
else
{
lean_object* v_val_751_; lean_object* v___x_753_; 
lean_dec(v_constName_716_);
v_val_751_ = lean_ctor_get(v_a_747_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v_a_747_, 1);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v_val_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_val_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_constName_716_);
v_a_756_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_746_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_746_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
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
else
{
lean_dec(v_val_734_);
goto v___jp_722_;
}
}
else
{
lean_dec(v___x_733_);
goto v___jp_722_;
}
v___jp_722_:
{
lean_object* v___x_723_; uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_723_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1);
v___x_724_ = 0;
v___x_725_ = l_Lean_MessageData_ofConstName(v_constName_716_, v___x_724_);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_723_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_728_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___boxed(lean_object* v_constName_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(v_constName_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2(lean_object* v_declNameNonRec_773_, lean_object* v___f_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v_env_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_env_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_780_ = lean_st_ref_get(v___y_778_);
v_env_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_ref(v_env_781_);
lean_dec(v___x_780_);
v___x_782_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__0));
lean_inc_n(v_declNameNonRec_773_, 3);
v___x_783_ = l_Lean_Meta_mkEqLikeNameFor(v_env_781_, v_declNameNonRec_773_, v___x_782_);
v___x_784_ = lean_st_ref_get(v___y_778_);
v_env_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc_ref(v_env_785_);
lean_dec(v___x_784_);
v___x_786_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__1));
v___x_787_ = l_Lean_Meta_mkEqLikeNameFor(v_env_785_, v_declNameNonRec_773_, v___x_786_);
v___x_788_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(v_declNameNonRec_773_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v_toConstantVal_790_; lean_object* v_value_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_920_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v_toConstantVal_790_ = lean_ctor_get(v_a_789_, 0);
v_value_791_ = lean_ctor_get(v_a_789_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_a_789_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; lean_object* v_unused_922_; 
v_unused_921_ = lean_ctor_get(v_a_789_, 3);
lean_dec(v_unused_921_);
v_unused_922_ = lean_ctor_get(v_a_789_, 2);
lean_dec(v_unused_922_);
v___x_793_ = v_a_789_;
v_isShared_794_ = v_isSharedCheck_920_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_value_791_);
lean_inc(v_toConstantVal_790_);
lean_dec(v_a_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_920_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_levelParams_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_917_; 
v_levelParams_795_ = lean_ctor_get(v_toConstantVal_790_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_toConstantVal_790_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; lean_object* v_unused_919_; 
v_unused_918_ = lean_ctor_get(v_toConstantVal_790_, 2);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_toConstantVal_790_, 0);
lean_dec(v_unused_919_);
v___x_797_ = v_toConstantVal_790_;
v_isShared_798_ = v_isSharedCheck_917_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_levelParams_795_);
lean_dec(v_toConstantVal_790_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_917_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___f_803_; lean_object* v___x_804_; 
v___x_799_ = lean_box(0);
lean_inc(v_levelParams_795_);
v___x_800_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(v_levelParams_795_, v___x_799_);
v___x_801_ = 0;
v___x_802_ = lean_box(v___x_801_);
lean_inc(v___x_787_);
v___f_803_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___boxed), 11, 4);
lean_closure_set(v___f_803_, 0, v_declNameNonRec_773_);
lean_closure_set(v___f_803_, 1, v___x_800_);
lean_closure_set(v___f_803_, 2, v___x_787_);
lean_closure_set(v___f_803_, 3, v___x_802_);
lean_inc_ref(v_value_791_);
v___x_804_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_791_, v___f_774_, v___x_801_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v_fst_806_; lean_object* v_snd_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_908_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_804_, 1);
v_fst_806_ = lean_ctor_get(v_a_805_, 0);
v_snd_807_ = lean_ctor_get(v_a_805_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_a_805_);
if (v_isSharedCheck_908_ == 0)
{
v___x_809_ = v_a_805_;
v_isShared_810_ = v_isSharedCheck_908_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_snd_807_);
lean_inc(v_fst_806_);
lean_dec(v_a_805_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_908_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
lean_inc(v_levelParams_795_);
lean_inc(v___x_787_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 2, v_fst_806_);
lean_ctor_set(v___x_797_, 0, v___x_787_);
v___x_812_ = v___x_797_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_levelParams_795_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_fst_806_);
v___x_812_ = v_reuseFailAlloc_907_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_816_; 
v___x_813_ = lean_box(1);
v___x_814_ = 1;
lean_inc(v___x_787_);
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 1);
lean_ctor_set(v___x_809_, 1, v___x_799_);
lean_ctor_set(v___x_809_, 0, v___x_787_);
v___x_816_ = v___x_809_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_799_);
v___x_816_ = v_reuseFailAlloc_906_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 3, v___x_816_);
lean_ctor_set(v___x_793_, 2, v___x_813_);
lean_ctor_set(v___x_793_, 1, v_snd_807_);
lean_ctor_set(v___x_793_, 0, v___x_812_);
v___x_818_ = v___x_793_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_snd_807_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v___x_816_);
v___x_818_ = v_reuseFailAlloc_905_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*4, v___x_814_);
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
v___x_820_ = l_Lean_addDecl(v___x_819_, v___x_801_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_821_; lean_object* v_env_822_; lean_object* v_nextMacroScope_823_; lean_object* v_ngen_824_; lean_object* v_auxDeclNGen_825_; lean_object* v_traceState_826_; lean_object* v_recordedDeps_827_; lean_object* v_messages_828_; lean_object* v_infoState_829_; lean_object* v_snapshotTasks_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref_known(v___x_820_, 1);
v___x_821_ = lean_st_ref_take(v___y_778_);
v_env_822_ = lean_ctor_get(v___x_821_, 0);
v_nextMacroScope_823_ = lean_ctor_get(v___x_821_, 1);
v_ngen_824_ = lean_ctor_get(v___x_821_, 2);
v_auxDeclNGen_825_ = lean_ctor_get(v___x_821_, 3);
v_traceState_826_ = lean_ctor_get(v___x_821_, 4);
v_recordedDeps_827_ = lean_ctor_get(v___x_821_, 6);
v_messages_828_ = lean_ctor_get(v___x_821_, 7);
v_infoState_829_ = lean_ctor_get(v___x_821_, 8);
v_snapshotTasks_830_ = lean_ctor_get(v___x_821_, 9);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v___x_821_, 5);
lean_dec(v_unused_896_);
v___x_832_ = v___x_821_;
v_isShared_833_ = v_isSharedCheck_895_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_snapshotTasks_830_);
lean_inc(v_infoState_829_);
lean_inc(v_messages_828_);
lean_inc(v_recordedDeps_827_);
lean_inc(v_traceState_826_);
lean_inc(v_auxDeclNGen_825_);
lean_inc(v_ngen_824_);
lean_inc(v_nextMacroScope_823_);
lean_inc(v_env_822_);
lean_dec(v___x_821_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_895_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_834_ = l_Lean_addNoncomputable(v_env_822_, v___x_787_);
v___x_835_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 5, v___x_835_);
lean_ctor_set(v___x_832_, 0, v___x_834_);
v___x_837_ = v___x_832_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_nextMacroScope_823_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_ngen_824_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_auxDeclNGen_825_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_traceState_826_);
lean_ctor_set(v_reuseFailAlloc_894_, 5, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_894_, 6, v_recordedDeps_827_);
lean_ctor_set(v_reuseFailAlloc_894_, 7, v_messages_828_);
lean_ctor_set(v_reuseFailAlloc_894_, 8, v_infoState_829_);
lean_ctor_set(v_reuseFailAlloc_894_, 9, v_snapshotTasks_830_);
v___x_837_ = v_reuseFailAlloc_894_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v_mctx_840_; lean_object* v_zetaDeltaFVarIds_841_; lean_object* v_postponed_842_; lean_object* v_diag_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_892_; 
v___x_838_ = lean_st_ref_put(v___y_778_, v___x_837_);
v___x_839_ = lean_st_ref_take(v___y_776_);
v_mctx_840_ = lean_ctor_get(v___x_839_, 0);
v_zetaDeltaFVarIds_841_ = lean_ctor_get(v___x_839_, 2);
v_postponed_842_ = lean_ctor_get(v___x_839_, 3);
v_diag_843_ = lean_ctor_get(v___x_839_, 4);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v___x_839_, 1);
lean_dec(v_unused_893_);
v___x_845_ = v___x_839_;
v_isShared_846_ = v_isSharedCheck_892_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_diag_843_);
lean_inc(v_postponed_842_);
lean_inc(v_zetaDeltaFVarIds_841_);
lean_inc(v_mctx_840_);
lean_dec(v___x_839_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_892_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v___x_847_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_mctx_840_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_zetaDeltaFVarIds_841_);
lean_ctor_set(v_reuseFailAlloc_891_, 3, v_postponed_842_);
lean_ctor_set(v_reuseFailAlloc_891_, 4, v_diag_843_);
v___x_849_ = v_reuseFailAlloc_891_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_st_ref_put(v___y_776_, v___x_849_);
v___x_851_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_791_, v___f_803_, v___x_801_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v_fst_853_; lean_object* v_snd_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_882_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
v_fst_853_ = lean_ctor_get(v_a_852_, 0);
v_snd_854_ = lean_ctor_get(v_a_852_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_a_852_);
if (v_isSharedCheck_882_ == 0)
{
v___x_856_ = v_a_852_;
v_isShared_857_ = v_isSharedCheck_882_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_snd_854_);
lean_inc(v_fst_853_);
lean_dec(v_a_852_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_882_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_inc_n(v___x_783_, 2);
v___x_858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_858_, 0, v___x_783_);
lean_ctor_set(v___x_858_, 1, v_levelParams_795_);
lean_ctor_set(v___x_858_, 2, v_fst_853_);
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 1);
lean_ctor_set(v___x_856_, 1, v___x_799_);
lean_ctor_set(v___x_856_, 0, v___x_783_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_799_);
v___x_860_ = v_reuseFailAlloc_881_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_a_863_; lean_object* v___x_864_; 
v___x_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_861_, 0, v___x_858_);
lean_ctor_set(v___x_861_, 1, v_snd_854_);
lean_ctor_set(v___x_861_, 2, v___x_860_);
v___x_862_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v___x_861_, v___y_778_);
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_862_);
v___x_864_ = l_Lean_addDecl(v_a_863_, v___x_801_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_872_);
v___x_866_ = v___x_864_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_dec(v___x_864_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_783_);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_783_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v___x_783_);
v_a_873_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_864_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_864_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec(v_levelParams_795_);
lean_dec(v___x_783_);
v_a_883_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_851_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_851_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
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
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v___f_803_);
lean_dec(v_levelParams_795_);
lean_dec_ref(v_value_791_);
lean_dec(v___x_787_);
lean_dec(v___x_783_);
v_a_897_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_820_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_820_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
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
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v___f_803_);
lean_del_object(v___x_797_);
lean_dec(v_levelParams_795_);
lean_del_object(v___x_793_);
lean_dec_ref(v_value_791_);
lean_dec(v___x_787_);
lean_dec(v___x_783_);
v_a_909_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_804_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_804_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
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
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v___x_787_);
lean_dec(v___x_783_);
lean_dec_ref(v___f_774_);
lean_dec(v_declNameNonRec_773_);
v_a_923_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_788_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_788_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___boxed(lean_object* v_declNameNonRec_931_, lean_object* v___f_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2(v_declNameNonRec_931_, v___f_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(lean_object* v_declNameNonRec_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___f_945_; lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v_env_948_; uint8_t v___x_949_; lean_object* v___x_950_; 
lean_inc_n(v_declNameNonRec_939_, 2);
v___f_945_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___boxed), 8, 1);
lean_closure_set(v___f_945_, 0, v_declNameNonRec_939_);
v___f_946_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___boxed), 7, 2);
lean_closure_set(v___f_946_, 0, v_declNameNonRec_939_);
lean_closure_set(v___f_946_, 1, v___f_945_);
v___x_947_ = lean_st_ref_get(v_a_943_);
v_env_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc_ref(v_env_948_);
lean_dec(v___x_947_);
v___x_949_ = l_Lean_Environment_hasExposedBody(v_env_948_, v_declNameNonRec_939_);
v___x_950_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v___f_946_, v___x_949_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___boxed(lean_object* v_declNameNonRec_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(v_declNameNonRec_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0(lean_object* v_00_u03b1_958_, lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v_msg_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___boxed(lean_object* v_00_u03b1_966_, lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0(v_00_u03b1_966_, v_msg_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t v___x_974_, uint8_t v___x_975_, uint8_t v_____do__lift_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
if (v_____do__lift_976_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_box(v___x_974_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_box(v___x_975_);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object* v___x_986_, lean_object* v___x_987_, lean_object* v_____do__lift_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
uint8_t v___x_4220__boxed_994_; uint8_t v___x_4221__boxed_995_; uint8_t v_____do__lift_4222__boxed_996_; lean_object* v_res_997_; 
v___x_4220__boxed_994_ = lean_unbox(v___x_986_);
v___x_4221__boxed_995_ = lean_unbox(v___x_987_);
v_____do__lift_4222__boxed_996_ = lean_unbox(v_____do__lift_988_);
v_res_997_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_4220__boxed_994_, v___x_4221__boxed_995_, v_____do__lift_4222__boxed_996_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
return v_res_997_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object* v_as_998_, size_t v_i_999_, size_t v_stop_1000_){
_start:
{
uint8_t v___x_1001_; 
v___x_1001_ = lean_usize_dec_eq(v_i_999_, v_stop_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; uint8_t v_kind_1003_; uint8_t v___x_1004_; 
v___x_1002_ = lean_array_uget_borrowed(v_as_998_, v_i_999_);
v_kind_1003_ = lean_ctor_get_uint8(v___x_1002_, sizeof(void*)*9);
v___x_1004_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1003_);
if (v___x_1004_ == 0)
{
uint8_t v___x_1005_; 
v___x_1005_ = 1;
return v___x_1005_;
}
else
{
size_t v___x_1006_; size_t v___x_1007_; 
v___x_1006_ = ((size_t)1ULL);
v___x_1007_ = lean_usize_add(v_i_999_, v___x_1006_);
v_i_999_ = v___x_1007_;
goto _start;
}
}
else
{
uint8_t v___x_1009_; 
v___x_1009_ = 0;
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object* v_as_1010_, lean_object* v_i_1011_, lean_object* v_stop_1012_){
_start:
{
size_t v_i_boxed_1013_; size_t v_stop_boxed_1014_; uint8_t v_res_1015_; lean_object* v_r_1016_; 
v_i_boxed_1013_ = lean_unbox_usize(v_i_1011_);
lean_dec(v_i_1011_);
v_stop_boxed_1014_ = lean_unbox_usize(v_stop_1012_);
lean_dec(v_stop_1012_);
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_as_1010_, v_i_boxed_1013_, v_stop_boxed_1014_);
lean_dec_ref(v_as_1010_);
v_r_1016_ = lean_box(v_res_1015_);
return v_r_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t v_sz_1017_, size_t v_i_1018_, lean_object* v_bs_1019_){
_start:
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_usize_dec_lt(v_i_1018_, v_sz_1017_);
if (v___x_1020_ == 0)
{
return v_bs_1019_;
}
else
{
lean_object* v_v_1021_; lean_object* v_declName_1022_; lean_object* v___x_1023_; lean_object* v_bs_x27_1024_; size_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
v_v_1021_ = lean_array_uget_borrowed(v_bs_1019_, v_i_1018_);
v_declName_1022_ = lean_ctor_get(v_v_1021_, 3);
lean_inc(v_declName_1022_);
v___x_1023_ = lean_unsigned_to_nat(0u);
v_bs_x27_1024_ = lean_array_uset(v_bs_1019_, v_i_1018_, v___x_1023_);
v___x_1025_ = ((size_t)1ULL);
v___x_1026_ = lean_usize_add(v_i_1018_, v___x_1025_);
v___x_1027_ = lean_array_uset(v_bs_x27_1024_, v_i_1018_, v_declName_1022_);
v_i_1018_ = v___x_1026_;
v_bs_1019_ = v___x_1027_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object* v_sz_1029_, lean_object* v_i_1030_, lean_object* v_bs_1031_){
_start:
{
size_t v_sz_boxed_1032_; size_t v_i_boxed_1033_; lean_object* v_res_1034_; 
v_sz_boxed_1032_ = lean_unbox_usize(v_sz_1029_);
lean_dec(v_sz_1029_);
v_i_boxed_1033_ = lean_unbox_usize(v_i_1030_);
lean_dec(v_i_1030_);
v_res_1034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_boxed_1032_, v_i_boxed_1033_, v_bs_1031_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object* v___x_1035_, lean_object* v_declNameNonRec_1036_, lean_object* v_fixedParamPerms_1037_, lean_object* v_fixpointType_1038_, lean_object* v_fixEq_x3f_1039_, uint8_t v_a_1040_, lean_object* v_as_1041_, size_t v_i_1042_, size_t v_stop_1043_, lean_object* v_b_1044_){
_start:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_usize_dec_eq(v_i_1042_, v_stop_1043_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v_levelParams_1047_; lean_object* v_declName_1048_; lean_object* v_type_1049_; lean_object* v_value_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; 
v___x_1046_ = lean_array_uget_borrowed(v_as_1041_, v_i_1042_);
v_levelParams_1047_ = lean_ctor_get(v___x_1046_, 1);
v_declName_1048_ = lean_ctor_get(v___x_1046_, 3);
v_type_1049_ = lean_ctor_get(v___x_1046_, 6);
v_value_1050_ = lean_ctor_get(v___x_1046_, 7);
v___x_1051_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
lean_inc(v_fixEq_x3f_1039_);
lean_inc_ref(v_fixpointType_1038_);
lean_inc_ref(v_fixedParamPerms_1037_);
lean_inc(v_declNameNonRec_1036_);
lean_inc_ref(v___x_1035_);
lean_inc_ref(v_value_1050_);
lean_inc_ref(v_type_1049_);
lean_inc(v_levelParams_1047_);
lean_inc_n(v_declName_1048_, 2);
v___x_1052_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1052_, 0, v_declName_1048_);
lean_ctor_set(v___x_1052_, 1, v_levelParams_1047_);
lean_ctor_set(v___x_1052_, 2, v_type_1049_);
lean_ctor_set(v___x_1052_, 3, v_value_1050_);
lean_ctor_set(v___x_1052_, 4, v___x_1035_);
lean_ctor_set(v___x_1052_, 5, v_declNameNonRec_1036_);
lean_ctor_set(v___x_1052_, 6, v_fixedParamPerms_1037_);
lean_ctor_set(v___x_1052_, 7, v_fixpointType_1038_);
lean_ctor_set(v___x_1052_, 8, v_fixEq_x3f_1039_);
v___x_1053_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1051_, v_b_1044_, v_declName_1048_, v___x_1052_, v_a_1040_);
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_add(v_i_1042_, v___x_1054_);
v_i_1042_ = v___x_1055_;
v_b_1044_ = v___x_1053_;
goto _start;
}
else
{
lean_dec(v_fixEq_x3f_1039_);
lean_dec_ref(v_fixpointType_1038_);
lean_dec_ref(v_fixedParamPerms_1037_);
lean_dec(v_declNameNonRec_1036_);
lean_dec_ref(v___x_1035_);
return v_b_1044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object* v___x_1057_, lean_object* v_declNameNonRec_1058_, lean_object* v_fixedParamPerms_1059_, lean_object* v_fixpointType_1060_, lean_object* v_fixEq_x3f_1061_, lean_object* v_a_1062_, lean_object* v_as_1063_, lean_object* v_i_1064_, lean_object* v_stop_1065_, lean_object* v_b_1066_){
_start:
{
uint8_t v_a_4281__boxed_1067_; size_t v_i_boxed_1068_; size_t v_stop_boxed_1069_; lean_object* v_res_1070_; 
v_a_4281__boxed_1067_ = lean_unbox(v_a_1062_);
v_i_boxed_1068_ = lean_unbox_usize(v_i_1064_);
lean_dec(v_i_1064_);
v_stop_boxed_1069_ = lean_unbox_usize(v_stop_1065_);
lean_dec(v_stop_1065_);
v_res_1070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_1057_, v_declNameNonRec_1058_, v_fixedParamPerms_1059_, v_fixpointType_1060_, v_fixEq_x3f_1061_, v_a_4281__boxed_1067_, v_as_1063_, v_i_boxed_1068_, v_stop_boxed_1069_, v_b_1066_);
lean_dec_ref(v_as_1063_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object* v_as_1071_, size_t v_i_1072_, size_t v_stop_1073_, lean_object* v_b_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_eq(v_i_1072_, v_stop_1073_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v_declName_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_array_uget_borrowed(v_as_1071_, v_i_1072_);
v_declName_1080_ = lean_ctor_get(v___x_1079_, 3);
lean_inc(v_declName_1080_);
v___x_1081_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_1080_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; size_t v___x_1083_; size_t v___x_1084_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_1072_, v___x_1083_);
v_i_1072_ = v___x_1084_;
v_b_1074_ = v_a_1082_;
goto _start;
}
else
{
return v___x_1081_;
}
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_b_1074_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object* v_as_1087_, lean_object* v_i_1088_, lean_object* v_stop_1089_, lean_object* v_b_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
size_t v_i_boxed_1094_; size_t v_stop_boxed_1095_; lean_object* v_res_1096_; 
v_i_boxed_1094_ = lean_unbox_usize(v_i_1088_);
lean_dec(v_i_1088_);
v_stop_boxed_1095_ = lean_unbox_usize(v_stop_1089_);
lean_dec(v_stop_1089_);
v_res_1096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_1087_, v_i_boxed_1094_, v_stop_boxed_1095_, v_b_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec_ref(v_as_1087_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t v___x_1097_, lean_object* v_as_1098_, size_t v_i_1099_, size_t v_stop_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_usize_dec_eq(v_i_1099_, v_stop_1100_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v_type_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; 
v___x_1111_ = lean_array_uget_borrowed(v_as_1098_, v_i_1099_);
v_type_1112_ = lean_ctor_get(v___x_1111_, 6);
v___x_1113_ = 1;
lean_inc_ref(v_type_1112_);
v___x_1114_ = l_Lean_Meta_isProp(v_type_1112_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1124_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_unbox(v_a_1115_);
lean_dec(v_a_1115_);
if (v___x_1119_ == 0)
{
if (v___x_1097_ == 0)
{
lean_del_object(v___x_1117_);
goto v___jp_1106_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = lean_box(v___x_1113_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1120_);
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_del_object(v___x_1117_);
goto v___jp_1106_;
}
}
}
else
{
return v___x_1114_;
}
}
else
{
uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = 0;
v___x_1126_ = lean_box(v___x_1125_);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
v___jp_1106_:
{
size_t v___x_1107_; size_t v___x_1108_; 
v___x_1107_ = ((size_t)1ULL);
v___x_1108_ = lean_usize_add(v_i_1099_, v___x_1107_);
v_i_1099_ = v___x_1108_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object* v___x_1128_, lean_object* v_as_1129_, lean_object* v_i_1130_, lean_object* v_stop_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v___x_4328__boxed_1137_; size_t v_i_boxed_1138_; size_t v_stop_boxed_1139_; lean_object* v_res_1140_; 
v___x_4328__boxed_1137_ = lean_unbox(v___x_1128_);
v_i_boxed_1138_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_stop_boxed_1139_ = lean_unbox_usize(v_stop_1131_);
lean_dec(v_stop_1131_);
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_4328__boxed_1137_, v_as_1129_, v_i_boxed_1138_, v_stop_boxed_1139_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v_as_1129_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object* v_preDefs_1141_, lean_object* v_declNameNonRec_1142_, lean_object* v_fixedParamPerms_1143_, lean_object* v_fixpointType_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v_nextMacroScope_1156_; lean_object* v_ngen_1157_; lean_object* v_auxDeclNGen_1158_; lean_object* v_traceState_1159_; lean_object* v_recordedDeps_1160_; lean_object* v_messages_1161_; lean_object* v_infoState_1162_; lean_object* v_snapshotTasks_1163_; lean_object* v___y_1164_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; size_t v___y_1192_; lean_object* v___y_1193_; uint8_t v___y_1194_; lean_object* v_fixEq_x3f_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1212_; uint8_t v___x_1260_; 
v___x_1188_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = lean_array_get_size(v_preDefs_1141_);
v___x_1260_ = lean_nat_dec_lt(v___x_1189_, v___x_1190_);
if (v___x_1260_ == 0)
{
goto v___jp_1241_;
}
else
{
lean_object* v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = ((size_t)0ULL);
v___x_1263_ = lean_usize_of_nat(v___x_1190_);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_1141_, v___x_1262_, v___x_1263_, v___x_1261_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_dec_ref_known(v___x_1264_, 1);
goto v___jp_1241_;
}
else
{
lean_dec_ref(v_fixpointType_1144_);
lean_dec_ref(v_fixedParamPerms_1143_);
lean_dec(v_declNameNonRec_1142_);
lean_dec_ref(v_preDefs_1141_);
return v___x_1264_;
}
}
v___jp_1150_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_box(0);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
v___jp_1153_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v_mctx_1169_; lean_object* v_zetaDeltaFVarIds_1170_; lean_object* v_postponed_1171_; lean_object* v_diag_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1183_; 
v___x_1165_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
v___x_1166_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1166_, 0, v___y_1164_);
lean_ctor_set(v___x_1166_, 1, v_nextMacroScope_1156_);
lean_ctor_set(v___x_1166_, 2, v_ngen_1157_);
lean_ctor_set(v___x_1166_, 3, v_auxDeclNGen_1158_);
lean_ctor_set(v___x_1166_, 4, v_traceState_1159_);
lean_ctor_set(v___x_1166_, 5, v___x_1165_);
lean_ctor_set(v___x_1166_, 6, v_recordedDeps_1160_);
lean_ctor_set(v___x_1166_, 7, v_messages_1161_);
lean_ctor_set(v___x_1166_, 8, v_infoState_1162_);
lean_ctor_set(v___x_1166_, 9, v_snapshotTasks_1163_);
v___x_1167_ = lean_st_ref_put(v___y_1154_, v___x_1166_);
v___x_1168_ = lean_st_ref_take(v___y_1155_);
v_mctx_1169_ = lean_ctor_get(v___x_1168_, 0);
v_zetaDeltaFVarIds_1170_ = lean_ctor_get(v___x_1168_, 2);
v_postponed_1171_ = lean_ctor_get(v___x_1168_, 3);
v_diag_1172_ = lean_ctor_get(v___x_1168_, 4);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; 
v_unused_1184_ = lean_ctor_get(v___x_1168_, 1);
lean_dec(v_unused_1184_);
v___x_1174_ = v___x_1168_;
v_isShared_1175_ = v_isSharedCheck_1183_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_diag_1172_);
lean_inc(v_postponed_1171_);
lean_inc(v_zetaDeltaFVarIds_1170_);
lean_inc(v_mctx_1169_);
lean_dec(v___x_1168_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1183_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1177_);
v___x_1179_ = v___x_1174_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_mctx_1169_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_zetaDeltaFVarIds_1170_);
lean_ctor_set(v_reuseFailAlloc_1182_, 3, v_postponed_1171_);
lean_ctor_set(v_reuseFailAlloc_1182_, 4, v_diag_1172_);
v___x_1179_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_st_ref_put(v___y_1155_, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1176_);
return v___x_1181_;
}
}
}
v___jp_1185_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_box(0);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
v___jp_1191_:
{
lean_object* v___x_1198_; lean_object* v_env_1199_; lean_object* v_nextMacroScope_1200_; lean_object* v_ngen_1201_; lean_object* v_auxDeclNGen_1202_; lean_object* v_traceState_1203_; lean_object* v_recordedDeps_1204_; lean_object* v_messages_1205_; lean_object* v_infoState_1206_; lean_object* v_snapshotTasks_1207_; uint8_t v___x_1208_; 
v___x_1198_ = lean_st_ref_take(v___y_1197_);
v_env_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc_ref(v_env_1199_);
v_nextMacroScope_1200_ = lean_ctor_get(v___x_1198_, 1);
lean_inc(v_nextMacroScope_1200_);
v_ngen_1201_ = lean_ctor_get(v___x_1198_, 2);
lean_inc_ref(v_ngen_1201_);
v_auxDeclNGen_1202_ = lean_ctor_get(v___x_1198_, 3);
lean_inc_ref(v_auxDeclNGen_1202_);
v_traceState_1203_ = lean_ctor_get(v___x_1198_, 4);
lean_inc_ref(v_traceState_1203_);
v_recordedDeps_1204_ = lean_ctor_get(v___x_1198_, 6);
lean_inc_ref(v_recordedDeps_1204_);
v_messages_1205_ = lean_ctor_get(v___x_1198_, 7);
lean_inc_ref(v_messages_1205_);
v_infoState_1206_ = lean_ctor_get(v___x_1198_, 8);
lean_inc_ref(v_infoState_1206_);
v_snapshotTasks_1207_ = lean_ctor_get(v___x_1198_, 9);
lean_inc_ref(v_snapshotTasks_1207_);
lean_dec(v___x_1198_);
v___x_1208_ = lean_nat_dec_lt(v___x_1189_, v___x_1190_);
if (v___x_1208_ == 0)
{
lean_dec(v_fixEq_x3f_1195_);
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_fixpointType_1144_);
lean_dec_ref(v_fixedParamPerms_1143_);
lean_dec(v_declNameNonRec_1142_);
lean_dec_ref(v_preDefs_1141_);
v___y_1154_ = v___y_1197_;
v___y_1155_ = v___y_1196_;
v_nextMacroScope_1156_ = v_nextMacroScope_1200_;
v_ngen_1157_ = v_ngen_1201_;
v_auxDeclNGen_1158_ = v_auxDeclNGen_1202_;
v_traceState_1159_ = v_traceState_1203_;
v_recordedDeps_1160_ = v_recordedDeps_1204_;
v_messages_1161_ = v_messages_1205_;
v_infoState_1162_ = v_infoState_1206_;
v_snapshotTasks_1163_ = v_snapshotTasks_1207_;
v___y_1164_ = v_env_1199_;
goto v___jp_1153_;
}
else
{
size_t v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_usize_of_nat(v___x_1190_);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___y_1193_, v_declNameNonRec_1142_, v_fixedParamPerms_1143_, v_fixpointType_1144_, v_fixEq_x3f_1195_, v___y_1194_, v_preDefs_1141_, v___y_1192_, v___x_1209_, v_env_1199_);
lean_dec_ref(v_preDefs_1141_);
v___y_1154_ = v___y_1197_;
v___y_1155_ = v___y_1196_;
v_nextMacroScope_1156_ = v_nextMacroScope_1200_;
v_ngen_1157_ = v_ngen_1201_;
v_auxDeclNGen_1158_ = v_auxDeclNGen_1202_;
v_traceState_1159_ = v_traceState_1203_;
v_recordedDeps_1160_ = v_recordedDeps_1204_;
v_messages_1161_ = v_messages_1205_;
v_infoState_1162_ = v_infoState_1206_;
v_snapshotTasks_1163_ = v_snapshotTasks_1207_;
v___y_1164_ = v___x_1210_;
goto v___jp_1153_;
}
}
v___jp_1211_:
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1240_; 
v_a_1213_ = lean_ctor_get(v___y_1212_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___y_1212_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1215_ = v___y_1212_;
v_isShared_1216_ = v_isSharedCheck_1240_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___y_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1240_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_unbox(v_a_1213_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v_declName_1219_; size_t v_sz_1220_; size_t v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1218_ = lean_array_get_borrowed(v___x_1188_, v_preDefs_1141_, v___x_1189_);
v_declName_1219_ = lean_ctor_get(v___x_1218_, 3);
v_sz_1220_ = lean_array_size(v_preDefs_1141_);
v___x_1221_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_1141_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_1220_, v___x_1221_, v_preDefs_1141_);
v___x_1223_ = lean_name_eq(v_declNameNonRec_1142_, v_declName_1219_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_inc(v_declNameNonRec_1142_);
v___x_1224_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(v_declNameNonRec_1142_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
if (v_isShared_1216_ == 0)
{
lean_ctor_set_tag(v___x_1215_, 1);
lean_ctor_set(v___x_1215_, 0, v_a_1225_);
v___x_1227_ = v___x_1215_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1225_);
v___x_1227_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
uint8_t v___x_1228_; 
v___x_1228_ = lean_unbox(v_a_1213_);
lean_dec(v_a_1213_);
v___y_1192_ = v___x_1221_;
v___y_1193_ = v___x_1222_;
v___y_1194_ = v___x_1228_;
v_fixEq_x3f_1195_ = v___x_1227_;
v___y_1196_ = v_a_1146_;
v___y_1197_ = v_a_1148_;
goto v___jp_1191_;
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v___x_1222_);
lean_del_object(v___x_1215_);
lean_dec(v_a_1213_);
lean_dec_ref(v_fixpointType_1144_);
lean_dec_ref(v_fixedParamPerms_1143_);
lean_dec(v_declNameNonRec_1142_);
lean_dec_ref(v_preDefs_1141_);
v_a_1230_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1224_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1224_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
lean_del_object(v___x_1215_);
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_unbox(v_a_1213_);
lean_dec(v_a_1213_);
v___y_1192_ = v___x_1221_;
v___y_1193_ = v___x_1222_;
v___y_1194_ = v___x_1239_;
v_fixEq_x3f_1195_ = v___x_1238_;
v___y_1196_ = v_a_1146_;
v___y_1197_ = v_a_1148_;
goto v___jp_1191_;
}
}
else
{
lean_del_object(v___x_1215_);
lean_dec(v_a_1213_);
lean_dec_ref(v_fixpointType_1144_);
lean_dec_ref(v_fixedParamPerms_1143_);
lean_dec(v_declNameNonRec_1142_);
lean_dec_ref(v_preDefs_1141_);
goto v___jp_1150_;
}
}
}
v___jp_1241_:
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_nat_dec_lt(v___x_1189_, v___x_1190_);
if (v___x_1242_ == 0)
{
lean_dec_ref(v_fixpointType_1144_);
lean_dec_ref(v_fixedParamPerms_1143_);
lean_dec(v_declNameNonRec_1142_);
lean_dec_ref(v_preDefs_1141_);
goto v___jp_1185_;
}
else
{
if (v___x_1242_ == 0)
{
lean_dec_ref(v_fixpointType_1144_);
lean_dec_ref(v_fixedParamPerms_1143_);
lean_dec(v_declNameNonRec_1142_);
lean_dec_ref(v_preDefs_1141_);
goto v___jp_1185_;
}
else
{
size_t v___x_1243_; size_t v___x_1244_; uint8_t v___x_1245_; 
v___x_1243_ = ((size_t)0ULL);
v___x_1244_ = lean_usize_of_nat(v___x_1190_);
v___x_1245_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_preDefs_1141_, v___x_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_dec_ref(v_fixpointType_1144_);
lean_dec_ref(v_fixedParamPerms_1143_);
lean_dec(v_declNameNonRec_1142_);
lean_dec_ref(v_preDefs_1141_);
goto v___jp_1185_;
}
else
{
uint8_t v___x_1246_; 
v___x_1246_ = 0;
if (v___x_1242_ == 0)
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_1245_, v___x_1246_, v___x_1242_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
v___y_1212_ = v___x_1247_;
goto v___jp_1211_;
}
else
{
if (v___x_1242_ == 0)
{
lean_dec_ref(v_fixpointType_1144_);
lean_dec_ref(v_fixedParamPerms_1143_);
lean_dec(v_declNameNonRec_1142_);
lean_dec_ref(v_preDefs_1141_);
goto v___jp_1150_;
}
else
{
lean_object* v___x_1248_; 
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_1245_, v_preDefs_1141_, v___x_1243_, v___x_1244_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1250_ = lean_unbox(v_a_1249_);
lean_dec(v_a_1249_);
v___x_1251_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_1245_, v___x_1246_, v___x_1250_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
v___y_1212_ = v___x_1251_;
goto v___jp_1211_;
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_fixpointType_1144_);
lean_dec_ref(v_fixedParamPerms_1143_);
lean_dec(v_declNameNonRec_1142_);
lean_dec_ref(v_preDefs_1141_);
v_a_1252_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1248_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1248_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(lean_object* v_preDefs_1265_, lean_object* v_declNameNonRec_1266_, lean_object* v_fixedParamPerms_1267_, lean_object* v_fixpointType_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_preDefs_1265_, v_declNameNonRec_1266_, v_fixedParamPerms_1267_, v_fixpointType_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object* v_as_1275_, size_t v_i_1276_, size_t v_stop_1277_, lean_object* v_b_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_1275_, v_i_1276_, v_stop_1277_, v_b_1278_, v___y_1281_, v___y_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object* v_as_1285_, lean_object* v_i_1286_, lean_object* v_stop_1287_, lean_object* v_b_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
size_t v_i_boxed_1294_; size_t v_stop_boxed_1295_; lean_object* v_res_1296_; 
v_i_boxed_1294_ = lean_unbox_usize(v_i_1286_);
lean_dec(v_i_1286_);
v_stop_boxed_1295_ = lean_unbox_usize(v_stop_1287_);
lean_dec(v_stop_1287_);
v_res_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(v_as_1285_, v_i_boxed_1294_, v_stop_boxed_1295_, v_b_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec_ref(v_as_1285_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(lean_object* v_mvarId_1297_, lean_object* v_x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1297_, v_x_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_a_1313_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1304_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1304_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg___boxed(lean_object* v_mvarId_1321_, lean_object* v_x_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1321_, v_x_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(lean_object* v_00_u03b1_1329_, lean_object* v_mvarId_1330_, lean_object* v_x_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1330_, v_x_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(lean_object* v_00_u03b1_1338_, lean_object* v_mvarId_1339_, lean_object* v_x_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(v_00_u03b1_1338_, v_mvarId_1339_, v_x_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
return v_res_1346_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object* v_declName_1347_, lean_object* v_declNameNonRec_1348_, lean_object* v_n_1349_){
_start:
{
uint8_t v___x_1350_; 
v___x_1350_ = lean_name_eq(v_n_1349_, v_declName_1347_);
if (v___x_1350_ == 0)
{
uint8_t v___x_1351_; 
v___x_1351_ = lean_name_eq(v_n_1349_, v_declNameNonRec_1348_);
return v___x_1351_;
}
else
{
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object* v_declName_1352_, lean_object* v_declNameNonRec_1353_, lean_object* v_n_1354_){
_start:
{
uint8_t v_res_1355_; lean_object* v_r_1356_; 
v_res_1355_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(v_declName_1352_, v_declNameNonRec_1353_, v_n_1354_);
lean_dec(v_n_1354_);
lean_dec(v_declNameNonRec_1353_);
lean_dec(v_declName_1352_);
v_r_1356_ = lean_box(v_res_1355_);
return v_r_1356_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5));
v___x_1367_ = l_Lean_MessageData_ofFormat(v___x_1366_);
return v___x_1367_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6);
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object* v_mvarId_1370_, lean_object* v___f_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; 
lean_inc(v_mvarId_1370_);
v___x_1377_ = l_Lean_MVarId_getType_x27(v_mvarId_1370_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_1380_ = lean_unsigned_to_nat(3u);
v___x_1381_ = l_Lean_Expr_isAppOfArity(v_a_1378_, v___x_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec(v_a_1378_);
lean_dec_ref(v___f_1371_);
v___x_1382_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3));
v___x_1383_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7);
v___x_1384_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1382_, v_mvarId_1370_, v___x_1383_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
return v___x_1384_;
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1385_ = l_Lean_Expr_appFn_x21(v_a_1378_);
v___x_1386_ = l_Lean_Expr_appArg_x21(v___x_1385_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = l_Lean_Expr_appArg_x21(v_a_1378_);
lean_dec(v_a_1378_);
v___x_1388_ = 0;
v___x_1389_ = l_Lean_Meta_deltaExpand(v___x_1386_, v___f_1371_, v___x_1388_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = l_Lean_Meta_mkEq(v_a_1390_, v___x_1387_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1370_, v_a_1392_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
return v___x_1393_;
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_mvarId_1370_);
v_a_1394_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1391_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1391_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec_ref(v___x_1387_);
lean_dec(v_mvarId_1370_);
v_a_1402_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1389_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1389_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec_ref(v___f_1371_);
lean_dec(v_mvarId_1370_);
v_a_1410_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1377_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1377_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed(lean_object* v_mvarId_1418_, lean_object* v___f_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(v_mvarId_1418_, v___f_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object* v_declName_1426_, lean_object* v_declNameNonRec_1427_, lean_object* v_mvarId_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v___f_1434_; lean_object* v___f_1435_; lean_object* v___x_1436_; 
v___f_1434_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1434_, 0, v_declName_1426_);
lean_closure_set(v___f_1434_, 1, v_declNameNonRec_1427_);
lean_inc(v_mvarId_1428_);
v___f_1435_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1435_, 0, v_mvarId_1428_);
lean_closure_set(v___f_1435_, 1, v___f_1434_);
v___x_1436_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1428_, v___f_1435_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(lean_object* v_declName_1437_, lean_object* v_declNameNonRec_1438_, lean_object* v_mvarId_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_1437_, v_declNameNonRec_1438_, v_mvarId_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(lean_object* v_msg_1446_){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = l_Lean_instInhabitedExpr;
v___x_1448_ = lean_panic_fn_borrowed(v___x_1447_, v_msg_1446_);
return v___x_1448_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0));
v___x_1451_ = l_Lean_stringToMessageData(v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = l_Lean_Expr_bvar___override(v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1463_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9));
v___x_1464_ = lean_unsigned_to_nat(18u);
v___x_1465_ = lean_unsigned_to_nat(1919u);
v___x_1466_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8));
v___x_1467_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7));
v___x_1468_ = l_mkPanicMessageWithDecl(v___x_1467_, v___x_1466_, v___x_1465_, v___x_1464_, v___x_1463_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(lean_object* v_lhs_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1478_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2));
v___x_1479_ = lean_unsigned_to_nat(4u);
v___x_1480_ = l_Lean_Expr_isAppOfArity(v_lhs_1472_, v___x_1478_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4));
v___x_1482_ = l_Lean_Expr_isAppOfArity(v_lhs_1472_, v___x_1481_, v___x_1479_);
if (v___x_1482_ == 0)
{
uint8_t v___x_1483_; 
v___x_1483_ = l_Lean_Expr_isApp(v_lhs_1472_);
if (v___x_1483_ == 0)
{
uint8_t v___x_1484_; 
v___x_1484_ = l_Lean_Expr_isProj(v_lhs_1472_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1485_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1);
v___x_1486_ = l_Lean_MessageData_ofExpr(v_lhs_1472_);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_1487_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
return v___x_1488_;
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = l_Lean_Expr_projExpr_x21(v_lhs_1472_);
lean_inc(v_a_1476_);
lean_inc_ref(v_a_1475_);
lean_inc(v_a_1474_);
lean_inc_ref(v_a_1473_);
lean_inc_ref(v___x_1489_);
v___x_1490_ = lean_infer_type(v___x_1489_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; lean_object* v___y_1495_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v___x_1492_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3));
v___x_1493_ = 0;
if (lean_obj_tag(v_lhs_1472_) == 11)
{
lean_object* v_typeName_1505_; lean_object* v_idx_1506_; lean_object* v_struct_1507_; lean_object* v___x_1508_; size_t v___x_1509_; size_t v___x_1510_; uint8_t v___x_1511_; 
v_typeName_1505_ = lean_ctor_get(v_lhs_1472_, 0);
v_idx_1506_ = lean_ctor_get(v_lhs_1472_, 1);
v_struct_1507_ = lean_ctor_get(v_lhs_1472_, 2);
v___x_1508_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
v___x_1509_ = lean_ptr_addr(v_struct_1507_);
v___x_1510_ = lean_ptr_addr(v___x_1508_);
v___x_1511_ = lean_usize_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
lean_inc(v_idx_1506_);
lean_inc(v_typeName_1505_);
lean_dec_ref_known(v_lhs_1472_, 3);
v___x_1512_ = l_Lean_Expr_proj___override(v_typeName_1505_, v_idx_1506_, v___x_1508_);
v___y_1495_ = v___x_1512_;
goto v___jp_1494_;
}
else
{
v___y_1495_ = v_lhs_1472_;
goto v___jp_1494_;
}
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref(v_lhs_1472_);
v___x_1513_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10);
v___x_1514_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(v___x_1513_);
v___y_1495_ = v___x_1514_;
goto v___jp_1494_;
}
v___jp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = l_Lean_mkLambda(v___x_1492_, v___x_1493_, v_a_1491_, v___y_1495_);
v___x_1497_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1489_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1499_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5));
v___x_1500_ = lean_unsigned_to_nat(2u);
v___x_1501_ = lean_mk_empty_array_with_capacity(v___x_1500_);
v___x_1502_ = lean_array_push(v___x_1501_, v___x_1496_);
v___x_1503_ = lean_array_push(v___x_1502_, v_a_1498_);
v___x_1504_ = l_Lean_Meta_mkAppM(v___x_1499_, v___x_1503_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
return v___x_1504_;
}
else
{
lean_dec_ref(v___x_1496_);
return v___x_1497_;
}
}
}
else
{
lean_dec_ref(v___x_1489_);
lean_dec_ref(v_lhs_1472_);
return v___x_1490_;
}
}
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = l_Lean_Expr_appFn_x21(v_lhs_1472_);
v___x_1516_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1515_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12));
v___x_1519_ = l_Lean_Expr_appArg_x21(v_lhs_1472_);
lean_dec_ref(v_lhs_1472_);
v___x_1520_ = lean_unsigned_to_nat(2u);
v___x_1521_ = lean_mk_empty_array_with_capacity(v___x_1520_);
v___x_1522_ = lean_array_push(v___x_1521_, v_a_1517_);
v___x_1523_ = lean_array_push(v___x_1522_, v___x_1519_);
v___x_1524_ = l_Lean_Meta_mkAppM(v___x_1518_, v___x_1523_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
return v___x_1524_;
}
else
{
lean_dec_ref(v_lhs_1472_);
return v___x_1516_;
}
}
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v_dummy_1529_; lean_object* v_nargs_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1525_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2));
v___x_1526_ = l_Lean_Expr_getAppFn(v_lhs_1472_);
v___x_1527_ = l_Lean_Expr_constLevels_x21(v___x_1526_);
lean_dec_ref(v___x_1526_);
v___x_1528_ = l_Lean_mkConst(v___x_1525_, v___x_1527_);
v_dummy_1529_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_1530_ = l_Lean_Expr_getAppNumArgs(v_lhs_1472_);
lean_inc(v_nargs_1530_);
v___x_1531_ = lean_mk_array(v_nargs_1530_, v_dummy_1529_);
v___x_1532_ = lean_unsigned_to_nat(1u);
v___x_1533_ = lean_nat_sub(v_nargs_1530_, v___x_1532_);
lean_dec(v_nargs_1530_);
v___x_1534_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_1472_, v___x_1531_, v___x_1533_);
v___x_1535_ = l_Lean_mkAppN(v___x_1528_, v___x_1534_);
lean_dec_ref(v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
return v___x_1536_;
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v_dummy_1541_; lean_object* v_nargs_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4));
v___x_1538_ = l_Lean_Expr_getAppFn(v_lhs_1472_);
v___x_1539_ = l_Lean_Expr_constLevels_x21(v___x_1538_);
lean_dec_ref(v___x_1538_);
v___x_1540_ = l_Lean_mkConst(v___x_1537_, v___x_1539_);
v_dummy_1541_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_1542_ = l_Lean_Expr_getAppNumArgs(v_lhs_1472_);
lean_inc(v_nargs_1542_);
v___x_1543_ = lean_mk_array(v_nargs_1542_, v_dummy_1541_);
v___x_1544_ = lean_unsigned_to_nat(1u);
v___x_1545_ = lean_nat_sub(v_nargs_1542_, v___x_1544_);
lean_dec(v_nargs_1542_);
v___x_1546_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_1472_, v___x_1543_, v___x_1545_);
v___x_1547_ = l_Lean_mkAppN(v___x_1540_, v___x_1546_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(lean_object* v_lhs_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v_lhs_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(lean_object* v_msg_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___f_1563_; lean_object* v___x_1515__overap_1564_; lean_object* v___x_1565_; 
v___f_1563_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0));
v___x_1515__overap_1564_ = lean_panic_fn_borrowed(v___f_1563_, v_msg_1557_);
lean_inc(v___y_1561_);
lean_inc_ref(v___y_1560_);
lean_inc(v___y_1559_);
lean_inc_ref(v___y_1558_);
v___x_1565_ = lean_apply_5(v___x_1515__overap_1564_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, lean_box(0));
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(lean_object* v_msg_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v_msg_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v_ks_1577_; lean_object* v_vs_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1602_; 
v_ks_1577_ = lean_ctor_get(v_x_1573_, 0);
v_vs_1578_ = lean_ctor_get(v_x_1573_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_x_1573_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1580_ = v_x_1573_;
v_isShared_1581_ = v_isSharedCheck_1602_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_vs_1578_);
lean_inc(v_ks_1577_);
lean_dec(v_x_1573_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1602_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = lean_array_get_size(v_ks_1577_);
v___x_1583_ = lean_nat_dec_lt(v_x_1574_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
lean_dec(v_x_1574_);
v___x_1584_ = lean_array_push(v_ks_1577_, v_x_1575_);
v___x_1585_ = lean_array_push(v_vs_1578_, v_x_1576_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v___x_1585_);
lean_ctor_set(v___x_1580_, 0, v___x_1584_);
v___x_1587_ = v___x_1580_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
else
{
lean_object* v_k_x27_1589_; uint8_t v___x_1590_; 
v_k_x27_1589_ = lean_array_fget_borrowed(v_ks_1577_, v_x_1574_);
v___x_1590_ = l_Lean_instBEqMVarId_beq(v_x_1575_, v_k_x27_1589_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1592_; 
if (v_isShared_1581_ == 0)
{
v___x_1592_ = v___x_1580_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_ks_1577_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_vs_1578_);
v___x_1592_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_add(v_x_1574_, v___x_1593_);
lean_dec(v_x_1574_);
v_x_1573_ = v___x_1592_;
v_x_1574_ = v___x_1594_;
goto _start;
}
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1597_ = lean_array_fset(v_ks_1577_, v_x_1574_, v_x_1575_);
v___x_1598_ = lean_array_fset(v_vs_1578_, v_x_1574_, v_x_1576_);
lean_dec(v_x_1574_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v___x_1598_);
lean_ctor_set(v___x_1580_, 0, v___x_1597_);
v___x_1600_ = v___x_1580_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_1603_, lean_object* v_k_1604_, lean_object* v_v_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1607_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_1603_, v___x_1606_, v_k_1604_, v_v_1605_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1609_, size_t v_x_1610_, size_t v_x_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_){
_start:
{
if (lean_obj_tag(v_x_1609_) == 0)
{
lean_object* v_es_1614_; size_t v___x_1615_; size_t v___x_1616_; lean_object* v_j_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v_es_1614_ = lean_ctor_get(v_x_1609_, 0);
v___x_1615_ = ((size_t)31ULL);
v___x_1616_ = lean_usize_land(v_x_1610_, v___x_1615_);
v_j_1617_ = lean_usize_to_nat(v___x_1616_);
v___x_1618_ = lean_array_get_size(v_es_1614_);
v___x_1619_ = lean_nat_dec_lt(v_j_1617_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_dec(v_j_1617_);
lean_dec(v_x_1613_);
lean_dec(v_x_1612_);
return v_x_1609_;
}
else
{
lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1658_; 
lean_inc_ref(v_es_1614_);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_x_1609_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v_x_1609_, 0);
lean_dec(v_unused_1659_);
v___x_1621_ = v_x_1609_;
v_isShared_1622_ = v_isSharedCheck_1658_;
goto v_resetjp_1620_;
}
else
{
lean_dec(v_x_1609_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1658_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_v_1623_; lean_object* v___x_1624_; lean_object* v_xs_x27_1625_; lean_object* v___y_1627_; 
v_v_1623_ = lean_array_fget(v_es_1614_, v_j_1617_);
v___x_1624_ = lean_box(0);
v_xs_x27_1625_ = lean_array_fset(v_es_1614_, v_j_1617_, v___x_1624_);
switch(lean_obj_tag(v_v_1623_))
{
case 0:
{
lean_object* v_key_1632_; lean_object* v_val_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1643_; 
v_key_1632_ = lean_ctor_get(v_v_1623_, 0);
v_val_1633_ = lean_ctor_get(v_v_1623_, 1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_v_1623_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1635_ = v_v_1623_;
v_isShared_1636_ = v_isSharedCheck_1643_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_val_1633_);
lean_inc(v_key_1632_);
lean_dec(v_v_1623_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1643_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
uint8_t v___x_1637_; 
v___x_1637_ = l_Lean_instBEqMVarId_beq(v_x_1612_, v_key_1632_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_del_object(v___x_1635_);
v___x_1638_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1632_, v_val_1633_, v_x_1612_, v_x_1613_);
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
v___y_1627_ = v___x_1639_;
goto v___jp_1626_;
}
else
{
lean_object* v___x_1641_; 
lean_dec(v_val_1633_);
lean_dec(v_key_1632_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 1, v_x_1613_);
lean_ctor_set(v___x_1635_, 0, v_x_1612_);
v___x_1641_ = v___x_1635_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_x_1612_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_x_1613_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
v___y_1627_ = v___x_1641_;
goto v___jp_1626_;
}
}
}
}
case 1:
{
lean_object* v_node_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1656_; 
v_node_1644_ = lean_ctor_get(v_v_1623_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_v_1623_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1646_ = v_v_1623_;
v_isShared_1647_ = v_isSharedCheck_1656_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_node_1644_);
lean_dec(v_v_1623_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1656_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
size_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; size_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1648_ = ((size_t)5ULL);
v___x_1649_ = lean_usize_shift_right(v_x_1610_, v___x_1648_);
v___x_1650_ = ((size_t)1ULL);
v___x_1651_ = lean_usize_add(v_x_1611_, v___x_1650_);
v___x_1652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_node_1644_, v___x_1649_, v___x_1651_, v_x_1612_, v_x_1613_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1652_);
v___x_1654_ = v___x_1646_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
v___y_1627_ = v___x_1654_;
goto v___jp_1626_;
}
}
}
default: 
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v_x_1612_);
lean_ctor_set(v___x_1657_, 1, v_x_1613_);
v___y_1627_ = v___x_1657_;
goto v___jp_1626_;
}
}
v___jp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = lean_array_fset(v_xs_x27_1625_, v_j_1617_, v___y_1627_);
lean_dec(v_j_1617_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1628_);
v___x_1630_ = v___x_1621_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
else
{
lean_object* v_ks_1660_; lean_object* v_vs_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1679_; 
v_ks_1660_ = lean_ctor_get(v_x_1609_, 0);
v_vs_1661_ = lean_ctor_get(v_x_1609_, 1);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_x_1609_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1663_ = v_x_1609_;
v_isShared_1664_ = v_isSharedCheck_1679_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_vs_1661_);
lean_inc(v_ks_1660_);
lean_dec(v_x_1609_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1679_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_ks_1660_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_vs_1661_);
v___x_1666_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v_newNode_1667_; size_t v___x_1668_; uint8_t v___x_1669_; 
v_newNode_1667_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v___x_1666_, v_x_1612_, v_x_1613_);
v___x_1668_ = ((size_t)7ULL);
v___x_1669_ = lean_usize_dec_le(v___x_1668_, v_x_1611_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1670_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1667_);
v___x_1671_ = lean_unsigned_to_nat(4u);
v___x_1672_ = lean_nat_dec_lt(v___x_1670_, v___x_1671_);
lean_dec(v___x_1670_);
if (v___x_1672_ == 0)
{
lean_object* v_ks_1673_; lean_object* v_vs_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_ks_1673_ = lean_ctor_get(v_newNode_1667_, 0);
lean_inc_ref(v_ks_1673_);
v_vs_1674_ = lean_ctor_get(v_newNode_1667_, 1);
lean_inc_ref(v_vs_1674_);
lean_dec_ref(v_newNode_1667_);
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_1677_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_1611_, v_ks_1673_, v_vs_1674_, v___x_1675_, v___x_1676_);
lean_dec_ref(v_vs_1674_);
lean_dec_ref(v_ks_1673_);
return v___x_1677_;
}
else
{
return v_newNode_1667_;
}
}
else
{
return v_newNode_1667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_1680_, lean_object* v_keys_1681_, lean_object* v_vals_1682_, lean_object* v_i_1683_, lean_object* v_entries_1684_){
_start:
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = lean_array_get_size(v_keys_1681_);
v___x_1686_ = lean_nat_dec_lt(v_i_1683_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_dec(v_i_1683_);
return v_entries_1684_;
}
else
{
lean_object* v_k_1687_; lean_object* v_v_1688_; uint64_t v___x_1689_; size_t v_h_1690_; size_t v___x_1691_; lean_object* v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; size_t v___x_1695_; size_t v_h_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v_k_1687_ = lean_array_fget_borrowed(v_keys_1681_, v_i_1683_);
v_v_1688_ = lean_array_fget_borrowed(v_vals_1682_, v_i_1683_);
v___x_1689_ = l_Lean_instHashableMVarId_hash(v_k_1687_);
v_h_1690_ = lean_uint64_to_usize(v___x_1689_);
v___x_1691_ = ((size_t)5ULL);
v___x_1692_ = lean_unsigned_to_nat(1u);
v___x_1693_ = ((size_t)1ULL);
v___x_1694_ = lean_usize_sub(v_depth_1680_, v___x_1693_);
v___x_1695_ = lean_usize_mul(v___x_1691_, v___x_1694_);
v_h_1696_ = lean_usize_shift_right(v_h_1690_, v___x_1695_);
v___x_1697_ = lean_nat_add(v_i_1683_, v___x_1692_);
lean_dec(v_i_1683_);
lean_inc(v_v_1688_);
lean_inc(v_k_1687_);
v___x_1698_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_entries_1684_, v_h_1696_, v_depth_1680_, v_k_1687_, v_v_1688_);
v_i_1683_ = v___x_1697_;
v_entries_1684_ = v___x_1698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_1700_, lean_object* v_keys_1701_, lean_object* v_vals_1702_, lean_object* v_i_1703_, lean_object* v_entries_1704_){
_start:
{
size_t v_depth_boxed_1705_; lean_object* v_res_1706_; 
v_depth_boxed_1705_ = lean_unbox_usize(v_depth_1700_);
lean_dec(v_depth_1700_);
v_res_1706_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_1705_, v_keys_1701_, v_vals_1702_, v_i_1703_, v_entries_1704_);
lean_dec_ref(v_vals_1702_);
lean_dec_ref(v_keys_1701_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1707_, lean_object* v_x_1708_, lean_object* v_x_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_){
_start:
{
size_t v_x_2106__boxed_1712_; size_t v_x_2107__boxed_1713_; lean_object* v_res_1714_; 
v_x_2106__boxed_1712_ = lean_unbox_usize(v_x_1708_);
lean_dec(v_x_1708_);
v_x_2107__boxed_1713_ = lean_unbox_usize(v_x_1709_);
lean_dec(v_x_1709_);
v_res_1714_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1707_, v_x_2106__boxed_1712_, v_x_2107__boxed_1713_, v_x_1710_, v_x_1711_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(lean_object* v_x_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_){
_start:
{
uint64_t v___x_1718_; size_t v___x_1719_; size_t v___x_1720_; lean_object* v___x_1721_; 
v___x_1718_ = l_Lean_instHashableMVarId_hash(v_x_1716_);
v___x_1719_ = lean_uint64_to_usize(v___x_1718_);
v___x_1720_ = ((size_t)1ULL);
v___x_1721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1715_, v___x_1719_, v___x_1720_, v_x_1716_, v_x_1717_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(lean_object* v_mvarId_1722_, lean_object* v_val_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; lean_object* v_mctx_1727_; lean_object* v_cache_1728_; lean_object* v_zetaDeltaFVarIds_1729_; lean_object* v_postponed_1730_; lean_object* v_diag_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1761_; 
v___x_1726_ = lean_st_ref_take(v___y_1724_);
v_mctx_1727_ = lean_ctor_get(v___x_1726_, 0);
v_cache_1728_ = lean_ctor_get(v___x_1726_, 1);
v_zetaDeltaFVarIds_1729_ = lean_ctor_get(v___x_1726_, 2);
v_postponed_1730_ = lean_ctor_get(v___x_1726_, 3);
v_diag_1731_ = lean_ctor_get(v___x_1726_, 4);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1733_ = v___x_1726_;
v_isShared_1734_ = v_isSharedCheck_1761_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_diag_1731_);
lean_inc(v_postponed_1730_);
lean_inc(v_zetaDeltaFVarIds_1729_);
lean_inc(v_cache_1728_);
lean_inc(v_mctx_1727_);
lean_dec(v___x_1726_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1761_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_depth_1735_; lean_object* v_levelAssignDepth_1736_; lean_object* v_lmvarCounter_1737_; lean_object* v_mvarCounter_1738_; lean_object* v_lDecls_1739_; lean_object* v_decls_1740_; lean_object* v_userNames_1741_; lean_object* v_lAssignment_1742_; lean_object* v_eAssignment_1743_; lean_object* v_dAssignment_1744_; lean_object* v_instanceTypedMVars_1745_; lean_object* v_synthNormMemo_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1760_; 
v_depth_1735_ = lean_ctor_get(v_mctx_1727_, 0);
v_levelAssignDepth_1736_ = lean_ctor_get(v_mctx_1727_, 1);
v_lmvarCounter_1737_ = lean_ctor_get(v_mctx_1727_, 2);
v_mvarCounter_1738_ = lean_ctor_get(v_mctx_1727_, 3);
v_lDecls_1739_ = lean_ctor_get(v_mctx_1727_, 4);
v_decls_1740_ = lean_ctor_get(v_mctx_1727_, 5);
v_userNames_1741_ = lean_ctor_get(v_mctx_1727_, 6);
v_lAssignment_1742_ = lean_ctor_get(v_mctx_1727_, 7);
v_eAssignment_1743_ = lean_ctor_get(v_mctx_1727_, 8);
v_dAssignment_1744_ = lean_ctor_get(v_mctx_1727_, 9);
v_instanceTypedMVars_1745_ = lean_ctor_get(v_mctx_1727_, 10);
v_synthNormMemo_1746_ = lean_ctor_get(v_mctx_1727_, 11);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_mctx_1727_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1748_ = v_mctx_1727_;
v_isShared_1749_ = v_isSharedCheck_1760_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_synthNormMemo_1746_);
lean_inc(v_instanceTypedMVars_1745_);
lean_inc(v_dAssignment_1744_);
lean_inc(v_eAssignment_1743_);
lean_inc(v_lAssignment_1742_);
lean_inc(v_userNames_1741_);
lean_inc(v_decls_1740_);
lean_inc(v_lDecls_1739_);
lean_inc(v_mvarCounter_1738_);
lean_inc(v_lmvarCounter_1737_);
lean_inc(v_levelAssignDepth_1736_);
lean_inc(v_depth_1735_);
lean_dec(v_mctx_1727_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1760_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1750_ = lean_box(0);
v___x_1751_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_1743_, v_mvarId_1722_, v_val_1723_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 8, v___x_1751_);
v___x_1753_ = v___x_1748_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_depth_1735_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_levelAssignDepth_1736_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_lmvarCounter_1737_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_mvarCounter_1738_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_lDecls_1739_);
lean_ctor_set(v_reuseFailAlloc_1759_, 5, v_decls_1740_);
lean_ctor_set(v_reuseFailAlloc_1759_, 6, v_userNames_1741_);
lean_ctor_set(v_reuseFailAlloc_1759_, 7, v_lAssignment_1742_);
lean_ctor_set(v_reuseFailAlloc_1759_, 8, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1759_, 9, v_dAssignment_1744_);
lean_ctor_set(v_reuseFailAlloc_1759_, 10, v_instanceTypedMVars_1745_);
lean_ctor_set(v_reuseFailAlloc_1759_, 11, v_synthNormMemo_1746_);
v___x_1753_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1755_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1753_);
v___x_1755_ = v___x_1733_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_cache_1728_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_zetaDeltaFVarIds_1729_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_postponed_1730_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_diag_1731_);
v___x_1755_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = lean_st_ref_put(v___y_1724_, v___x_1755_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1750_);
return v___x_1757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object* v_mvarId_1762_, lean_object* v_val_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1762_, v_val_1763_, v___y_1764_);
lean_dec(v___y_1764_);
return v_res_1766_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1769_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1770_ = lean_unsigned_to_nat(41u);
v___x_1771_ = lean_unsigned_to_nat(113u);
v___x_1772_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_1773_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1774_ = l_mkPanicMessageWithDecl(v___x_1773_, v___x_1772_, v___x_1771_, v___x_1770_, v___x_1769_);
return v___x_1774_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1775_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1776_ = lean_unsigned_to_nat(51u);
v___x_1777_ = lean_unsigned_to_nat(115u);
v___x_1778_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_1779_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1780_ = l_mkPanicMessageWithDecl(v___x_1779_, v___x_1778_, v___x_1777_, v___x_1776_, v___x_1775_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object* v_mvarId_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; 
lean_inc(v_mvarId_1781_);
v___x_1787_ = l_Lean_MVarId_getType_x27(v_mvarId_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v___x_1789_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_1790_ = lean_unsigned_to_nat(3u);
v___x_1791_ = l_Lean_Expr_isAppOfArity(v_a_1788_, v___x_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec(v_a_1788_);
lean_dec(v_mvarId_1781_);
v___x_1792_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2);
v___x_1793_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_1792_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = l_Lean_Expr_appFn_x21(v_a_1788_);
v___x_1795_ = l_Lean_Expr_appArg_x21(v___x_1794_);
lean_dec_ref(v___x_1794_);
v___x_1796_ = l_Lean_Expr_appArg_x21(v_a_1788_);
lean_dec(v_a_1788_);
v___x_1797_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1795_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1799_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc_n(v_a_1798_, 2);
lean_dec_ref_known(v___x_1797_, 1);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
v___x_1799_ = lean_infer_type(v_a_1798_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; uint8_t v___x_1801_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
v___x_1801_ = l_Lean_Expr_isAppOfArity(v_a_1800_, v___x_1789_, v___x_1790_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
lean_dec(v_a_1800_);
lean_dec(v_a_1798_);
lean_dec_ref(v___x_1796_);
lean_dec(v_mvarId_1781_);
v___x_1802_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
v___x_1803_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_1802_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = l_Lean_Expr_appArg_x21(v_a_1800_);
lean_dec(v_a_1800_);
v___x_1805_ = l_Lean_Meta_mkEq(v___x_1804_, v___x_1796_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v___x_1807_ = lean_box(0);
v___x_1808_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1806_, v___x_1807_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc_n(v_a_1809_, 2);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = l_Lean_Meta_mkEqTrans(v_a_1798_, v_a_1809_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v___y_1782_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1820_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___x_1812_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1781_, v_a_1811_, v___y_1783_);
lean_dec(v___y_1783_);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v___x_1812_, 0);
lean_dec(v_unused_1821_);
v___x_1814_ = v___x_1812_;
v_isShared_1815_ = v_isSharedCheck_1820_;
goto v_resetjp_1813_;
}
else
{
lean_dec(v___x_1812_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1820_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = l_Lean_Expr_mvarId_x21(v_a_1809_);
lean_dec(v_a_1809_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1816_);
v___x_1818_ = v___x_1814_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_a_1809_);
lean_dec(v___y_1783_);
lean_dec(v_mvarId_1781_);
v_a_1822_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1810_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1810_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec(v_a_1798_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v_mvarId_1781_);
v_a_1830_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1808_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1808_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_a_1798_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v_mvarId_1781_);
v_a_1838_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1805_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1805_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v_a_1798_);
lean_dec_ref(v___x_1796_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v_mvarId_1781_);
v_a_1846_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1799_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1799_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v___x_1796_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v_mvarId_1781_);
v_a_1854_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1797_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1797_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v_mvarId_1781_);
v_a_1862_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1787_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1787_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object* v_mvarId_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object* v_mvarId_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v___f_1883_; lean_object* v___x_1884_; 
lean_inc(v_mvarId_1877_);
v___f_1883_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1883_, 0, v_mvarId_1877_);
v___x_1884_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1877_, v___f_1883_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object* v_mvarId_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object* v_mvarId_1892_, lean_object* v_val_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1892_, v_val_1893_, v___y_1895_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object* v_mvarId_1900_, lean_object* v_val_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_1900_, v_val_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object* v_00_u03b2_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_1909_, v_x_1910_, v_x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1913_, lean_object* v_x_1914_, size_t v_x_1915_, size_t v_x_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1914_, v_x_1915_, v_x_1916_, v_x_1917_, v_x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
size_t v_x_2580__boxed_1926_; size_t v_x_2581__boxed_1927_; lean_object* v_res_1928_; 
v_x_2580__boxed_1926_ = lean_unbox_usize(v_x_1922_);
lean_dec(v_x_1922_);
v_x_2581__boxed_1927_ = lean_unbox_usize(v_x_1923_);
lean_dec(v_x_1923_);
v_res_1928_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_1920_, v_x_1921_, v_x_2580__boxed_1926_, v_x_2581__boxed_1927_, v_x_1924_, v_x_1925_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1929_, lean_object* v_n_1930_, lean_object* v_k_1931_, lean_object* v_v_1932_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1930_, v_k_1931_, v_v_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1934_, size_t v_depth_1935_, lean_object* v_keys_1936_, lean_object* v_vals_1937_, lean_object* v_heq_1938_, lean_object* v_i_1939_, lean_object* v_entries_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1935_, v_keys_1936_, v_vals_1937_, v_i_1939_, v_entries_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1942_, lean_object* v_depth_1943_, lean_object* v_keys_1944_, lean_object* v_vals_1945_, lean_object* v_heq_1946_, lean_object* v_i_1947_, lean_object* v_entries_1948_){
_start:
{
size_t v_depth_boxed_1949_; lean_object* v_res_1950_; 
v_depth_boxed_1949_ = lean_unbox_usize(v_depth_1943_);
lean_dec(v_depth_1943_);
v_res_1950_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1942_, v_depth_boxed_1949_, v_keys_1944_, v_vals_1945_, v_heq_1946_, v_i_1947_, v_entries_1948_);
lean_dec_ref(v_vals_1945_);
lean_dec_ref(v_keys_1944_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_, lean_object* v_x_1954_, lean_object* v_x_1955_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1952_, v_x_1953_, v_x_1954_, v_x_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0(lean_object* v_declNameNonRec_1957_, lean_object* v_numFixed_1958_, lean_object* v_x_1959_){
_start:
{
uint8_t v___x_1960_; 
v___x_1960_ = l_Lean_Expr_isAppOfArity(v_x_1959_, v_declNameNonRec_1957_, v_numFixed_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0___boxed(lean_object* v_declNameNonRec_1961_, lean_object* v_numFixed_1962_, lean_object* v_x_1963_){
_start:
{
uint8_t v_res_1964_; lean_object* v_r_1965_; 
v_res_1964_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0(v_declNameNonRec_1961_, v_numFixed_1962_, v_x_1963_);
lean_dec_ref(v_x_1963_);
lean_dec(v_declNameNonRec_1961_);
v_r_1965_ = lean_box(v_res_1964_);
return v_r_1965_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1967_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1968_ = lean_unsigned_to_nat(41u);
v___x_1969_ = lean_unsigned_to_nat(128u);
v___x_1970_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__0));
v___x_1971_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1972_ = l_mkPanicMessageWithDecl(v___x_1971_, v___x_1970_, v___x_1969_, v___x_1968_, v___x_1967_);
return v___x_1972_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1973_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1974_ = lean_unsigned_to_nat(51u);
v___x_1975_ = lean_unsigned_to_nat(134u);
v___x_1976_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__0));
v___x_1977_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1978_ = l_mkPanicMessageWithDecl(v___x_1977_, v___x_1976_, v___x_1975_, v___x_1974_, v___x_1973_);
return v___x_1978_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__5));
v___x_1984_ = l_Lean_stringToMessageData(v___x_1983_);
return v___x_1984_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__7));
v___x_1987_ = l_Lean_stringToMessageData(v___x_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1(lean_object* v_mvarId_1988_, lean_object* v___f_1989_, lean_object* v_fixEq_1990_, lean_object* v_declNameNonRec_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v___x_1997_; 
lean_inc(v_mvarId_1988_);
v___x_1997_ = l_Lean_MVarId_getType_x27(v_mvarId_1988_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_1999_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_2000_ = lean_unsigned_to_nat(3u);
v___x_2001_ = l_Lean_Expr_isAppOfArity(v_a_1998_, v___x_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_dec(v_a_1998_);
lean_dec(v_declNameNonRec_1991_);
lean_dec(v_fixEq_1990_);
lean_dec(v_mvarId_1988_);
v___x_2002_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1);
v___x_2003_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_2002_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v___x_2003_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2004_ = l_Lean_Expr_appFn_x21(v_a_1998_);
v___x_2005_ = l_Lean_Expr_appArg_x21(v___x_2004_);
lean_dec_ref(v___x_2004_);
v___x_2006_ = lean_find_expr(v___f_1989_, v___x_2005_);
if (lean_obj_tag(v___x_2006_) == 1)
{
lean_object* v_val_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec(v_declNameNonRec_1991_);
v_val_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc_n(v_val_2007_, 2);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2008_ = l_Lean_Expr_appArg_x21(v_a_1998_);
lean_dec(v_a_1998_);
lean_inc(v___y_1995_);
lean_inc_ref(v___y_1994_);
lean_inc(v___y_1993_);
lean_inc_ref(v___y_1992_);
v___x_2009_ = lean_infer_type(v_val_2007_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = lean_box(0);
lean_inc(v_val_2007_);
v___x_2012_ = l_Lean_Meta_kabstract(v___x_2005_, v_val_2007_, v___x_2011_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v_dummy_2020_; lean_object* v_nargs_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v___x_2014_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3));
v___x_2015_ = 0;
v___x_2016_ = l_Lean_mkLambda(v___x_2014_, v___x_2015_, v_a_2010_, v_a_2013_);
v___x_2017_ = l_Lean_Expr_getAppFn(v_val_2007_);
v___x_2018_ = l_Lean_Expr_constLevels_x21(v___x_2017_);
lean_dec_ref(v___x_2017_);
v___x_2019_ = l_Lean_mkConst(v_fixEq_1990_, v___x_2018_);
v_dummy_2020_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_2021_ = l_Lean_Expr_getAppNumArgs(v_val_2007_);
lean_inc(v_nargs_2021_);
v___x_2022_ = lean_mk_array(v_nargs_2021_, v_dummy_2020_);
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = lean_nat_sub(v_nargs_2021_, v___x_2023_);
lean_dec(v_nargs_2021_);
v___x_2025_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_2007_, v___x_2022_, v___x_2024_);
v___x_2026_ = l_Lean_mkAppN(v___x_2019_, v___x_2025_);
lean_dec_ref(v___x_2025_);
v___x_2027_ = l_Lean_Meta_mkCongrArg(v___x_2016_, v___x_2026_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc_n(v_a_2028_, 2);
lean_dec_ref_known(v___x_2027_, 1);
lean_inc(v___y_1995_);
lean_inc_ref(v___y_1994_);
lean_inc(v___y_1993_);
lean_inc_ref(v___y_1992_);
v___x_2029_ = lean_infer_type(v_a_2028_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; uint8_t v___x_2031_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2031_ = l_Lean_Expr_isAppOfArity(v_a_2030_, v___x_1999_, v___x_2000_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec(v_a_2030_);
lean_dec(v_a_2028_);
lean_dec_ref(v___x_2008_);
lean_dec(v_mvarId_1988_);
v___x_2032_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2);
v___x_2033_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_2032_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v___x_2033_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2034_ = l_Lean_Expr_appArg_x21(v_a_2030_);
lean_dec(v_a_2030_);
v___x_2035_ = l_Lean_Expr_headBeta(v___x_2034_);
v___x_2036_ = l_Lean_Meta_mkEq(v___x_2035_, v___x_2008_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = lean_box(0);
v___x_2039_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2037_, v___x_2038_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc_n(v_a_2040_, 2);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = l_Lean_Meta_mkEqTrans(v_a_2028_, v_a_2040_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec_ref(v___y_1992_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2051_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1988_, v_a_2042_, v___y_1993_);
lean_dec(v___y_1993_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2043_, 0);
lean_dec(v_unused_2052_);
v___x_2045_ = v___x_2043_;
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
else
{
lean_dec(v___x_2043_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = l_Lean_Expr_mvarId_x21(v_a_2040_);
lean_dec(v_a_2040_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2047_);
v___x_2049_ = v___x_2045_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_a_2040_);
lean_dec(v___y_1993_);
lean_dec(v_mvarId_1988_);
v_a_2053_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2041_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2041_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_a_2028_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v_mvarId_1988_);
v_a_2061_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2039_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2039_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_a_2028_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v_mvarId_1988_);
v_a_2069_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2036_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2036_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v_a_2028_);
lean_dec_ref(v___x_2008_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v_mvarId_1988_);
v_a_2077_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2029_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2029_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v___x_2008_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v_mvarId_1988_);
v_a_2085_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2027_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2027_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v_a_2010_);
lean_dec_ref(v___x_2008_);
lean_dec(v_val_2007_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v_fixEq_1990_);
lean_dec(v_mvarId_1988_);
v_a_2093_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2012_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2012_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref(v___x_2008_);
lean_dec(v_val_2007_);
lean_dec_ref(v___x_2005_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v_fixEq_1990_);
lean_dec(v_mvarId_1988_);
v_a_2101_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2009_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2009_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec(v___x_2006_);
lean_dec_ref(v___x_2005_);
lean_dec(v_a_1998_);
lean_dec(v_fixEq_1990_);
v___x_2109_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__4));
v___x_2110_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6);
v___x_2111_ = 0;
v___x_2112_ = l_Lean_MessageData_ofConstName(v_declNameNonRec_1991_, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2110_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8);
v___x_2115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
v___x_2117_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2109_, v_mvarId_1988_, v___x_2116_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v___x_2117_;
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v_declNameNonRec_1991_);
lean_dec(v_fixEq_1990_);
lean_dec(v_mvarId_1988_);
v_a_2118_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_1997_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_1997_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___boxed(lean_object* v_mvarId_2126_, lean_object* v___f_2127_, lean_object* v_fixEq_2128_, lean_object* v_declNameNonRec_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1(v_mvarId_2126_, v___f_2127_, v_fixEq_2128_, v_declNameNonRec_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec_ref(v___f_2127_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(lean_object* v_declNameNonRec_2136_, lean_object* v_fixEq_2137_, lean_object* v_numFixed_2138_, lean_object* v_mvarId_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v___f_2145_; lean_object* v___f_2146_; lean_object* v___x_2147_; 
lean_inc(v_declNameNonRec_2136_);
v___f_2145_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2145_, 0, v_declNameNonRec_2136_);
lean_closure_set(v___f_2145_, 1, v_numFixed_2138_);
lean_inc(v_mvarId_2139_);
v___f_2146_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___boxed), 9, 4);
lean_closure_set(v___f_2146_, 0, v_mvarId_2139_);
lean_closure_set(v___f_2146_, 1, v___f_2145_);
lean_closure_set(v___f_2146_, 2, v_fixEq_2137_);
lean_closure_set(v___f_2146_, 3, v_declNameNonRec_2136_);
v___x_2147_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_2139_, v___f_2146_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___boxed(lean_object* v_declNameNonRec_2148_, lean_object* v_fixEq_2149_, lean_object* v_numFixed_2150_, lean_object* v_mvarId_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(v_declNameNonRec_2148_, v_fixEq_2149_, v_numFixed_2150_, v_mvarId_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(lean_object* v_e_2158_, lean_object* v___y_2159_){
_start:
{
uint8_t v___x_2161_; 
v___x_2161_ = l_Lean_Expr_hasMVar(v_e_2158_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v_e_2158_);
return v___x_2162_;
}
else
{
lean_object* v___x_2163_; lean_object* v_mctx_2164_; lean_object* v___x_2165_; lean_object* v_fst_2166_; lean_object* v_snd_2167_; lean_object* v___x_2168_; lean_object* v_cache_2169_; lean_object* v_zetaDeltaFVarIds_2170_; lean_object* v_postponed_2171_; lean_object* v_diag_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2181_; 
v___x_2163_ = lean_st_ref_get(v___y_2159_);
v_mctx_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc_ref(v_mctx_2164_);
lean_dec(v___x_2163_);
v___x_2165_ = l_Lean_instantiateMVarsCore(v_mctx_2164_, v_e_2158_);
v_fst_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_fst_2166_);
v_snd_2167_ = lean_ctor_get(v___x_2165_, 1);
lean_inc(v_snd_2167_);
lean_dec_ref(v___x_2165_);
v___x_2168_ = lean_st_ref_take(v___y_2159_);
v_cache_2169_ = lean_ctor_get(v___x_2168_, 1);
v_zetaDeltaFVarIds_2170_ = lean_ctor_get(v___x_2168_, 2);
v_postponed_2171_ = lean_ctor_get(v___x_2168_, 3);
v_diag_2172_ = lean_ctor_get(v___x_2168_, 4);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v___x_2168_, 0);
lean_dec(v_unused_2182_);
v___x_2174_ = v___x_2168_;
v_isShared_2175_ = v_isSharedCheck_2181_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_diag_2172_);
lean_inc(v_postponed_2171_);
lean_inc(v_zetaDeltaFVarIds_2170_);
lean_inc(v_cache_2169_);
lean_dec(v___x_2168_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2181_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v_snd_2167_);
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_snd_2167_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_cache_2169_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_zetaDeltaFVarIds_2170_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_postponed_2171_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v_diag_2172_);
v___x_2177_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_st_ref_put(v___y_2159_, v___x_2177_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_fst_2166_);
return v___x_2179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg___boxed(lean_object* v_e_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_e_2183_, v___y_2184_);
lean_dec(v___y_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object* v_e_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_e_2187_, v___y_2189_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___boxed(lean_object* v_e_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_e_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_2201_, lean_object* v_opt_2202_){
_start:
{
lean_object* v_name_2203_; lean_object* v_defValue_2204_; lean_object* v_map_2205_; lean_object* v___x_2206_; 
v_name_2203_ = lean_ctor_get(v_opt_2202_, 0);
v_defValue_2204_ = lean_ctor_get(v_opt_2202_, 1);
v_map_2205_ = lean_ctor_get(v_opts_2201_, 0);
v___x_2206_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2205_, v_name_2203_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_inc(v_defValue_2204_);
return v_defValue_2204_;
}
else
{
lean_object* v_val_2207_; 
v_val_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v___x_2206_, 1);
if (lean_obj_tag(v_val_2207_) == 3)
{
lean_object* v_v_2208_; 
v_v_2208_ = lean_ctor_get(v_val_2207_, 0);
lean_inc(v_v_2208_);
lean_dec_ref_known(v_val_2207_, 1);
return v_v_2208_;
}
else
{
lean_dec(v_val_2207_);
lean_inc(v_defValue_2204_);
return v_defValue_2204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_2209_, lean_object* v_opt_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_2209_, v_opt_2210_);
lean_dec_ref(v_opt_2210_);
lean_dec_ref(v_opts_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(lean_object* v_k_2212_, uint8_t v_allowLevelAssignments_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2213_, v_k_2212_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
v_a_2228_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2219_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2219_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg___boxed(lean_object* v_k_2236_, lean_object* v_allowLevelAssignments_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2243_; lean_object* v_res_2244_; 
v_allowLevelAssignments_boxed_2243_ = lean_unbox(v_allowLevelAssignments_2237_);
v_res_2244_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_k_2236_, v_allowLevelAssignments_boxed_2243_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object* v_00_u03b1_2245_, lean_object* v_k_2246_, uint8_t v_allowLevelAssignments_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_k_2246_, v_allowLevelAssignments_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object* v_00_u03b1_2254_, lean_object* v_k_2255_, lean_object* v_allowLevelAssignments_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2262_; lean_object* v_res_2263_; 
v_allowLevelAssignments_boxed_2262_ = lean_unbox(v_allowLevelAssignments_2256_);
v_res_2263_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v_00_u03b1_2254_, v_k_2255_, v_allowLevelAssignments_boxed_2262_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object* v___x_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_toCold_2273_; lean_object* v_options_2274_; uint8_t v_hasTrace_2275_; 
v_toCold_2273_ = lean_ctor_get(v___y_2270_, 0);
v_options_2274_ = lean_ctor_get(v_toCold_2273_, 2);
v_hasTrace_2275_ = lean_ctor_get_uint8(v_options_2274_, sizeof(void*)*1);
if (v_hasTrace_2275_ == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec(v___x_2267_);
v___x_2276_ = lean_box(v_hasTrace_2275_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
else
{
lean_object* v_inheritedTraceOptions_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_inheritedTraceOptions_2278_ = lean_ctor_get(v_toCold_2273_, 11);
v___x_2279_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_2280_ = l_Lean_Name_append(v___x_2279_, v___x_2267_);
v___x_2281_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2278_, v_options_2274_, v___x_2280_);
lean_dec(v___x_2280_);
v___x_2282_ = lean_box(v___x_2281_);
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
return v___x_2283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v___x_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(lean_object* v_o_2291_, lean_object* v_k_2292_, uint8_t v_v_2293_){
_start:
{
lean_object* v_map_2294_; uint8_t v_hasTrace_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2309_; 
v_map_2294_ = lean_ctor_get(v_o_2291_, 0);
v_hasTrace_2295_ = lean_ctor_get_uint8(v_o_2291_, sizeof(void*)*1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_o_2291_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2297_ = v_o_2291_;
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_map_2294_);
lean_dec(v_o_2291_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2299_, 0, v_v_2293_);
lean_inc(v_k_2292_);
v___x_2300_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2292_, v___x_2299_, v_map_2294_);
if (v_hasTrace_2295_ == 0)
{
lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2304_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_2302_ = l_Lean_Name_isPrefixOf(v___x_2301_, v_k_2292_);
lean_dec(v_k_2292_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2300_);
v___x_2304_ = v___x_2297_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2300_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_ctor_set_uint8(v___x_2304_, sizeof(void*)*1, v___x_2302_);
return v___x_2304_;
}
}
else
{
lean_object* v___x_2307_; 
lean_dec(v_k_2292_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2300_);
v___x_2307_ = v___x_2297_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2300_);
lean_ctor_set_uint8(v_reuseFailAlloc_2308_, sizeof(void*)*1, v_hasTrace_2295_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3___boxed(lean_object* v_o_2310_, lean_object* v_k_2311_, lean_object* v_v_2312_){
_start:
{
uint8_t v_v_boxed_2313_; lean_object* v_res_2314_; 
v_v_boxed_2313_ = lean_unbox(v_v_2312_);
v_res_2314_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(v_o_2310_, v_k_2311_, v_v_boxed_2313_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_2315_, lean_object* v_opt_2316_, uint8_t v_val_2317_){
_start:
{
lean_object* v_name_2318_; lean_object* v___x_2319_; 
v_name_2318_ = lean_ctor_get(v_opt_2316_, 0);
lean_inc(v_name_2318_);
lean_dec_ref(v_opt_2316_);
v___x_2319_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(v_opts_2315_, v_name_2318_, v_val_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_2320_, lean_object* v_opt_2321_, lean_object* v_val_2322_){
_start:
{
uint8_t v_val_boxed_2323_; lean_object* v_res_2324_; 
v_val_boxed_2323_ = lean_unbox(v_val_2322_);
v_res_2324_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_2320_, v_opt_2321_, v_val_boxed_2323_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object* v_mvarId_2325_, uint8_t v___x_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint16_t v___y_2333_; lean_object* v___y_2334_; lean_object* v_fileName_2335_; lean_object* v_fileMap_2336_; lean_object* v_currNamespace_2337_; lean_object* v_openDecls_2338_; lean_object* v_initHeartbeats_2339_; lean_object* v_maxHeartbeats_2340_; lean_object* v_quotContext_2341_; lean_object* v_currMacroScope_2342_; lean_object* v_cancelTk_x3f_2343_; lean_object* v_inheritedTraceOptions_2344_; lean_object* v_currRecDepth_2345_; lean_object* v_ref_2346_; uint8_t v_suppressElabErrors_2347_; uint8_t v_checkDeprecated_2348_; uint8_t v_isRecordingDeps_2349_; lean_object* v___y_2350_; lean_object* v_toCold_2356_; lean_object* v_currRecDepth_2357_; lean_object* v_ref_2358_; uint8_t v_suppressElabErrors_2359_; uint8_t v_checkDeprecated_2360_; uint8_t v_isRecordingDeps_2361_; lean_object* v_fileName_2362_; lean_object* v_fileMap_2363_; lean_object* v_options_2364_; lean_object* v_currNamespace_2365_; lean_object* v_openDecls_2366_; lean_object* v_initHeartbeats_2367_; lean_object* v_maxHeartbeats_2368_; lean_object* v_quotContext_2369_; lean_object* v_currMacroScope_2370_; lean_object* v_cancelTk_x3f_2371_; lean_object* v_inheritedTraceOptions_2372_; uint16_t v___y_2374_; lean_object* v___y_2375_; uint8_t v___y_2376_; lean_object* v___y_2399_; 
v_toCold_2356_ = lean_ctor_get(v___y_2329_, 0);
v_currRecDepth_2357_ = lean_ctor_get(v___y_2329_, 1);
v_ref_2358_ = lean_ctor_get(v___y_2329_, 2);
v_suppressElabErrors_2359_ = lean_ctor_get_uint8(v___y_2329_, sizeof(void*)*3 + 2);
v_checkDeprecated_2360_ = lean_ctor_get_uint8(v___y_2329_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2361_ = lean_ctor_get_uint8(v___y_2329_, sizeof(void*)*3 + 4);
v_fileName_2362_ = lean_ctor_get(v_toCold_2356_, 0);
v_fileMap_2363_ = lean_ctor_get(v_toCold_2356_, 1);
v_options_2364_ = lean_ctor_get(v_toCold_2356_, 2);
v_currNamespace_2365_ = lean_ctor_get(v_toCold_2356_, 4);
v_openDecls_2366_ = lean_ctor_get(v_toCold_2356_, 5);
v_initHeartbeats_2367_ = lean_ctor_get(v_toCold_2356_, 6);
v_maxHeartbeats_2368_ = lean_ctor_get(v_toCold_2356_, 7);
v_quotContext_2369_ = lean_ctor_get(v_toCold_2356_, 8);
v_currMacroScope_2370_ = lean_ctor_get(v_toCold_2356_, 9);
v_cancelTk_x3f_2371_ = lean_ctor_get(v_toCold_2356_, 10);
v_inheritedTraceOptions_2372_ = lean_ctor_get(v_toCold_2356_, 11);
if (v_isRecordingDeps_2361_ == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = l_Lean_Meta_smartUnfolding;
lean_inc_ref(v_options_2364_);
v___x_2410_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_options_2364_, v___x_2409_, v_isRecordingDeps_2361_);
v___y_2399_ = v___x_2410_;
goto v___jp_2398_;
}
else
{
lean_object* v___x_2411_; 
lean_inc_ref(v_options_2364_);
v___x_2411_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2364_);
v___y_2399_ = v___x_2411_;
goto v___jp_2398_;
}
v___jp_2332_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2351_ = l_Lean_maxRecDepth;
v___x_2352_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___y_2334_, v___x_2351_);
v___x_2353_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2353_, 0, v_fileName_2335_);
lean_ctor_set(v___x_2353_, 1, v_fileMap_2336_);
lean_ctor_set(v___x_2353_, 2, v___y_2334_);
lean_ctor_set(v___x_2353_, 3, v___x_2352_);
lean_ctor_set(v___x_2353_, 4, v_currNamespace_2337_);
lean_ctor_set(v___x_2353_, 5, v_openDecls_2338_);
lean_ctor_set(v___x_2353_, 6, v_initHeartbeats_2339_);
lean_ctor_set(v___x_2353_, 7, v_maxHeartbeats_2340_);
lean_ctor_set(v___x_2353_, 8, v_quotContext_2341_);
lean_ctor_set(v___x_2353_, 9, v_currMacroScope_2342_);
lean_ctor_set(v___x_2353_, 10, v_cancelTk_x3f_2343_);
lean_ctor_set(v___x_2353_, 11, v_inheritedTraceOptions_2344_);
lean_inc(v_ref_2346_);
lean_inc(v_currRecDepth_2345_);
v___x_2354_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v_currRecDepth_2345_);
lean_ctor_set(v___x_2354_, 2, v_ref_2346_);
lean_ctor_set_uint16(v___x_2354_, sizeof(void*)*3, v___y_2333_);
lean_ctor_set_uint8(v___x_2354_, sizeof(void*)*3 + 2, v_suppressElabErrors_2347_);
lean_ctor_set_uint8(v___x_2354_, sizeof(void*)*3 + 3, v_checkDeprecated_2348_);
lean_ctor_set_uint8(v___x_2354_, sizeof(void*)*3 + 4, v_isRecordingDeps_2349_);
v___x_2355_ = l_Lean_MVarId_refl(v_mvarId_2325_, v___x_2326_, v___y_2327_, v___y_2328_, v___x_2354_, v___y_2350_);
lean_dec_ref_known(v___x_2354_, 3);
return v___x_2355_;
}
v___jp_2373_:
{
lean_object* v___x_2377_; lean_object* v_env_2378_; lean_object* v_nextMacroScope_2379_; lean_object* v_ngen_2380_; lean_object* v_auxDeclNGen_2381_; lean_object* v_traceState_2382_; lean_object* v_recordedDeps_2383_; lean_object* v_messages_2384_; lean_object* v_infoState_2385_; lean_object* v_snapshotTasks_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2396_; 
v___x_2377_ = lean_st_ref_take(v___y_2330_);
v_env_2378_ = lean_ctor_get(v___x_2377_, 0);
v_nextMacroScope_2379_ = lean_ctor_get(v___x_2377_, 1);
v_ngen_2380_ = lean_ctor_get(v___x_2377_, 2);
v_auxDeclNGen_2381_ = lean_ctor_get(v___x_2377_, 3);
v_traceState_2382_ = lean_ctor_get(v___x_2377_, 4);
v_recordedDeps_2383_ = lean_ctor_get(v___x_2377_, 6);
v_messages_2384_ = lean_ctor_get(v___x_2377_, 7);
v_infoState_2385_ = lean_ctor_get(v___x_2377_, 8);
v_snapshotTasks_2386_ = lean_ctor_get(v___x_2377_, 9);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; 
v_unused_2397_ = lean_ctor_get(v___x_2377_, 5);
lean_dec(v_unused_2397_);
v___x_2388_ = v___x_2377_;
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_snapshotTasks_2386_);
lean_inc(v_infoState_2385_);
lean_inc(v_messages_2384_);
lean_inc(v_recordedDeps_2383_);
lean_inc(v_traceState_2382_);
lean_inc(v_auxDeclNGen_2381_);
lean_inc(v_ngen_2380_);
lean_inc(v_nextMacroScope_2379_);
lean_inc(v_env_2378_);
lean_dec(v___x_2377_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2390_ = l_Lean_Kernel_enableDiag(v_env_2378_, v___y_2376_);
v___x_2391_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 5, v___x_2391_);
lean_ctor_set(v___x_2388_, 0, v___x_2390_);
v___x_2393_ = v___x_2388_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_nextMacroScope_2379_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_ngen_2380_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v_auxDeclNGen_2381_);
lean_ctor_set(v_reuseFailAlloc_2395_, 4, v_traceState_2382_);
lean_ctor_set(v_reuseFailAlloc_2395_, 5, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2395_, 6, v_recordedDeps_2383_);
lean_ctor_set(v_reuseFailAlloc_2395_, 7, v_messages_2384_);
lean_ctor_set(v_reuseFailAlloc_2395_, 8, v_infoState_2385_);
lean_ctor_set(v_reuseFailAlloc_2395_, 9, v_snapshotTasks_2386_);
v___x_2393_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_st_ref_put(v___y_2330_, v___x_2393_);
lean_inc_ref(v_inheritedTraceOptions_2372_);
lean_inc(v_cancelTk_x3f_2371_);
lean_inc(v_currMacroScope_2370_);
lean_inc(v_quotContext_2369_);
lean_inc(v_maxHeartbeats_2368_);
lean_inc(v_initHeartbeats_2367_);
lean_inc(v_openDecls_2366_);
lean_inc(v_currNamespace_2365_);
lean_inc_ref(v_fileMap_2363_);
lean_inc_ref(v_fileName_2362_);
v___y_2333_ = v___y_2374_;
v___y_2334_ = v___y_2375_;
v_fileName_2335_ = v_fileName_2362_;
v_fileMap_2336_ = v_fileMap_2363_;
v_currNamespace_2337_ = v_currNamespace_2365_;
v_openDecls_2338_ = v_openDecls_2366_;
v_initHeartbeats_2339_ = v_initHeartbeats_2367_;
v_maxHeartbeats_2340_ = v_maxHeartbeats_2368_;
v_quotContext_2341_ = v_quotContext_2369_;
v_currMacroScope_2342_ = v_currMacroScope_2370_;
v_cancelTk_x3f_2343_ = v_cancelTk_x3f_2371_;
v_inheritedTraceOptions_2344_ = v_inheritedTraceOptions_2372_;
v_currRecDepth_2345_ = v_currRecDepth_2357_;
v_ref_2346_ = v_ref_2358_;
v_suppressElabErrors_2347_ = v_suppressElabErrors_2359_;
v_checkDeprecated_2348_ = v_checkDeprecated_2360_;
v_isRecordingDeps_2349_ = v_isRecordingDeps_2361_;
v___y_2350_ = v___y_2330_;
goto v___jp_2332_;
}
}
}
v___jp_2398_:
{
uint16_t v___x_2400_; lean_object* v___x_2401_; lean_object* v_env_2402_; uint8_t v___x_2403_; uint16_t v___x_2404_; uint16_t v___x_2405_; uint16_t v___x_2406_; uint8_t v___x_2407_; 
v___x_2400_ = l_Lean_OptionFlags_ofOptions(v___y_2399_);
v___x_2401_ = lean_st_ref_get(v___y_2330_);
v_env_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc_ref(v_env_2402_);
lean_dec(v___x_2401_);
v___x_2403_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2402_);
lean_dec_ref(v_env_2402_);
v___x_2404_ = 512;
v___x_2405_ = lean_uint16_land(v___x_2400_, v___x_2404_);
v___x_2406_ = 0;
v___x_2407_ = lean_uint16_dec_eq(v___x_2405_, v___x_2406_);
if (v___x_2407_ == 0)
{
if (v___x_2403_ == 0)
{
v___y_2374_ = v___x_2400_;
v___y_2375_ = v___y_2399_;
v___y_2376_ = v___x_2326_;
goto v___jp_2373_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2372_);
lean_inc(v_cancelTk_x3f_2371_);
lean_inc(v_currMacroScope_2370_);
lean_inc(v_quotContext_2369_);
lean_inc(v_maxHeartbeats_2368_);
lean_inc(v_initHeartbeats_2367_);
lean_inc(v_openDecls_2366_);
lean_inc(v_currNamespace_2365_);
lean_inc_ref(v_fileMap_2363_);
lean_inc_ref(v_fileName_2362_);
v___y_2333_ = v___x_2400_;
v___y_2334_ = v___y_2399_;
v_fileName_2335_ = v_fileName_2362_;
v_fileMap_2336_ = v_fileMap_2363_;
v_currNamespace_2337_ = v_currNamespace_2365_;
v_openDecls_2338_ = v_openDecls_2366_;
v_initHeartbeats_2339_ = v_initHeartbeats_2367_;
v_maxHeartbeats_2340_ = v_maxHeartbeats_2368_;
v_quotContext_2341_ = v_quotContext_2369_;
v_currMacroScope_2342_ = v_currMacroScope_2370_;
v_cancelTk_x3f_2343_ = v_cancelTk_x3f_2371_;
v_inheritedTraceOptions_2344_ = v_inheritedTraceOptions_2372_;
v_currRecDepth_2345_ = v_currRecDepth_2357_;
v_ref_2346_ = v_ref_2358_;
v_suppressElabErrors_2347_ = v_suppressElabErrors_2359_;
v_checkDeprecated_2348_ = v_checkDeprecated_2360_;
v_isRecordingDeps_2349_ = v_isRecordingDeps_2361_;
v___y_2350_ = v___y_2330_;
goto v___jp_2332_;
}
}
else
{
if (v___x_2403_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2372_);
lean_inc(v_cancelTk_x3f_2371_);
lean_inc(v_currMacroScope_2370_);
lean_inc(v_quotContext_2369_);
lean_inc(v_maxHeartbeats_2368_);
lean_inc(v_initHeartbeats_2367_);
lean_inc(v_openDecls_2366_);
lean_inc(v_currNamespace_2365_);
lean_inc_ref(v_fileMap_2363_);
lean_inc_ref(v_fileName_2362_);
v___y_2333_ = v___x_2400_;
v___y_2334_ = v___y_2399_;
v_fileName_2335_ = v_fileName_2362_;
v_fileMap_2336_ = v_fileMap_2363_;
v_currNamespace_2337_ = v_currNamespace_2365_;
v_openDecls_2338_ = v_openDecls_2366_;
v_initHeartbeats_2339_ = v_initHeartbeats_2367_;
v_maxHeartbeats_2340_ = v_maxHeartbeats_2368_;
v_quotContext_2341_ = v_quotContext_2369_;
v_currMacroScope_2342_ = v_currMacroScope_2370_;
v_cancelTk_x3f_2343_ = v_cancelTk_x3f_2371_;
v_inheritedTraceOptions_2344_ = v_inheritedTraceOptions_2372_;
v_currRecDepth_2345_ = v_currRecDepth_2357_;
v_ref_2346_ = v_ref_2358_;
v_suppressElabErrors_2347_ = v_suppressElabErrors_2359_;
v_checkDeprecated_2348_ = v_checkDeprecated_2360_;
v_isRecordingDeps_2349_ = v_isRecordingDeps_2361_;
v___y_2350_ = v___y_2330_;
goto v___jp_2332_;
}
else
{
uint8_t v___x_2408_; 
v___x_2408_ = 0;
v___y_2374_ = v___x_2400_;
v___y_2375_ = v___y_2399_;
v___y_2376_ = v___x_2408_;
goto v___jp_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object* v_mvarId_2412_, lean_object* v___x_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
uint8_t v___x_10259__boxed_2419_; lean_object* v_res_2420_; 
v___x_10259__boxed_2419_ = lean_unbox(v___x_2413_);
v_res_2420_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_mvarId_2412_, v___x_10259__boxed_2419_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
return v_res_2420_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2421_; double v___x_2422_; 
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_float_of_nat(v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object* v_cls_2426_, lean_object* v_msg_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_ref_2433_; lean_object* v___x_2434_; lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2480_; 
v_ref_2433_ = lean_ctor_get(v___y_2430_, 2);
v___x_2434_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msg_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2480_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2480_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v_traceState_2440_; lean_object* v_env_2441_; lean_object* v_nextMacroScope_2442_; lean_object* v_ngen_2443_; lean_object* v_auxDeclNGen_2444_; lean_object* v_cache_2445_; lean_object* v_recordedDeps_2446_; lean_object* v_messages_2447_; lean_object* v_infoState_2448_; lean_object* v_snapshotTasks_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2479_; 
v___x_2439_ = lean_st_ref_take(v___y_2431_);
v_traceState_2440_ = lean_ctor_get(v___x_2439_, 4);
v_env_2441_ = lean_ctor_get(v___x_2439_, 0);
v_nextMacroScope_2442_ = lean_ctor_get(v___x_2439_, 1);
v_ngen_2443_ = lean_ctor_get(v___x_2439_, 2);
v_auxDeclNGen_2444_ = lean_ctor_get(v___x_2439_, 3);
v_cache_2445_ = lean_ctor_get(v___x_2439_, 5);
v_recordedDeps_2446_ = lean_ctor_get(v___x_2439_, 6);
v_messages_2447_ = lean_ctor_get(v___x_2439_, 7);
v_infoState_2448_ = lean_ctor_get(v___x_2439_, 8);
v_snapshotTasks_2449_ = lean_ctor_get(v___x_2439_, 9);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2451_ = v___x_2439_;
v_isShared_2452_ = v_isSharedCheck_2479_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_snapshotTasks_2449_);
lean_inc(v_infoState_2448_);
lean_inc(v_messages_2447_);
lean_inc(v_recordedDeps_2446_);
lean_inc(v_cache_2445_);
lean_inc(v_traceState_2440_);
lean_inc(v_auxDeclNGen_2444_);
lean_inc(v_ngen_2443_);
lean_inc(v_nextMacroScope_2442_);
lean_inc(v_env_2441_);
lean_dec(v___x_2439_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2479_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
uint64_t v_tid_2453_; lean_object* v_traces_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2478_; 
v_tid_2453_ = lean_ctor_get_uint64(v_traceState_2440_, sizeof(void*)*1);
v_traces_2454_ = lean_ctor_get(v_traceState_2440_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_traceState_2440_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2456_ = v_traceState_2440_;
v_isShared_2457_ = v_isSharedCheck_2478_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_traces_2454_);
lean_dec(v_traceState_2440_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2478_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; double v___x_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2458_ = lean_box(0);
v___x_2459_ = lean_box(0);
v___x_2460_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0);
v___x_2461_ = 0;
v___x_2462_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__1));
v___x_2463_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2463_, 0, v_cls_2426_);
lean_ctor_set(v___x_2463_, 1, v___x_2459_);
lean_ctor_set(v___x_2463_, 2, v___x_2462_);
lean_ctor_set_float(v___x_2463_, sizeof(void*)*3, v___x_2460_);
lean_ctor_set_float(v___x_2463_, sizeof(void*)*3 + 8, v___x_2460_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*3 + 16, v___x_2461_);
v___x_2464_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__2));
v___x_2465_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v_a_2435_);
lean_ctor_set(v___x_2465_, 2, v___x_2464_);
lean_inc(v_ref_2433_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v_ref_2433_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = l_Lean_PersistentArray_push___redArg(v_traces_2454_, v___x_2466_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2467_);
v___x_2469_ = v___x_2456_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2467_);
lean_ctor_set_uint64(v_reuseFailAlloc_2477_, sizeof(void*)*1, v_tid_2453_);
v___x_2469_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2471_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v___x_2469_);
v___x_2471_ = v___x_2451_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_env_2441_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_nextMacroScope_2442_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_ngen_2443_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_auxDeclNGen_2444_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2476_, 5, v_cache_2445_);
lean_ctor_set(v_reuseFailAlloc_2476_, 6, v_recordedDeps_2446_);
lean_ctor_set(v_reuseFailAlloc_2476_, 7, v_messages_2447_);
lean_ctor_set(v_reuseFailAlloc_2476_, 8, v_infoState_2448_);
lean_ctor_set(v_reuseFailAlloc_2476_, 9, v_snapshotTasks_2449_);
v___x_2471_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2472_ = lean_st_ref_put(v___y_2431_, v___x_2471_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2458_);
v___x_2474_ = v___x_2437_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2458_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_cls_2481_, lean_object* v_msg_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_cls_2481_, v_msg_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
return v_res_2488_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0));
v___x_2491_ = l_Lean_stringToMessageData(v___x_2490_);
return v___x_2491_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2));
v___x_2494_ = l_Lean_stringToMessageData(v___x_2493_);
return v___x_2494_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4));
v___x_2497_ = l_Lean_stringToMessageData(v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object* v_a_2498_, lean_object* v___x_2499_, lean_object* v___f_2500_, lean_object* v_fixEq_x3f_2501_, lean_object* v_declName_2502_, lean_object* v___x_2503_, lean_object* v___x_2504_, lean_object* v_fixedParamPerms_2505_, lean_object* v_declNameNonRec_2506_, lean_object* v_____r_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v_mvarId_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; 
if (lean_obj_tag(v_fixEq_x3f_2501_) == 1)
{
lean_object* v_val_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2657_; 
v_val_2602_ = lean_ctor_get(v_fixEq_x3f_2501_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_fixEq_x3f_2501_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2604_ = v_fixEq_x3f_2501_;
v_isShared_2605_ = v_isSharedCheck_2657_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_val_2602_);
lean_dec(v_fixEq_x3f_2501_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2657_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; 
v___x_2606_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_2502_, v___x_2503_, v___x_2504_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___x_2624_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
lean_inc_ref(v___f_2500_);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
v___x_2624_ = lean_apply_5(v___f_2500_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, lean_box(0));
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; uint8_t v___x_2626_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 1);
v___x_2626_ = lean_unbox(v_a_2625_);
lean_dec(v_a_2625_);
if (v___x_2626_ == 0)
{
lean_del_object(v___x_2604_);
v___y_2609_ = v___y_2508_;
v___y_2610_ = v___y_2509_;
v___y_2611_ = v___y_2510_;
v___y_2612_ = v___y_2511_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2627_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5);
lean_inc(v_a_2607_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v_a_2607_);
v___x_2629_ = v___x_2604_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2607_);
v___x_2629_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2627_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
lean_inc(v___x_2499_);
v___x_2631_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2499_, v___x_2630_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_dec_ref_known(v___x_2631_, 1);
v___y_2609_ = v___y_2508_;
v___y_2610_ = v___y_2509_;
v___y_2611_ = v___y_2510_;
v___y_2612_ = v___y_2511_;
goto v___jp_2608_;
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_a_2607_);
lean_dec(v_val_2602_);
lean_dec(v_declNameNonRec_2506_);
lean_dec_ref(v_fixedParamPerms_2505_);
lean_dec_ref(v___f_2500_);
lean_dec(v___x_2499_);
lean_dec_ref(v_a_2498_);
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec(v_declNameNonRec_2506_);
lean_dec_ref(v_fixedParamPerms_2505_);
lean_dec_ref(v___f_2500_);
lean_dec(v___x_2499_);
lean_dec_ref(v_a_2498_);
v_a_2641_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2624_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2624_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
v___jp_2608_:
{
lean_object* v_numFixed_2613_; lean_object* v___x_2614_; 
v_numFixed_2613_ = lean_ctor_get(v_fixedParamPerms_2505_, 0);
lean_inc(v_numFixed_2613_);
lean_dec_ref(v_fixedParamPerms_2505_);
v___x_2614_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(v_declNameNonRec_2506_, v_val_2602_, v_numFixed_2613_, v_a_2607_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v_mvarId_2574_ = v_a_2615_;
v___y_2575_ = v___y_2609_;
v___y_2576_ = v___y_2610_;
v___y_2577_ = v___y_2611_;
v___y_2578_ = v___y_2612_;
goto v___jp_2573_;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v___f_2500_);
lean_dec(v___x_2499_);
lean_dec_ref(v_a_2498_);
v_a_2616_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2614_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2614_);
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
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec(v_declNameNonRec_2506_);
lean_dec_ref(v_fixedParamPerms_2505_);
lean_dec_ref(v___f_2500_);
lean_dec(v___x_2499_);
lean_dec_ref(v_a_2498_);
v_a_2649_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2606_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2606_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
else
{
lean_object* v___x_2658_; 
lean_dec_ref(v_fixedParamPerms_2505_);
lean_dec(v___x_2503_);
lean_dec(v_fixEq_x3f_2501_);
v___x_2658_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_2502_, v_declNameNonRec_2506_, v___x_2504_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___x_2675_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
lean_inc_ref(v___f_2500_);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
v___x_2675_ = lean_apply_5(v___f_2500_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, lean_box(0));
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; uint8_t v___x_2677_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2677_ = lean_unbox(v_a_2676_);
lean_dec(v_a_2676_);
if (v___x_2677_ == 0)
{
v___y_2661_ = v___y_2508_;
v___y_2662_ = v___y_2509_;
v___y_2663_ = v___y_2510_;
v___y_2664_ = v___y_2511_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2678_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5);
lean_inc(v_a_2659_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_a_2659_);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
lean_inc(v___x_2499_);
v___x_2681_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2499_, v___x_2680_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_dec_ref_known(v___x_2681_, 1);
v___y_2661_ = v___y_2508_;
v___y_2662_ = v___y_2509_;
v___y_2663_ = v___y_2510_;
v___y_2664_ = v___y_2511_;
goto v___jp_2660_;
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v_a_2659_);
lean_dec_ref(v___f_2500_);
lean_dec(v___x_2499_);
lean_dec_ref(v_a_2498_);
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2681_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2681_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
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
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v_a_2659_);
lean_dec_ref(v___f_2500_);
lean_dec(v___x_2499_);
lean_dec_ref(v_a_2498_);
v_a_2690_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2675_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2675_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
v___jp_2660_:
{
lean_object* v___x_2665_; 
v___x_2665_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_a_2659_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v_mvarId_2574_ = v_a_2666_;
v___y_2575_ = v___y_2661_;
v___y_2576_ = v___y_2662_;
v___y_2577_ = v___y_2663_;
v___y_2578_ = v___y_2664_;
goto v___jp_2573_;
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec_ref(v___f_2500_);
lean_dec(v___x_2499_);
lean_dec_ref(v_a_2498_);
v_a_2667_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2665_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2665_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec_ref(v___f_2500_);
lean_dec(v___x_2499_);
lean_dec_ref(v_a_2498_);
v_a_2698_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2658_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2658_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
v___jp_2513_:
{
if (lean_obj_tag(v___y_2518_) == 0)
{
lean_object* v_toCold_2519_; lean_object* v_options_2520_; uint8_t v_hasTrace_2521_; 
lean_dec_ref_known(v___y_2518_, 1);
v_toCold_2519_ = lean_ctor_get(v___y_2517_, 0);
v_options_2520_ = lean_ctor_get(v_toCold_2519_, 2);
v_hasTrace_2521_ = lean_ctor_get_uint8(v_options_2520_, sizeof(void*)*1);
if (v_hasTrace_2521_ == 0)
{
lean_object* v___x_2522_; 
lean_dec(v___x_2499_);
v___x_2522_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2498_, v___y_2515_);
return v___x_2522_;
}
else
{
lean_object* v_inheritedTraceOptions_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_inheritedTraceOptions_2523_ = lean_ctor_get(v_toCold_2519_, 11);
v___x_2524_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
lean_inc(v___x_2499_);
v___x_2525_ = l_Lean_Name_append(v___x_2524_, v___x_2499_);
v___x_2526_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2523_, v_options_2520_, v___x_2525_);
lean_dec(v___x_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; 
lean_dec(v___x_2499_);
v___x_2527_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2498_, v___y_2515_);
return v___x_2527_;
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1);
v___x_2529_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2499_, v___x_2528_, v___y_2516_, v___y_2515_, v___y_2517_, v___y_2514_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v___x_2530_; 
lean_dec_ref_known(v___x_2529_, 1);
v___x_2530_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2498_, v___y_2515_);
return v___x_2530_;
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v_a_2498_);
v_a_2531_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2529_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2529_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v___x_2499_);
lean_dec_ref(v_a_2498_);
v_a_2539_ = lean_ctor_get(v___y_2518_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___y_2518_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___y_2518_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___y_2518_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
v___jp_2547_:
{
lean_object* v___x_2553_; uint8_t v_transparency_2554_; uint8_t v___x_2555_; uint8_t v___x_2556_; uint8_t v___x_2557_; 
v___x_2553_ = l_Lean_Meta_Context_config(v___y_2548_);
v_transparency_2554_ = lean_ctor_get_uint8(v___x_2553_, 9);
lean_dec_ref(v___x_2553_);
v___x_2555_ = 0;
v___x_2556_ = 1;
v___x_2557_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2554_, v___x_2555_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v___y_2550_, v___x_2556_, v___y_2548_, v___y_2549_, v___y_2552_, v___y_2551_);
v___y_2514_ = v___y_2551_;
v___y_2515_ = v___y_2549_;
v___y_2516_ = v___y_2548_;
v___y_2517_ = v___y_2552_;
v___y_2518_ = v___x_2558_;
goto v___jp_2513_;
}
else
{
lean_object* v_keyedConfig_2559_; uint8_t v_trackZetaDelta_2560_; lean_object* v_zetaDeltaSet_2561_; lean_object* v_lctx_2562_; lean_object* v_localInstances_2563_; lean_object* v_defEqCtx_x3f_2564_; lean_object* v_synthPendingDepth_2565_; lean_object* v_customCanUnfoldPredicate_x3f_2566_; uint8_t v_univApprox_2567_; uint8_t v_inTypeClassResolution_2568_; uint8_t v_cacheInferType_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v_keyedConfig_2559_ = lean_ctor_get(v___y_2548_, 0);
v_trackZetaDelta_2560_ = lean_ctor_get_uint8(v___y_2548_, sizeof(void*)*7);
v_zetaDeltaSet_2561_ = lean_ctor_get(v___y_2548_, 1);
v_lctx_2562_ = lean_ctor_get(v___y_2548_, 2);
v_localInstances_2563_ = lean_ctor_get(v___y_2548_, 3);
v_defEqCtx_x3f_2564_ = lean_ctor_get(v___y_2548_, 4);
v_synthPendingDepth_2565_ = lean_ctor_get(v___y_2548_, 5);
v_customCanUnfoldPredicate_x3f_2566_ = lean_ctor_get(v___y_2548_, 6);
v_univApprox_2567_ = lean_ctor_get_uint8(v___y_2548_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2568_ = lean_ctor_get_uint8(v___y_2548_, sizeof(void*)*7 + 2);
v_cacheInferType_2569_ = lean_ctor_get_uint8(v___y_2548_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2559_);
v___x_2570_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2555_, v_keyedConfig_2559_);
lean_inc(v_customCanUnfoldPredicate_x3f_2566_);
lean_inc(v_synthPendingDepth_2565_);
lean_inc(v_defEqCtx_x3f_2564_);
lean_inc_ref(v_localInstances_2563_);
lean_inc_ref(v_lctx_2562_);
lean_inc(v_zetaDeltaSet_2561_);
v___x_2571_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_ctor_set(v___x_2571_, 1, v_zetaDeltaSet_2561_);
lean_ctor_set(v___x_2571_, 2, v_lctx_2562_);
lean_ctor_set(v___x_2571_, 3, v_localInstances_2563_);
lean_ctor_set(v___x_2571_, 4, v_defEqCtx_x3f_2564_);
lean_ctor_set(v___x_2571_, 5, v_synthPendingDepth_2565_);
lean_ctor_set(v___x_2571_, 6, v_customCanUnfoldPredicate_x3f_2566_);
lean_ctor_set_uint8(v___x_2571_, sizeof(void*)*7, v_trackZetaDelta_2560_);
lean_ctor_set_uint8(v___x_2571_, sizeof(void*)*7 + 1, v_univApprox_2567_);
lean_ctor_set_uint8(v___x_2571_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2568_);
lean_ctor_set_uint8(v___x_2571_, sizeof(void*)*7 + 3, v_cacheInferType_2569_);
v___x_2572_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v___y_2550_, v___x_2556_, v___x_2571_, v___y_2549_, v___y_2552_, v___y_2551_);
lean_dec_ref_known(v___x_2571_, 7);
v___y_2514_ = v___y_2551_;
v___y_2515_ = v___y_2549_;
v___y_2516_ = v___y_2548_;
v___y_2517_ = v___y_2552_;
v___y_2518_ = v___x_2572_;
goto v___jp_2513_;
}
}
v___jp_2573_:
{
lean_object* v___x_2579_; 
lean_inc(v___y_2578_);
lean_inc_ref(v___y_2577_);
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
v___x_2579_ = lean_apply_5(v___f_2500_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, lean_box(0));
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; uint8_t v___x_2581_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = lean_unbox(v_a_2580_);
lean_dec(v_a_2580_);
if (v___x_2581_ == 0)
{
v___y_2548_ = v___y_2575_;
v___y_2549_ = v___y_2576_;
v___y_2550_ = v_mvarId_2574_;
v___y_2551_ = v___y_2578_;
v___y_2552_ = v___y_2577_;
goto v___jp_2547_;
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2582_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3);
lean_inc(v_mvarId_2574_);
v___x_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2583_, 0, v_mvarId_2574_);
v___x_2584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
lean_inc(v___x_2499_);
v___x_2585_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2499_, v___x_2584_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_dec_ref_known(v___x_2585_, 1);
v___y_2548_ = v___y_2575_;
v___y_2549_ = v___y_2576_;
v___y_2550_ = v_mvarId_2574_;
v___y_2551_ = v___y_2578_;
v___y_2552_ = v___y_2577_;
goto v___jp_2547_;
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v_mvarId_2574_);
lean_dec(v___x_2499_);
lean_dec_ref(v_a_2498_);
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
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
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_mvarId_2574_);
lean_dec(v___x_2499_);
lean_dec_ref(v_a_2498_);
v_a_2594_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2579_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2579_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object* v_a_2706_, lean_object* v___x_2707_, lean_object* v___f_2708_, lean_object* v_fixEq_x3f_2709_, lean_object* v_declName_2710_, lean_object* v___x_2711_, lean_object* v___x_2712_, lean_object* v_fixedParamPerms_2713_, lean_object* v_declNameNonRec_2714_, lean_object* v_____r_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2706_, v___x_2707_, v___f_2708_, v_fixEq_x3f_2709_, v_declName_2710_, v___x_2711_, v___x_2712_, v_fixedParamPerms_2713_, v_declNameNonRec_2714_, v_____r_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
return v_res_2721_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__0));
v___x_2724_ = l_Lean_stringToMessageData(v___x_2723_);
return v___x_2724_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__2));
v___x_2727_ = l_Lean_stringToMessageData(v___x_2726_);
return v___x_2727_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__8));
v___x_2738_ = l_Lean_stringToMessageData(v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(lean_object* v_declName_2739_, lean_object* v_a_2740_, lean_object* v___x_2741_, lean_object* v_fixEq_x3f_2742_, lean_object* v_fixedParamPerms_2743_, lean_object* v_declNameNonRec_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___y_2751_; lean_object* v_a_2752_; lean_object* v___y_2764_; lean_object* v___x_2766_; 
lean_inc(v___x_2741_);
v___x_2766_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2740_, v___x_2741_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2795_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
v___x_2768_ = l_Lean_Expr_mvarId_x21(v_a_2767_);
v___x_2769_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6));
v___f_2770_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__7));
v___x_2771_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_2769_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2795_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2795_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_unbox(v_a_2772_);
lean_dec(v_a_2772_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
lean_del_object(v___x_2774_);
v___x_2777_ = lean_box(0);
lean_inc(v_declName_2739_);
v___x_2778_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2767_, v___x_2769_, v___f_2770_, v_fixEq_x3f_2742_, v_declName_2739_, v___x_2741_, v___x_2768_, v_fixedParamPerms_2743_, v_declNameNonRec_2744_, v___x_2777_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
v___y_2764_ = v___x_2778_;
goto v___jp_2763_;
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9);
lean_inc(v___x_2768_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set_tag(v___x_2774_, 1);
lean_ctor_set(v___x_2774_, 0, v___x_2768_);
v___x_2781_ = v___x_2774_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2768_);
v___x_2781_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2779_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2769_, v___x_2782_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v___x_2783_, 1);
lean_inc(v_declName_2739_);
v___x_2785_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2767_, v___x_2769_, v___f_2770_, v_fixEq_x3f_2742_, v_declName_2739_, v___x_2741_, v___x_2768_, v_fixedParamPerms_2743_, v_declNameNonRec_2744_, v_a_2784_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
v___y_2764_ = v___x_2785_;
goto v___jp_2763_;
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec(v___x_2768_);
lean_dec(v_a_2767_);
lean_dec(v_declNameNonRec_2744_);
lean_dec_ref(v_fixedParamPerms_2743_);
lean_dec(v_fixEq_x3f_2742_);
lean_dec(v___x_2741_);
v_a_2786_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2783_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2783_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
lean_inc(v_a_2786_);
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
v___y_2751_ = v___x_2791_;
v_a_2752_ = v_a_2786_;
goto v___jp_2750_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2796_; 
lean_dec(v_declNameNonRec_2744_);
lean_dec_ref(v_fixedParamPerms_2743_);
lean_dec(v_fixEq_x3f_2742_);
lean_dec(v___x_2741_);
v_a_2796_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2796_);
v___y_2751_ = v___x_2766_;
v_a_2752_ = v_a_2796_;
goto v___jp_2750_;
}
v___jp_2750_:
{
uint8_t v___x_2753_; 
v___x_2753_ = l_Lean_Exception_isInterrupt(v_a_2752_);
if (v___x_2753_ == 0)
{
uint8_t v___x_2754_; 
lean_inc_ref(v_a_2752_);
v___x_2754_ = l_Lean_Exception_isRuntime(v_a_2752_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec_ref(v___y_2751_);
v___x_2755_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1);
v___x_2756_ = l_Lean_MessageData_ofConstName(v_declName_2739_, v___x_2754_);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = l_Lean_Exception_toMessageData(v_a_2752_);
v___x_2761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_2761_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
return v___x_2762_;
}
else
{
lean_dec_ref(v_a_2752_);
lean_dec(v_declName_2739_);
return v___y_2751_;
}
}
else
{
lean_dec_ref(v_a_2752_);
lean_dec(v_declName_2739_);
return v___y_2751_;
}
}
v___jp_2763_:
{
if (lean_obj_tag(v___y_2764_) == 0)
{
lean_dec(v_declName_2739_);
return v___y_2764_;
}
else
{
lean_object* v_a_2765_; 
v_a_2765_ = lean_ctor_get(v___y_2764_, 0);
lean_inc(v_a_2765_);
v___y_2751_ = v___y_2764_;
v_a_2752_ = v_a_2765_;
goto v___jp_2750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed(lean_object* v_declName_2797_, lean_object* v_a_2798_, lean_object* v___x_2799_, lean_object* v_fixEq_x3f_2800_, lean_object* v_fixedParamPerms_2801_, lean_object* v_declNameNonRec_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(v_declName_2797_, v_a_2798_, v___x_2799_, v_fixEq_x3f_2800_, v_fixedParamPerms_2801_, v_declNameNonRec_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4(lean_object* v_levelParams_2809_, lean_object* v_declName_2810_, lean_object* v_fixEq_x3f_2811_, lean_object* v_fixedParamPerms_2812_, lean_object* v_declNameNonRec_2813_, lean_object* v_name_2814_, lean_object* v_xs_2815_, lean_object* v_body_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; lean_object* v_us_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2822_ = lean_box(0);
lean_inc(v_levelParams_2809_);
v_us_2823_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(v_levelParams_2809_, v___x_2822_);
lean_inc(v_declName_2810_);
v___x_2824_ = l_Lean_mkConst(v_declName_2810_, v_us_2823_);
v___x_2825_ = l_Lean_mkAppN(v___x_2824_, v_xs_2815_);
v___x_2826_ = l_Lean_Meta_mkEq(v___x_2825_, v_body_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; lean_object* v___f_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc_n(v_a_2827_, 2);
lean_dec_ref_known(v___x_2826_, 1);
v___x_2828_ = lean_box(0);
v___f_2829_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed), 11, 6);
lean_closure_set(v___f_2829_, 0, v_declName_2810_);
lean_closure_set(v___f_2829_, 1, v_a_2827_);
lean_closure_set(v___f_2829_, 2, v___x_2828_);
lean_closure_set(v___f_2829_, 3, v_fixEq_x3f_2811_);
lean_closure_set(v___f_2829_, 4, v_fixedParamPerms_2812_);
lean_closure_set(v___f_2829_, 5, v_declNameNonRec_2813_);
v___x_2830_ = 0;
v___x_2831_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v___f_2829_, v___x_2830_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; uint8_t v___x_2833_; uint8_t v___x_2834_; lean_object* v___x_2835_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
v___x_2833_ = 1;
v___x_2834_ = 1;
v___x_2835_ = l_Lean_Meta_mkForallFVars(v_xs_2815_, v_a_2827_, v___x_2830_, v___x_2833_, v___x_2833_, v___x_2834_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2837_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v___x_2837_ = l_Lean_Meta_letToHave(v_a_2836_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2839_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2837_, 1);
v___x_2839_ = l_Lean_Meta_mkLambdaFVars(v_xs_2815_, v_a_2832_, v___x_2830_, v___x_2833_, v___x_2830_, v___x_2833_, v___x_2834_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
lean_inc(v_name_2814_);
v___x_2841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2841_, 0, v_name_2814_);
lean_ctor_set(v___x_2841_, 1, v_levelParams_2809_);
lean_ctor_set(v___x_2841_, 2, v_a_2838_);
v___x_2842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2842_, 0, v_name_2814_);
lean_ctor_set(v___x_2842_, 1, v___x_2822_);
v___x_2843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v_a_2840_);
lean_ctor_set(v___x_2843_, 2, v___x_2842_);
v___x_2844_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v___x_2843_, v___y_2820_);
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref(v___x_2844_);
v___x_2846_ = l_Lean_addDecl(v_a_2845_, v___x_2830_, v___y_2819_, v___y_2820_);
return v___x_2846_;
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_a_2838_);
lean_dec(v_name_2814_);
lean_dec(v_levelParams_2809_);
v_a_2847_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2839_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2839_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_a_2832_);
lean_dec(v_name_2814_);
lean_dec(v_levelParams_2809_);
v_a_2855_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2837_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2837_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v_a_2832_);
lean_dec(v_name_2814_);
lean_dec(v_levelParams_2809_);
v_a_2863_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2835_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2835_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_a_2827_);
lean_dec(v_name_2814_);
lean_dec(v_levelParams_2809_);
v_a_2871_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2831_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2831_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_name_2814_);
lean_dec(v_declNameNonRec_2813_);
lean_dec_ref(v_fixedParamPerms_2812_);
lean_dec(v_fixEq_x3f_2811_);
lean_dec(v_declName_2810_);
lean_dec(v_levelParams_2809_);
v_a_2879_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2826_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2826_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4___boxed(lean_object* v_levelParams_2887_, lean_object* v_declName_2888_, lean_object* v_fixEq_x3f_2889_, lean_object* v_fixedParamPerms_2890_, lean_object* v_declNameNonRec_2891_, lean_object* v_name_2892_, lean_object* v_xs_2893_, lean_object* v_body_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4(v_levelParams_2887_, v_declName_2888_, v_fixEq_x3f_2889_, v_fixedParamPerms_2890_, v_declNameNonRec_2891_, v_name_2892_, v_xs_2893_, v_body_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec_ref(v_xs_2893_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object* v_declName_2901_, lean_object* v_info_2902_, lean_object* v_name_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_toCold_2909_; lean_object* v_levelParams_2910_; lean_object* v_value_2911_; lean_object* v_declNameNonRec_2912_; lean_object* v_fixedParamPerms_2913_; lean_object* v_fixEq_x3f_2914_; lean_object* v_currRecDepth_2915_; lean_object* v_ref_2916_; uint8_t v_suppressElabErrors_2917_; uint8_t v_checkDeprecated_2918_; uint8_t v_isRecordingDeps_2919_; lean_object* v_fileName_2920_; lean_object* v_fileMap_2921_; lean_object* v_options_2922_; lean_object* v_currNamespace_2923_; lean_object* v_openDecls_2924_; lean_object* v_initHeartbeats_2925_; lean_object* v_maxHeartbeats_2926_; lean_object* v_quotContext_2927_; lean_object* v_currMacroScope_2928_; lean_object* v_cancelTk_x3f_2929_; lean_object* v_inheritedTraceOptions_2930_; lean_object* v___f_2931_; uint8_t v___x_2932_; lean_object* v___y_2934_; uint16_t v___y_2935_; lean_object* v_fileName_2936_; lean_object* v_fileMap_2937_; lean_object* v_currNamespace_2938_; lean_object* v_openDecls_2939_; lean_object* v_initHeartbeats_2940_; lean_object* v_maxHeartbeats_2941_; lean_object* v_quotContext_2942_; lean_object* v_currMacroScope_2943_; lean_object* v_cancelTk_x3f_2944_; lean_object* v_inheritedTraceOptions_2945_; lean_object* v_currRecDepth_2946_; lean_object* v_ref_2947_; uint8_t v_suppressElabErrors_2948_; uint8_t v_checkDeprecated_2949_; uint8_t v_isRecordingDeps_2950_; lean_object* v___y_2951_; lean_object* v___y_2958_; uint16_t v___y_2959_; uint8_t v___y_2960_; lean_object* v___y_2983_; 
v_toCold_2909_ = lean_ctor_get(v_a_2906_, 0);
v_levelParams_2910_ = lean_ctor_get(v_info_2902_, 1);
lean_inc(v_levelParams_2910_);
v_value_2911_ = lean_ctor_get(v_info_2902_, 3);
lean_inc_ref(v_value_2911_);
v_declNameNonRec_2912_ = lean_ctor_get(v_info_2902_, 5);
lean_inc(v_declNameNonRec_2912_);
v_fixedParamPerms_2913_ = lean_ctor_get(v_info_2902_, 6);
lean_inc_ref(v_fixedParamPerms_2913_);
v_fixEq_x3f_2914_ = lean_ctor_get(v_info_2902_, 8);
lean_inc(v_fixEq_x3f_2914_);
lean_dec_ref(v_info_2902_);
v_currRecDepth_2915_ = lean_ctor_get(v_a_2906_, 1);
v_ref_2916_ = lean_ctor_get(v_a_2906_, 2);
v_suppressElabErrors_2917_ = lean_ctor_get_uint8(v_a_2906_, sizeof(void*)*3 + 2);
v_checkDeprecated_2918_ = lean_ctor_get_uint8(v_a_2906_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2919_ = lean_ctor_get_uint8(v_a_2906_, sizeof(void*)*3 + 4);
v_fileName_2920_ = lean_ctor_get(v_toCold_2909_, 0);
v_fileMap_2921_ = lean_ctor_get(v_toCold_2909_, 1);
v_options_2922_ = lean_ctor_get(v_toCold_2909_, 2);
v_currNamespace_2923_ = lean_ctor_get(v_toCold_2909_, 4);
v_openDecls_2924_ = lean_ctor_get(v_toCold_2909_, 5);
v_initHeartbeats_2925_ = lean_ctor_get(v_toCold_2909_, 6);
v_maxHeartbeats_2926_ = lean_ctor_get(v_toCold_2909_, 7);
v_quotContext_2927_ = lean_ctor_get(v_toCold_2909_, 8);
v_currMacroScope_2928_ = lean_ctor_get(v_toCold_2909_, 9);
v_cancelTk_x3f_2929_ = lean_ctor_get(v_toCold_2909_, 10);
v_inheritedTraceOptions_2930_ = lean_ctor_get(v_toCold_2909_, 11);
v___f_2931_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4___boxed), 13, 6);
lean_closure_set(v___f_2931_, 0, v_levelParams_2910_);
lean_closure_set(v___f_2931_, 1, v_declName_2901_);
lean_closure_set(v___f_2931_, 2, v_fixEq_x3f_2914_);
lean_closure_set(v___f_2931_, 3, v_fixedParamPerms_2913_);
lean_closure_set(v___f_2931_, 4, v_declNameNonRec_2912_);
lean_closure_set(v___f_2931_, 5, v_name_2903_);
v___x_2932_ = 0;
if (v_isRecordingDeps_2919_ == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_2922_);
v___x_2994_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_options_2922_, v___x_2993_, v_isRecordingDeps_2919_);
v___y_2983_ = v___x_2994_;
goto v___jp_2982_;
}
else
{
lean_object* v___x_2995_; 
lean_inc_ref(v_options_2922_);
v___x_2995_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2922_);
v___y_2983_ = v___x_2995_;
goto v___jp_2982_;
}
v___jp_2933_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2952_ = l_Lean_maxRecDepth;
v___x_2953_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___y_2934_, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2954_, 0, v_fileName_2936_);
lean_ctor_set(v___x_2954_, 1, v_fileMap_2937_);
lean_ctor_set(v___x_2954_, 2, v___y_2934_);
lean_ctor_set(v___x_2954_, 3, v___x_2953_);
lean_ctor_set(v___x_2954_, 4, v_currNamespace_2938_);
lean_ctor_set(v___x_2954_, 5, v_openDecls_2939_);
lean_ctor_set(v___x_2954_, 6, v_initHeartbeats_2940_);
lean_ctor_set(v___x_2954_, 7, v_maxHeartbeats_2941_);
lean_ctor_set(v___x_2954_, 8, v_quotContext_2942_);
lean_ctor_set(v___x_2954_, 9, v_currMacroScope_2943_);
lean_ctor_set(v___x_2954_, 10, v_cancelTk_x3f_2944_);
lean_ctor_set(v___x_2954_, 11, v_inheritedTraceOptions_2945_);
lean_inc(v_ref_2947_);
lean_inc(v_currRecDepth_2946_);
v___x_2955_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
lean_ctor_set(v___x_2955_, 1, v_currRecDepth_2946_);
lean_ctor_set(v___x_2955_, 2, v_ref_2947_);
lean_ctor_set_uint16(v___x_2955_, sizeof(void*)*3, v___y_2935_);
lean_ctor_set_uint8(v___x_2955_, sizeof(void*)*3 + 2, v_suppressElabErrors_2948_);
lean_ctor_set_uint8(v___x_2955_, sizeof(void*)*3 + 3, v_checkDeprecated_2949_);
lean_ctor_set_uint8(v___x_2955_, sizeof(void*)*3 + 4, v_isRecordingDeps_2950_);
v___x_2956_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_2911_, v___f_2931_, v___x_2932_, v_a_2904_, v_a_2905_, v___x_2955_, v___y_2951_);
lean_dec_ref_known(v___x_2955_, 3);
return v___x_2956_;
}
v___jp_2957_:
{
lean_object* v___x_2961_; lean_object* v_env_2962_; lean_object* v_nextMacroScope_2963_; lean_object* v_ngen_2964_; lean_object* v_auxDeclNGen_2965_; lean_object* v_traceState_2966_; lean_object* v_recordedDeps_2967_; lean_object* v_messages_2968_; lean_object* v_infoState_2969_; lean_object* v_snapshotTasks_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2980_; 
v___x_2961_ = lean_st_ref_take(v_a_2907_);
v_env_2962_ = lean_ctor_get(v___x_2961_, 0);
v_nextMacroScope_2963_ = lean_ctor_get(v___x_2961_, 1);
v_ngen_2964_ = lean_ctor_get(v___x_2961_, 2);
v_auxDeclNGen_2965_ = lean_ctor_get(v___x_2961_, 3);
v_traceState_2966_ = lean_ctor_get(v___x_2961_, 4);
v_recordedDeps_2967_ = lean_ctor_get(v___x_2961_, 6);
v_messages_2968_ = lean_ctor_get(v___x_2961_, 7);
v_infoState_2969_ = lean_ctor_get(v___x_2961_, 8);
v_snapshotTasks_2970_ = lean_ctor_get(v___x_2961_, 9);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2980_ == 0)
{
lean_object* v_unused_2981_; 
v_unused_2981_ = lean_ctor_get(v___x_2961_, 5);
lean_dec(v_unused_2981_);
v___x_2972_ = v___x_2961_;
v_isShared_2973_ = v_isSharedCheck_2980_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_snapshotTasks_2970_);
lean_inc(v_infoState_2969_);
lean_inc(v_messages_2968_);
lean_inc(v_recordedDeps_2967_);
lean_inc(v_traceState_2966_);
lean_inc(v_auxDeclNGen_2965_);
lean_inc(v_ngen_2964_);
lean_inc(v_nextMacroScope_2963_);
lean_inc(v_env_2962_);
lean_dec(v___x_2961_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2980_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2974_ = l_Lean_Kernel_enableDiag(v_env_2962_, v___y_2960_);
v___x_2975_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 5, v___x_2975_);
lean_ctor_set(v___x_2972_, 0, v___x_2974_);
v___x_2977_ = v___x_2972_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_nextMacroScope_2963_);
lean_ctor_set(v_reuseFailAlloc_2979_, 2, v_ngen_2964_);
lean_ctor_set(v_reuseFailAlloc_2979_, 3, v_auxDeclNGen_2965_);
lean_ctor_set(v_reuseFailAlloc_2979_, 4, v_traceState_2966_);
lean_ctor_set(v_reuseFailAlloc_2979_, 5, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_2979_, 6, v_recordedDeps_2967_);
lean_ctor_set(v_reuseFailAlloc_2979_, 7, v_messages_2968_);
lean_ctor_set(v_reuseFailAlloc_2979_, 8, v_infoState_2969_);
lean_ctor_set(v_reuseFailAlloc_2979_, 9, v_snapshotTasks_2970_);
v___x_2977_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_st_ref_put(v_a_2907_, v___x_2977_);
lean_inc_ref(v_inheritedTraceOptions_2930_);
lean_inc(v_cancelTk_x3f_2929_);
lean_inc(v_currMacroScope_2928_);
lean_inc(v_quotContext_2927_);
lean_inc(v_maxHeartbeats_2926_);
lean_inc(v_initHeartbeats_2925_);
lean_inc(v_openDecls_2924_);
lean_inc(v_currNamespace_2923_);
lean_inc_ref(v_fileMap_2921_);
lean_inc_ref(v_fileName_2920_);
v___y_2934_ = v___y_2958_;
v___y_2935_ = v___y_2959_;
v_fileName_2936_ = v_fileName_2920_;
v_fileMap_2937_ = v_fileMap_2921_;
v_currNamespace_2938_ = v_currNamespace_2923_;
v_openDecls_2939_ = v_openDecls_2924_;
v_initHeartbeats_2940_ = v_initHeartbeats_2925_;
v_maxHeartbeats_2941_ = v_maxHeartbeats_2926_;
v_quotContext_2942_ = v_quotContext_2927_;
v_currMacroScope_2943_ = v_currMacroScope_2928_;
v_cancelTk_x3f_2944_ = v_cancelTk_x3f_2929_;
v_inheritedTraceOptions_2945_ = v_inheritedTraceOptions_2930_;
v_currRecDepth_2946_ = v_currRecDepth_2915_;
v_ref_2947_ = v_ref_2916_;
v_suppressElabErrors_2948_ = v_suppressElabErrors_2917_;
v_checkDeprecated_2949_ = v_checkDeprecated_2918_;
v_isRecordingDeps_2950_ = v_isRecordingDeps_2919_;
v___y_2951_ = v_a_2907_;
goto v___jp_2933_;
}
}
}
v___jp_2982_:
{
uint16_t v___x_2984_; lean_object* v___x_2985_; lean_object* v_env_2986_; uint8_t v___x_2987_; uint16_t v___x_2988_; uint16_t v___x_2989_; uint16_t v___x_2990_; uint8_t v___x_2991_; 
v___x_2984_ = l_Lean_OptionFlags_ofOptions(v___y_2983_);
v___x_2985_ = lean_st_ref_get(v_a_2907_);
v_env_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc_ref(v_env_2986_);
lean_dec(v___x_2985_);
v___x_2987_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2986_);
lean_dec_ref(v_env_2986_);
v___x_2988_ = 512;
v___x_2989_ = lean_uint16_land(v___x_2984_, v___x_2988_);
v___x_2990_ = 0;
v___x_2991_ = lean_uint16_dec_eq(v___x_2989_, v___x_2990_);
if (v___x_2991_ == 0)
{
if (v___x_2987_ == 0)
{
uint8_t v___x_2992_; 
v___x_2992_ = 1;
v___y_2958_ = v___y_2983_;
v___y_2959_ = v___x_2984_;
v___y_2960_ = v___x_2992_;
goto v___jp_2957_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2930_);
lean_inc(v_cancelTk_x3f_2929_);
lean_inc(v_currMacroScope_2928_);
lean_inc(v_quotContext_2927_);
lean_inc(v_maxHeartbeats_2926_);
lean_inc(v_initHeartbeats_2925_);
lean_inc(v_openDecls_2924_);
lean_inc(v_currNamespace_2923_);
lean_inc_ref(v_fileMap_2921_);
lean_inc_ref(v_fileName_2920_);
v___y_2934_ = v___y_2983_;
v___y_2935_ = v___x_2984_;
v_fileName_2936_ = v_fileName_2920_;
v_fileMap_2937_ = v_fileMap_2921_;
v_currNamespace_2938_ = v_currNamespace_2923_;
v_openDecls_2939_ = v_openDecls_2924_;
v_initHeartbeats_2940_ = v_initHeartbeats_2925_;
v_maxHeartbeats_2941_ = v_maxHeartbeats_2926_;
v_quotContext_2942_ = v_quotContext_2927_;
v_currMacroScope_2943_ = v_currMacroScope_2928_;
v_cancelTk_x3f_2944_ = v_cancelTk_x3f_2929_;
v_inheritedTraceOptions_2945_ = v_inheritedTraceOptions_2930_;
v_currRecDepth_2946_ = v_currRecDepth_2915_;
v_ref_2947_ = v_ref_2916_;
v_suppressElabErrors_2948_ = v_suppressElabErrors_2917_;
v_checkDeprecated_2949_ = v_checkDeprecated_2918_;
v_isRecordingDeps_2950_ = v_isRecordingDeps_2919_;
v___y_2951_ = v_a_2907_;
goto v___jp_2933_;
}
}
else
{
if (v___x_2987_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2930_);
lean_inc(v_cancelTk_x3f_2929_);
lean_inc(v_currMacroScope_2928_);
lean_inc(v_quotContext_2927_);
lean_inc(v_maxHeartbeats_2926_);
lean_inc(v_initHeartbeats_2925_);
lean_inc(v_openDecls_2924_);
lean_inc(v_currNamespace_2923_);
lean_inc_ref(v_fileMap_2921_);
lean_inc_ref(v_fileName_2920_);
v___y_2934_ = v___y_2983_;
v___y_2935_ = v___x_2984_;
v_fileName_2936_ = v_fileName_2920_;
v_fileMap_2937_ = v_fileMap_2921_;
v_currNamespace_2938_ = v_currNamespace_2923_;
v_openDecls_2939_ = v_openDecls_2924_;
v_initHeartbeats_2940_ = v_initHeartbeats_2925_;
v_maxHeartbeats_2941_ = v_maxHeartbeats_2926_;
v_quotContext_2942_ = v_quotContext_2927_;
v_currMacroScope_2943_ = v_currMacroScope_2928_;
v_cancelTk_x3f_2944_ = v_cancelTk_x3f_2929_;
v_inheritedTraceOptions_2945_ = v_inheritedTraceOptions_2930_;
v_currRecDepth_2946_ = v_currRecDepth_2915_;
v_ref_2947_ = v_ref_2916_;
v_suppressElabErrors_2948_ = v_suppressElabErrors_2917_;
v_checkDeprecated_2949_ = v_checkDeprecated_2918_;
v_isRecordingDeps_2950_ = v_isRecordingDeps_2919_;
v___y_2951_ = v_a_2907_;
goto v___jp_2933_;
}
else
{
v___y_2958_ = v___y_2983_;
v___y_2959_ = v___x_2984_;
v___y_2960_ = v___x_2932_;
goto v___jp_2957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_2996_, lean_object* v_info_2997_, lean_object* v_name_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_2996_, v_info_2997_, v_name_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* v_declName_3005_, lean_object* v_info_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v___x_3012_; lean_object* v_env_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3012_ = lean_st_ref_get(v_a_3010_);
v_env_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc_ref(v_env_3013_);
lean_dec(v___x_3012_);
v___x_3014_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc_n(v_declName_3005_, 2);
v___x_3015_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3013_, v_declName_3005_, v___x_3014_);
lean_inc_n(v___x_3015_, 2);
v___x_3016_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3016_, 0, v_declName_3005_);
lean_closure_set(v___x_3016_, 1, v_info_3006_);
lean_closure_set(v___x_3016_, 2, v___x_3015_);
v___x_3017_ = l_Lean_Meta_realizeConst(v_declName_3005_, v___x_3015_, v___x_3016_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3024_ == 0)
{
lean_object* v_unused_3025_; 
v_unused_3025_ = lean_ctor_get(v___x_3017_, 0);
lean_dec(v_unused_3025_);
v___x_3019_ = v___x_3017_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_dec(v___x_3017_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v___x_3015_);
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3015_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec(v___x_3015_);
v_a_3026_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3017_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3017_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object* v_declName_3034_, lean_object* v_info_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_3034_, v_info_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* v_declName_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v___x_3048_; lean_object* v_env_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v_env_3053_; uint8_t v___x_3054_; uint8_t v___x_3055_; 
v___x_3048_ = lean_st_ref_get(v_a_3046_);
v_env_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc_ref(v_env_3049_);
lean_dec(v___x_3048_);
v___x_3050_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3042_);
v___x_3051_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3049_, v_declName_3042_, v___x_3050_);
v___x_3052_ = lean_st_ref_get(v_a_3046_);
v_env_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc_ref_n(v_env_3053_, 2);
lean_dec(v___x_3052_);
v___x_3054_ = 1;
lean_inc(v___x_3051_);
v___x_3055_ = l_Lean_Environment_contains(v_env_3053_, v___x_3051_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; lean_object* v_toEnvExtension_3057_; lean_object* v_asyncMode_3058_; uint8_t v___x_3059_; lean_object* v___x_3060_; 
lean_dec(v___x_3051_);
v___x_3056_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
v_toEnvExtension_3057_ = lean_ctor_get(v___x_3056_, 0);
v_asyncMode_3058_ = lean_ctor_get(v_toEnvExtension_3057_, 2);
v___x_3059_ = 0;
lean_inc(v_declName_3042_);
v___x_3060_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3056_, v_env_3053_, v_declName_3042_, v_asyncMode_3058_, v___x_3059_);
if (lean_obj_tag(v___x_3060_) == 1)
{
lean_object* v_val_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3085_; 
v_val_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3085_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_val_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3085_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_3042_, v_val_3061_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3076_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3068_ = v___x_3065_;
v_isShared_3069_ = v_isSharedCheck_3076_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3076_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 0, v_a_3066_);
v___x_3071_ = v___x_3063_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3073_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3071_);
v___x_3073_ = v___x_3068_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_del_object(v___x_3063_);
v_a_3077_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3065_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3065_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_dec(v___x_3060_);
lean_dec(v_declName_3042_);
v___x_3086_ = lean_box(0);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_dec_ref(v_env_3053_);
lean_dec(v_declName_3042_);
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3051_);
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
return v___x_3089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object* v_declName_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_));
v___x_3100_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object* v_a_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
return v_res_3102_;
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
