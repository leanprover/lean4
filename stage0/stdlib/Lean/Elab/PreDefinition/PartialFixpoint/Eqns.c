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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "mkFixEq: unexpected body of `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(18, 104, 23, 57, 110, 104, 99, 16)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lfp_monotone"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(226, 115, 213, 20, 156, 86, 56, 31)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lfp_monotone_fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(178, 113, 187, 250, 69, 106, 19, 81)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fix_eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
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
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateProj!Impl"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13_value;
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
lean_object* v___x_157_; lean_object* v_env_158_; lean_object* v_toConstantVal_159_; lean_object* v_value_160_; lean_object* v_all_161_; uint8_t v___y_163_; lean_object* v_type_171_; uint8_t v___x_172_; 
v___x_157_ = lean_st_ref_get(v___y_155_);
v_env_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc_ref_n(v_env_158_, 2);
lean_dec(v___x_157_);
v_toConstantVal_159_ = lean_ctor_get(v_thm_154_, 0);
v_value_160_ = lean_ctor_get(v_thm_154_, 1);
v_all_161_ = lean_ctor_get(v_thm_154_, 2);
v_type_171_ = lean_ctor_get(v_toConstantVal_159_, 2);
v___x_172_ = l_Lean_Environment_hasUnsafe(v_env_158_, v_type_171_);
if (v___x_172_ == 0)
{
uint8_t v___x_173_; 
v___x_173_ = l_Lean_Environment_hasUnsafe(v_env_158_, v_value_160_);
v___y_163_ = v___x_173_;
goto v___jp_162_;
}
else
{
lean_dec_ref(v_env_158_);
v___y_163_ = v___x_172_;
goto v___jp_162_;
}
v___jp_162_:
{
if (v___y_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_164_, 0, v_thm_154_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
lean_inc(v_all_161_);
lean_inc_ref(v_value_160_);
lean_inc_ref(v_toConstantVal_159_);
lean_dec_ref(v_thm_154_);
v___x_166_ = lean_box(0);
v___x_167_ = 0;
v___x_168_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_168_, 0, v_toConstantVal_159_);
lean_ctor_set(v___x_168_, 1, v_value_160_);
lean_ctor_set(v___x_168_, 2, v___x_166_);
lean_ctor_set(v___x_168_, 3, v_all_161_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*4, v___x_167_);
v___x_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg___boxed(lean_object* v_thm_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v_thm_174_, v___y_175_);
lean_dec(v___y_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4(lean_object* v_thm_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v_thm_178_, v___y_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___boxed(lean_object* v_thm_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4(v_thm_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(lean_object* v___y_192_, uint8_t v_isExporting_193_, lean_object* v___x_194_, lean_object* v___y_195_, lean_object* v___x_196_, lean_object* v_a_x3f_197_){
_start:
{
lean_object* v___x_199_; lean_object* v_env_200_; lean_object* v_nextMacroScope_201_; lean_object* v_ngen_202_; lean_object* v_auxDeclNGen_203_; lean_object* v_traceState_204_; lean_object* v_recordedDeps_205_; lean_object* v_messages_206_; lean_object* v_infoState_207_; lean_object* v_snapshotTasks_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_233_; 
v___x_199_ = lean_st_ref_take(v___y_192_);
v_env_200_ = lean_ctor_get(v___x_199_, 0);
v_nextMacroScope_201_ = lean_ctor_get(v___x_199_, 1);
v_ngen_202_ = lean_ctor_get(v___x_199_, 2);
v_auxDeclNGen_203_ = lean_ctor_get(v___x_199_, 3);
v_traceState_204_ = lean_ctor_get(v___x_199_, 4);
v_recordedDeps_205_ = lean_ctor_get(v___x_199_, 6);
v_messages_206_ = lean_ctor_get(v___x_199_, 7);
v_infoState_207_ = lean_ctor_get(v___x_199_, 8);
v_snapshotTasks_208_ = lean_ctor_get(v___x_199_, 9);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; 
v_unused_234_ = lean_ctor_get(v___x_199_, 5);
lean_dec(v_unused_234_);
v___x_210_ = v___x_199_;
v_isShared_211_ = v_isSharedCheck_233_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_snapshotTasks_208_);
lean_inc(v_infoState_207_);
lean_inc(v_messages_206_);
lean_inc(v_recordedDeps_205_);
lean_inc(v_traceState_204_);
lean_inc(v_auxDeclNGen_203_);
lean_inc(v_ngen_202_);
lean_inc(v_nextMacroScope_201_);
lean_inc(v_env_200_);
lean_dec(v___x_199_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_233_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = l_Lean_Environment_setExporting(v_env_200_, v_isExporting_193_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 5, v___x_194_);
lean_ctor_set(v___x_210_, 0, v___x_212_);
v___x_214_ = v___x_210_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_nextMacroScope_201_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_ngen_202_);
lean_ctor_set(v_reuseFailAlloc_232_, 3, v_auxDeclNGen_203_);
lean_ctor_set(v_reuseFailAlloc_232_, 4, v_traceState_204_);
lean_ctor_set(v_reuseFailAlloc_232_, 5, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_232_, 6, v_recordedDeps_205_);
lean_ctor_set(v_reuseFailAlloc_232_, 7, v_messages_206_);
lean_ctor_set(v_reuseFailAlloc_232_, 8, v_infoState_207_);
lean_ctor_set(v_reuseFailAlloc_232_, 9, v_snapshotTasks_208_);
v___x_214_ = v_reuseFailAlloc_232_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_mctx_217_; lean_object* v_zetaDeltaFVarIds_218_; lean_object* v_postponed_219_; lean_object* v_diag_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_230_; 
v___x_215_ = lean_st_ref_put(v___y_192_, v___x_214_);
v___x_216_ = lean_st_ref_take(v___y_195_);
v_mctx_217_ = lean_ctor_get(v___x_216_, 0);
v_zetaDeltaFVarIds_218_ = lean_ctor_get(v___x_216_, 2);
v_postponed_219_ = lean_ctor_get(v___x_216_, 3);
v_diag_220_ = lean_ctor_get(v___x_216_, 4);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; 
v_unused_231_ = lean_ctor_get(v___x_216_, 1);
lean_dec(v_unused_231_);
v___x_222_ = v___x_216_;
v_isShared_223_ = v_isSharedCheck_230_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_diag_220_);
lean_inc(v_postponed_219_);
lean_inc(v_zetaDeltaFVarIds_218_);
lean_inc(v_mctx_217_);
lean_dec(v___x_216_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_230_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_box(0);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___x_196_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_mctx_217_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_zetaDeltaFVarIds_218_);
lean_ctor_set(v_reuseFailAlloc_229_, 3, v_postponed_219_);
lean_ctor_set(v_reuseFailAlloc_229_, 4, v_diag_220_);
v___x_226_ = v_reuseFailAlloc_229_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_st_ref_put(v___y_195_, v___x_226_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_224_);
return v___x_228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0___boxed(lean_object* v___y_235_, lean_object* v_isExporting_236_, lean_object* v___x_237_, lean_object* v___y_238_, lean_object* v___x_239_, lean_object* v_a_x3f_240_, lean_object* v___y_241_){
_start:
{
uint8_t v_isExporting_boxed_242_; lean_object* v_res_243_; 
v_isExporting_boxed_242_ = lean_unbox(v_isExporting_236_);
v_res_243_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(v___y_235_, v_isExporting_boxed_242_, v___x_237_, v___y_238_, v___x_239_, v_a_x3f_240_);
lean_dec(v_a_x3f_240_);
lean_dec(v___y_238_);
lean_dec(v___y_235_);
return v_res_243_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_244_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1);
v___x_250_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
lean_ctor_set(v___x_250_, 2, v___x_249_);
lean_ctor_set(v___x_250_, 3, v___x_249_);
lean_ctor_set(v___x_250_, 4, v___x_249_);
lean_ctor_set(v___x_250_, 5, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(lean_object* v_x_251_, uint8_t v_isExporting_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; lean_object* v_env_259_; lean_object* v___x_260_; uint8_t v_isModule_261_; 
v___x_258_ = lean_st_ref_get(v___y_256_);
v_env_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_env_259_);
lean_dec(v___x_258_);
v___x_260_ = l_Lean_Environment_header(v_env_259_);
v_isModule_261_ = lean_ctor_get_uint8(v___x_260_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_260_);
if (v_isModule_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec_ref(v_env_259_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
lean_inc(v___y_254_);
lean_inc_ref(v___y_253_);
v___x_262_ = lean_apply_5(v_x_251_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, lean_box(0));
return v___x_262_;
}
else
{
uint8_t v_isExporting_263_; 
v_isExporting_263_ = lean_ctor_get_uint8(v_env_259_, sizeof(void*)*13);
lean_dec_ref(v_env_259_);
if (v_isExporting_252_ == 0)
{
if (v_isExporting_263_ == 0)
{
lean_object* v___x_330_; 
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
lean_inc(v___y_254_);
lean_inc_ref(v___y_253_);
v___x_330_ = lean_apply_5(v_x_251_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, lean_box(0));
return v___x_330_;
}
else
{
goto v___jp_264_;
}
}
else
{
if (v_isExporting_263_ == 0)
{
goto v___jp_264_;
}
else
{
lean_object* v___x_331_; 
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
lean_inc(v___y_254_);
lean_inc_ref(v___y_253_);
v___x_331_ = lean_apply_5(v_x_251_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, lean_box(0));
return v___x_331_;
}
}
v___jp_264_:
{
lean_object* v___x_265_; lean_object* v_env_266_; lean_object* v_nextMacroScope_267_; lean_object* v_ngen_268_; lean_object* v_auxDeclNGen_269_; lean_object* v_traceState_270_; lean_object* v_recordedDeps_271_; lean_object* v_messages_272_; lean_object* v_infoState_273_; lean_object* v_snapshotTasks_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_328_; 
v___x_265_ = lean_st_ref_take(v___y_256_);
v_env_266_ = lean_ctor_get(v___x_265_, 0);
v_nextMacroScope_267_ = lean_ctor_get(v___x_265_, 1);
v_ngen_268_ = lean_ctor_get(v___x_265_, 2);
v_auxDeclNGen_269_ = lean_ctor_get(v___x_265_, 3);
v_traceState_270_ = lean_ctor_get(v___x_265_, 4);
v_recordedDeps_271_ = lean_ctor_get(v___x_265_, 6);
v_messages_272_ = lean_ctor_get(v___x_265_, 7);
v_infoState_273_ = lean_ctor_get(v___x_265_, 8);
v_snapshotTasks_274_ = lean_ctor_get(v___x_265_, 9);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v___x_265_, 5);
lean_dec(v_unused_329_);
v___x_276_ = v___x_265_;
v_isShared_277_ = v_isSharedCheck_328_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_snapshotTasks_274_);
lean_inc(v_infoState_273_);
lean_inc(v_messages_272_);
lean_inc(v_recordedDeps_271_);
lean_inc(v_traceState_270_);
lean_inc(v_auxDeclNGen_269_);
lean_inc(v_ngen_268_);
lean_inc(v_nextMacroScope_267_);
lean_inc(v_env_266_);
lean_dec(v___x_265_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_328_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_278_ = l_Lean_Environment_setExporting(v_env_266_, v_isExporting_252_);
v___x_279_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 5, v___x_279_);
lean_ctor_set(v___x_276_, 0, v___x_278_);
v___x_281_ = v___x_276_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_nextMacroScope_267_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_ngen_268_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_auxDeclNGen_269_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_traceState_270_);
lean_ctor_set(v_reuseFailAlloc_327_, 5, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_327_, 6, v_recordedDeps_271_);
lean_ctor_set(v_reuseFailAlloc_327_, 7, v_messages_272_);
lean_ctor_set(v_reuseFailAlloc_327_, 8, v_infoState_273_);
lean_ctor_set(v_reuseFailAlloc_327_, 9, v_snapshotTasks_274_);
v___x_281_ = v_reuseFailAlloc_327_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_mctx_284_; lean_object* v_zetaDeltaFVarIds_285_; lean_object* v_postponed_286_; lean_object* v_diag_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_325_; 
v___x_282_ = lean_st_ref_put(v___y_256_, v___x_281_);
v___x_283_ = lean_st_ref_take(v___y_254_);
v_mctx_284_ = lean_ctor_get(v___x_283_, 0);
v_zetaDeltaFVarIds_285_ = lean_ctor_get(v___x_283_, 2);
v_postponed_286_ = lean_ctor_get(v___x_283_, 3);
v_diag_287_ = lean_ctor_get(v___x_283_, 4);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; 
v_unused_326_ = lean_ctor_get(v___x_283_, 1);
lean_dec(v_unused_326_);
v___x_289_ = v___x_283_;
v_isShared_290_ = v_isSharedCheck_325_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_diag_287_);
lean_inc(v_postponed_286_);
lean_inc(v_zetaDeltaFVarIds_285_);
lean_inc(v_mctx_284_);
lean_dec(v___x_283_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_325_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v___x_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_mctx_284_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_zetaDeltaFVarIds_285_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v_postponed_286_);
lean_ctor_set(v_reuseFailAlloc_324_, 4, v_diag_287_);
v___x_293_ = v_reuseFailAlloc_324_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; lean_object* v_r_295_; 
v___x_294_ = lean_st_ref_put(v___y_254_, v___x_293_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
lean_inc(v___y_254_);
lean_inc_ref(v___y_253_);
v_r_295_ = lean_apply_5(v_x_251_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, lean_box(0));
if (lean_obj_tag(v_r_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_312_; 
v_a_296_ = lean_ctor_get(v_r_295_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v_r_295_);
if (v_isSharedCheck_312_ == 0)
{
v___x_298_ = v_r_295_;
v_isShared_299_ = v_isSharedCheck_312_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v_r_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_312_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
lean_inc(v_a_296_);
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 1);
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_311_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v___x_302_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(v___y_256_, v_isExporting_263_, v___x_279_, v___y_254_, v___x_291_, v___x_301_);
lean_dec_ref(v___x_301_);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; 
v_unused_310_ = lean_ctor_get(v___x_302_, 0);
lean_dec(v_unused_310_);
v___x_304_ = v___x_302_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_dec(v___x_302_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v_a_296_);
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_296_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
v_a_313_ = lean_ctor_get(v_r_295_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v_r_295_, 1);
v___x_314_ = lean_box(0);
v___x_315_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(v___y_256_, v_isExporting_263_, v___x_279_, v___y_254_, v___x_291_, v___x_314_);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; 
v_unused_323_ = lean_ctor_get(v___x_315_, 0);
lean_dec(v_unused_323_);
v___x_317_ = v___x_315_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_dec(v___x_315_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 1);
lean_ctor_set(v___x_317_, 0, v_a_313_);
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_313_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___boxed(lean_object* v_x_332_, lean_object* v_isExporting_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
uint8_t v_isExporting_boxed_339_; lean_object* v_res_340_; 
v_isExporting_boxed_339_ = lean_unbox(v_isExporting_333_);
v_res_340_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v_x_332_, v_isExporting_boxed_339_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5(lean_object* v_00_u03b1_341_, lean_object* v_x_342_, uint8_t v_isExporting_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v_x_342_, v_isExporting_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___boxed(lean_object* v_00_u03b1_350_, lean_object* v_x_351_, lean_object* v_isExporting_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
uint8_t v_isExporting_boxed_358_; lean_object* v_res_359_; 
v_isExporting_boxed_358_ = lean_unbox(v_isExporting_352_);
v_res_359_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5(v_00_u03b1_350_, v_x_351_, v_isExporting_boxed_358_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(lean_object* v_msgData_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v___x_366_; lean_object* v_env_367_; uint8_t v___x_368_; lean_object* v_env_369_; lean_object* v___x_370_; lean_object* v_toCold_371_; lean_object* v_mctx_372_; lean_object* v_lctx_373_; lean_object* v_options_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_366_ = lean_st_ref_get(v___y_364_);
v_env_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc_ref(v_env_367_);
lean_dec(v___x_366_);
v___x_368_ = 0;
v_env_369_ = l_Lean_Environment_setRecordingDeps(v_env_367_, v___x_368_);
v___x_370_ = lean_st_ref_get(v___y_362_);
v_toCold_371_ = lean_ctor_get(v___y_363_, 0);
v_mctx_372_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_mctx_372_);
lean_dec(v___x_370_);
v_lctx_373_ = lean_ctor_get(v___y_361_, 2);
v_options_374_ = lean_ctor_get(v_toCold_371_, 2);
lean_inc_ref(v_options_374_);
lean_inc_ref(v_lctx_373_);
v___x_375_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_375_, 0, v_env_369_);
lean_ctor_set(v___x_375_, 1, v_mctx_372_);
lean_ctor_set(v___x_375_, 2, v_lctx_373_);
lean_ctor_set(v___x_375_, 3, v_options_374_);
v___x_376_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v_msgData_360_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0___boxed(lean_object* v_msgData_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msgData_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(lean_object* v_msg_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_ref_391_; lean_object* v___x_392_; lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_ref_391_ = lean_ctor_get(v___y_388_, 2);
v___x_392_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msg_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
lean_inc(v_ref_391_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_ref_391_);
lean_ctor_set(v___x_397_, 1, v_a_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 1);
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg___boxed(lean_object* v_msg_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v_msg_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_408_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2));
v___x_414_ = l_Lean_stringToMessageData(v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0(lean_object* v_declNameNonRec_426_, lean_object* v_xs_427_, lean_object* v_body_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
uint8_t v___y_479_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_496_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6));
v___x_497_ = lean_unsigned_to_nat(4u);
v___x_498_ = l_Lean_Expr_isAppOfArity(v_body_428_, v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8));
v___x_500_ = l_Lean_Expr_isAppOfArity(v_body_428_, v___x_499_, v___x_497_);
v___y_479_ = v___x_500_;
goto v___jp_478_;
}
else
{
v___y_479_ = v___x_498_;
goto v___jp_478_;
}
v___jp_434_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = l_Lean_Expr_appFn_x21(v_body_428_);
lean_dec_ref(v_body_428_);
v___x_436_ = l_Lean_Expr_appArg_x21(v___x_435_);
lean_dec_ref(v___x_435_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc_ref(v___x_436_);
v___x_437_ = lean_infer_type(v___x_436_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; uint8_t v___x_439_; uint8_t v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = 0;
v___x_440_ = 1;
v___x_441_ = 1;
v___x_442_ = l_Lean_Meta_mkForallFVars(v_xs_427_, v_a_438_, v___x_439_, v___x_440_, v___x_440_, v___x_441_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
v___x_444_ = l_Lean_Meta_mkLambdaFVars(v_xs_427_, v___x_436_, v___x_439_, v___x_440_, v___x_439_, v___x_440_, v___x_441_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_453_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_a_443_);
lean_ctor_set(v___x_449_, 1, v_a_445_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec(v_a_443_);
v_a_454_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_444_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_444_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec_ref(v___x_436_);
v_a_462_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_442_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_442_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec_ref(v___x_436_);
v_a_470_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_437_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_437_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
v___jp_478_:
{
if (v___y_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
v___x_480_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1);
v___x_481_ = l_Lean_MessageData_ofConstName(v_declNameNonRec_426_, v___y_479_);
v___x_482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3);
v___x_484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = l_Lean_indentExpr(v_body_428_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_486_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
lean_dec(v_declNameNonRec_426_);
goto v___jp_434_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___boxed(lean_object* v_declNameNonRec_501_, lean_object* v_xs_502_, lean_object* v_body_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0(v_declNameNonRec_501_, v_xs_502_, v_body_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_xs_502_);
return v_res_509_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0(void){
_start:
{
lean_object* v___x_510_; lean_object* v_dummy_511_; 
v___x_510_ = lean_box(0);
v_dummy_511_ = l_Lean_Expr_sort___override(v___x_510_);
return v_dummy_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1(lean_object* v_declNameNonRec_522_, lean_object* v___x_523_, lean_object* v___x_524_, uint8_t v___x_525_, lean_object* v_xs_526_, lean_object* v_body_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; uint8_t v___x_540_; lean_object* v___y_542_; 
lean_inc(v___x_523_);
v___x_533_ = l_Lean_mkConst(v_declNameNonRec_522_, v___x_523_);
v___x_534_ = l_Lean_mkAppN(v___x_533_, v_xs_526_);
v___x_535_ = l_Lean_mkConst(v___x_524_, v___x_523_);
v___x_536_ = l_Lean_mkAppN(v___x_535_, v_xs_526_);
lean_inc_ref(v___x_534_);
v___x_537_ = l_Lean_Expr_app___override(v___x_536_, v___x_534_);
v___x_538_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6));
v___x_539_ = l_Lean_Expr_isAppOf(v_body_527_, v___x_538_);
v___x_540_ = 1;
if (v___x_539_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2));
v___y_542_ = v___x_592_;
goto v___jp_541_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4));
v___y_542_ = v___x_593_;
goto v___jp_541_;
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_dummy_546_; lean_object* v_nargs_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_543_ = l_Lean_Expr_getAppFn(v_body_527_);
v___x_544_ = l_Lean_Expr_constLevels_x21(v___x_543_);
lean_dec_ref(v___x_543_);
lean_inc(v___y_542_);
v___x_545_ = l_Lean_mkConst(v___y_542_, v___x_544_);
v_dummy_546_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_547_ = l_Lean_Expr_getAppNumArgs(v_body_527_);
lean_inc(v_nargs_547_);
v___x_548_ = lean_mk_array(v_nargs_547_, v_dummy_546_);
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_sub(v_nargs_547_, v___x_549_);
lean_dec(v_nargs_547_);
v___x_551_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_body_527_, v___x_548_, v___x_550_);
v___x_552_ = l_Lean_mkAppN(v___x_545_, v___x_551_);
lean_dec_ref(v___x_551_);
v___x_553_ = l_Lean_Meta_mkEq(v___x_534_, v___x_537_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; uint8_t v___x_555_; lean_object* v___x_556_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = 1;
v___x_556_ = l_Lean_Meta_mkForallFVars(v_xs_526_, v_a_554_, v___x_525_, v___x_540_, v___x_540_, v___x_555_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = l_Lean_Meta_mkLambdaFVars(v_xs_526_, v___x_552_, v___x_525_, v___x_540_, v___x_525_, v___x_540_, v___x_555_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
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
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_a_557_);
lean_ctor_set(v___x_563_, 1, v_a_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec(v_a_557_);
v_a_568_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_558_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_558_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v___x_552_);
v_a_576_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_556_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_556_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec_ref(v___x_552_);
v_a_584_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_553_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_553_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___boxed(lean_object* v_declNameNonRec_594_, lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v_xs_598_, lean_object* v_body_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
uint8_t v___x_10048__boxed_605_; lean_object* v_res_606_; 
v___x_10048__boxed_605_ = lean_unbox(v___x_597_);
v_res_606_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1(v_declNameNonRec_594_, v___x_595_, v___x_596_, v___x_10048__boxed_605_, v_xs_598_, v_body_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec_ref(v_xs_598_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
if (lean_obj_tag(v_a_607_) == 0)
{
lean_object* v___x_609_; 
v___x_609_ = l_List_reverse___redArg(v_a_608_);
return v___x_609_;
}
else
{
lean_object* v_head_610_; lean_object* v_tail_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_620_; 
v_head_610_ = lean_ctor_get(v_a_607_, 0);
v_tail_611_ = lean_ctor_get(v_a_607_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_a_607_);
if (v_isSharedCheck_620_ == 0)
{
v___x_613_ = v_a_607_;
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_tail_611_);
lean_inc(v_head_610_);
lean_dec(v_a_607_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = l_Lean_mkLevelParam(v_head_610_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v_a_608_);
lean_ctor_set(v___x_613_, 0, v___x_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_a_608_);
v___x_617_ = v_reuseFailAlloc_619_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
v_a_607_ = v_tail_611_;
v_a_608_ = v___x_617_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_instMonadEIO___redArg();
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(lean_object* v_msg_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_toApplicative_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_695_; 
v___x_632_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0, &l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0);
v___x_633_ = l_StateRefT_x27_instMonad___redArg(v___x_632_);
v_toApplicative_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v___x_633_, 1);
lean_dec(v_unused_696_);
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_695_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_toApplicative_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_695_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_toFunctor_638_; lean_object* v_toSeq_639_; lean_object* v_toSeqLeft_640_; lean_object* v_toSeqRight_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_693_; 
v_toFunctor_638_ = lean_ctor_get(v_toApplicative_634_, 0);
v_toSeq_639_ = lean_ctor_get(v_toApplicative_634_, 2);
v_toSeqLeft_640_ = lean_ctor_get(v_toApplicative_634_, 3);
v_toSeqRight_641_ = lean_ctor_get(v_toApplicative_634_, 4);
v_isSharedCheck_693_ = !lean_is_exclusive(v_toApplicative_634_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v_toApplicative_634_, 1);
lean_dec(v_unused_694_);
v___x_643_ = v_toApplicative_634_;
v_isShared_644_ = v_isSharedCheck_693_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_toSeqRight_641_);
lean_inc(v_toSeqLeft_640_);
lean_inc(v_toSeq_639_);
lean_inc(v_toFunctor_638_);
lean_dec(v_toApplicative_634_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_693_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___f_645_; lean_object* v___f_646_; lean_object* v___f_647_; lean_object* v___f_648_; lean_object* v___x_649_; lean_object* v___f_650_; lean_object* v___f_651_; lean_object* v___f_652_; lean_object* v___x_654_; 
v___f_645_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__1));
v___f_646_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__2));
lean_inc_ref(v_toFunctor_638_);
v___f_647_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_647_, 0, v_toFunctor_638_);
v___f_648_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_648_, 0, v_toFunctor_638_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___f_647_);
lean_ctor_set(v___x_649_, 1, v___f_648_);
v___f_650_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_650_, 0, v_toSeqRight_641_);
v___f_651_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_651_, 0, v_toSeqLeft_640_);
v___f_652_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_652_, 0, v_toSeq_639_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 4, v___f_650_);
lean_ctor_set(v___x_643_, 3, v___f_651_);
lean_ctor_set(v___x_643_, 2, v___f_652_);
lean_ctor_set(v___x_643_, 1, v___f_645_);
lean_ctor_set(v___x_643_, 0, v___x_649_);
v___x_654_ = v___x_643_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___f_645_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v___f_652_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v___f_651_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v___f_650_);
v___x_654_ = v_reuseFailAlloc_692_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_656_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___f_646_);
lean_ctor_set(v___x_636_, 0, v___x_654_);
v___x_656_ = v___x_636_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___f_646_);
v___x_656_ = v_reuseFailAlloc_691_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; lean_object* v_toApplicative_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_689_; 
v___x_657_ = l_StateRefT_x27_instMonad___redArg(v___x_656_);
v_toApplicative_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v___x_657_, 1);
lean_dec(v_unused_690_);
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_689_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_toApplicative_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_689_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_toFunctor_662_; lean_object* v_toSeq_663_; lean_object* v_toSeqLeft_664_; lean_object* v_toSeqRight_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_687_; 
v_toFunctor_662_ = lean_ctor_get(v_toApplicative_658_, 0);
v_toSeq_663_ = lean_ctor_get(v_toApplicative_658_, 2);
v_toSeqLeft_664_ = lean_ctor_get(v_toApplicative_658_, 3);
v_toSeqRight_665_ = lean_ctor_get(v_toApplicative_658_, 4);
v_isSharedCheck_687_ = !lean_is_exclusive(v_toApplicative_658_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_toApplicative_658_, 1);
lean_dec(v_unused_688_);
v___x_667_ = v_toApplicative_658_;
v_isShared_668_ = v_isSharedCheck_687_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_toSeqRight_665_);
lean_inc(v_toSeqLeft_664_);
lean_inc(v_toSeq_663_);
lean_inc(v_toFunctor_662_);
lean_dec(v_toApplicative_658_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_687_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___f_669_; lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___x_673_; lean_object* v___f_674_; lean_object* v___f_675_; lean_object* v___f_676_; lean_object* v___x_678_; 
v___f_669_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__3));
v___f_670_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__4));
lean_inc_ref(v_toFunctor_662_);
v___f_671_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_671_, 0, v_toFunctor_662_);
v___f_672_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_672_, 0, v_toFunctor_662_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___f_671_);
lean_ctor_set(v___x_673_, 1, v___f_672_);
v___f_674_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_674_, 0, v_toSeqRight_665_);
v___f_675_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_675_, 0, v_toSeqLeft_664_);
v___f_676_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_676_, 0, v_toSeq_663_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 4, v___f_674_);
lean_ctor_set(v___x_667_, 3, v___f_675_);
lean_ctor_set(v___x_667_, 2, v___f_676_);
lean_ctor_set(v___x_667_, 1, v___f_669_);
lean_ctor_set(v___x_667_, 0, v___x_673_);
v___x_678_ = v___x_667_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___f_669_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v___f_676_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v___f_675_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v___f_674_);
v___x_678_ = v_reuseFailAlloc_686_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_680_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___f_670_);
lean_ctor_set(v___x_660_, 0, v___x_678_);
v___x_680_ = v___x_660_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___f_670_);
v___x_680_ = v_reuseFailAlloc_685_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_9043__overap_683_; lean_object* v___x_684_; 
v___x_681_ = lean_box(0);
v___x_682_ = l_instInhabitedOfMonad___redArg(v___x_680_, v___x_681_);
v___x_9043__overap_683_ = lean_panic_fn_borrowed(v___x_682_, v_msg_626_);
lean_dec(v___x_682_);
lean_inc(v___y_630_);
lean_inc_ref(v___y_629_);
lean_inc(v___y_628_);
lean_inc_ref(v___y_627_);
v___x_684_ = lean_apply_5(v___x_9043__overap_683_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, lean_box(0));
return v___x_684_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___boxed(lean_object* v_msg_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(v_msg_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_703_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__0));
v___x_706_ = l_Lean_stringToMessageData(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__2));
v___x_709_ = l_Lean_stringToMessageData(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_713_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_714_ = lean_unsigned_to_nat(11u);
v___x_715_ = lean_unsigned_to_nat(115u);
v___x_716_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__5));
v___x_717_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__4));
v___x_718_ = l_mkPanicMessageWithDecl(v___x_717_, v___x_716_, v___x_715_, v___x_714_, v___x_713_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(lean_object* v_constName_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_733_; lean_object* v_env_734_; uint8_t v___x_735_; lean_object* v___x_736_; 
v___x_733_ = lean_st_ref_get(v___y_723_);
v_env_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc_ref(v_env_734_);
lean_dec(v___x_733_);
v___x_735_ = 0;
lean_inc(v_constName_719_);
v___x_736_ = l_Lean_Environment_findAsync_x3f(v_env_734_, v_constName_719_, v___x_735_);
if (lean_obj_tag(v___x_736_) == 1)
{
lean_object* v_val_737_; uint8_t v_kind_738_; 
v_val_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v___x_736_, 1);
v_kind_738_ = lean_ctor_get_uint8(v_val_737_, sizeof(void*)*3);
if (v_kind_738_ == 0)
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_737_);
if (lean_obj_tag(v___x_739_) == 1)
{
lean_object* v_val_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_constName_719_);
v_val_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_val_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 0);
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_val_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec_ref(v___x_739_);
v___x_748_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7);
v___x_749_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(v___x_748_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_758_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_758_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
if (lean_obj_tag(v_a_750_) == 0)
{
lean_del_object(v___x_752_);
goto v___jp_725_;
}
else
{
lean_object* v_val_754_; lean_object* v___x_756_; 
lean_dec(v_constName_719_);
v_val_754_ = lean_ctor_get(v_a_750_, 0);
lean_inc(v_val_754_);
lean_dec_ref_known(v_a_750_, 1);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v_val_754_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_val_754_);
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
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_constName_719_);
v_a_759_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_749_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_749_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
else
{
lean_dec(v_val_737_);
goto v___jp_725_;
}
}
else
{
lean_dec(v___x_736_);
goto v___jp_725_;
}
v___jp_725_:
{
lean_object* v___x_726_; uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_726_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1);
v___x_727_ = 0;
v___x_728_ = l_Lean_MessageData_ofConstName(v_constName_719_, v___x_727_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_726_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_731_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___boxed(lean_object* v_constName_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(v_constName_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2(lean_object* v_declNameNonRec_776_, lean_object* v___f_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; lean_object* v_env_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v_env_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_783_ = lean_st_ref_get(v___y_781_);
v_env_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc_ref(v_env_784_);
lean_dec(v___x_783_);
v___x_785_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__0));
lean_inc_n(v_declNameNonRec_776_, 3);
v___x_786_ = l_Lean_Meta_mkEqLikeNameFor(v_env_784_, v_declNameNonRec_776_, v___x_785_);
v___x_787_ = lean_st_ref_get(v___y_781_);
v_env_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc_ref(v_env_788_);
lean_dec(v___x_787_);
v___x_789_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__1));
v___x_790_ = l_Lean_Meta_mkEqLikeNameFor(v_env_788_, v_declNameNonRec_776_, v___x_789_);
v___x_791_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(v_declNameNonRec_776_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v_toConstantVal_793_; lean_object* v_value_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_923_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v_toConstantVal_793_ = lean_ctor_get(v_a_792_, 0);
v_value_794_ = lean_ctor_get(v_a_792_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v_a_792_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; lean_object* v_unused_925_; 
v_unused_924_ = lean_ctor_get(v_a_792_, 3);
lean_dec(v_unused_924_);
v_unused_925_ = lean_ctor_get(v_a_792_, 2);
lean_dec(v_unused_925_);
v___x_796_ = v_a_792_;
v_isShared_797_ = v_isSharedCheck_923_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_value_794_);
lean_inc(v_toConstantVal_793_);
lean_dec(v_a_792_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_923_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_levelParams_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_920_; 
v_levelParams_798_ = lean_ctor_get(v_toConstantVal_793_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_toConstantVal_793_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; lean_object* v_unused_922_; 
v_unused_921_ = lean_ctor_get(v_toConstantVal_793_, 2);
lean_dec(v_unused_921_);
v_unused_922_ = lean_ctor_get(v_toConstantVal_793_, 0);
lean_dec(v_unused_922_);
v___x_800_ = v_toConstantVal_793_;
v_isShared_801_ = v_isSharedCheck_920_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_levelParams_798_);
lean_dec(v_toConstantVal_793_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_920_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___f_806_; lean_object* v___x_807_; 
v___x_802_ = lean_box(0);
lean_inc(v_levelParams_798_);
v___x_803_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(v_levelParams_798_, v___x_802_);
v___x_804_ = 0;
v___x_805_ = lean_box(v___x_804_);
lean_inc(v___x_790_);
v___f_806_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___boxed), 11, 4);
lean_closure_set(v___f_806_, 0, v_declNameNonRec_776_);
lean_closure_set(v___f_806_, 1, v___x_803_);
lean_closure_set(v___f_806_, 2, v___x_790_);
lean_closure_set(v___f_806_, 3, v___x_805_);
lean_inc_ref(v_value_794_);
v___x_807_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_794_, v___f_777_, v___x_804_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v_fst_809_; lean_object* v_snd_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_911_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v_fst_809_ = lean_ctor_get(v_a_808_, 0);
v_snd_810_ = lean_ctor_get(v_a_808_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_911_ == 0)
{
v___x_812_ = v_a_808_;
v_isShared_813_ = v_isSharedCheck_911_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_snd_810_);
lean_inc(v_fst_809_);
lean_dec(v_a_808_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_911_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
lean_inc(v_levelParams_798_);
lean_inc(v___x_790_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 2, v_fst_809_);
lean_ctor_set(v___x_800_, 0, v___x_790_);
v___x_815_ = v___x_800_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_levelParams_798_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_fst_809_);
v___x_815_ = v_reuseFailAlloc_910_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_819_; 
v___x_816_ = lean_box(1);
v___x_817_ = 1;
lean_inc(v___x_790_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 1);
lean_ctor_set(v___x_812_, 1, v___x_802_);
lean_ctor_set(v___x_812_, 0, v___x_790_);
v___x_819_ = v___x_812_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v___x_802_);
v___x_819_ = v_reuseFailAlloc_909_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_821_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 3, v___x_819_);
lean_ctor_set(v___x_796_, 2, v___x_816_);
lean_ctor_set(v___x_796_, 1, v_snd_810_);
lean_ctor_set(v___x_796_, 0, v___x_815_);
v___x_821_ = v___x_796_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_snd_810_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_908_, 3, v___x_819_);
v___x_821_ = v_reuseFailAlloc_908_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*4, v___x_817_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
v___x_823_ = l_Lean_addDecl(v___x_822_, v___x_804_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; lean_object* v_env_825_; lean_object* v_nextMacroScope_826_; lean_object* v_ngen_827_; lean_object* v_auxDeclNGen_828_; lean_object* v_traceState_829_; lean_object* v_recordedDeps_830_; lean_object* v_messages_831_; lean_object* v_infoState_832_; lean_object* v_snapshotTasks_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref_known(v___x_823_, 1);
v___x_824_ = lean_st_ref_take(v___y_781_);
v_env_825_ = lean_ctor_get(v___x_824_, 0);
v_nextMacroScope_826_ = lean_ctor_get(v___x_824_, 1);
v_ngen_827_ = lean_ctor_get(v___x_824_, 2);
v_auxDeclNGen_828_ = lean_ctor_get(v___x_824_, 3);
v_traceState_829_ = lean_ctor_get(v___x_824_, 4);
v_recordedDeps_830_ = lean_ctor_get(v___x_824_, 6);
v_messages_831_ = lean_ctor_get(v___x_824_, 7);
v_infoState_832_ = lean_ctor_get(v___x_824_, 8);
v_snapshotTasks_833_ = lean_ctor_get(v___x_824_, 9);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v___x_824_, 5);
lean_dec(v_unused_899_);
v___x_835_ = v___x_824_;
v_isShared_836_ = v_isSharedCheck_898_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_snapshotTasks_833_);
lean_inc(v_infoState_832_);
lean_inc(v_messages_831_);
lean_inc(v_recordedDeps_830_);
lean_inc(v_traceState_829_);
lean_inc(v_auxDeclNGen_828_);
lean_inc(v_ngen_827_);
lean_inc(v_nextMacroScope_826_);
lean_inc(v_env_825_);
lean_dec(v___x_824_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_898_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_837_ = l_Lean_addNoncomputable(v_env_825_, v___x_790_);
v___x_838_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 5, v___x_838_);
lean_ctor_set(v___x_835_, 0, v___x_837_);
v___x_840_ = v___x_835_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_nextMacroScope_826_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_ngen_827_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_auxDeclNGen_828_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v_traceState_829_);
lean_ctor_set(v_reuseFailAlloc_897_, 5, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_897_, 6, v_recordedDeps_830_);
lean_ctor_set(v_reuseFailAlloc_897_, 7, v_messages_831_);
lean_ctor_set(v_reuseFailAlloc_897_, 8, v_infoState_832_);
lean_ctor_set(v_reuseFailAlloc_897_, 9, v_snapshotTasks_833_);
v___x_840_ = v_reuseFailAlloc_897_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v_mctx_843_; lean_object* v_zetaDeltaFVarIds_844_; lean_object* v_postponed_845_; lean_object* v_diag_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_895_; 
v___x_841_ = lean_st_ref_put(v___y_781_, v___x_840_);
v___x_842_ = lean_st_ref_take(v___y_779_);
v_mctx_843_ = lean_ctor_get(v___x_842_, 0);
v_zetaDeltaFVarIds_844_ = lean_ctor_get(v___x_842_, 2);
v_postponed_845_ = lean_ctor_get(v___x_842_, 3);
v_diag_846_ = lean_ctor_get(v___x_842_, 4);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v___x_842_, 1);
lean_dec(v_unused_896_);
v___x_848_ = v___x_842_;
v_isShared_849_ = v_isSharedCheck_895_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_diag_846_);
lean_inc(v_postponed_845_);
lean_inc(v_zetaDeltaFVarIds_844_);
lean_inc(v_mctx_843_);
lean_dec(v___x_842_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_895_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v___x_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_mctx_843_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_zetaDeltaFVarIds_844_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_postponed_845_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_diag_846_);
v___x_852_ = v_reuseFailAlloc_894_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_st_ref_put(v___y_779_, v___x_852_);
v___x_854_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_794_, v___f_806_, v___x_804_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v_fst_856_; lean_object* v_snd_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_885_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v_fst_856_ = lean_ctor_get(v_a_855_, 0);
v_snd_857_ = lean_ctor_get(v_a_855_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_a_855_);
if (v_isSharedCheck_885_ == 0)
{
v___x_859_ = v_a_855_;
v_isShared_860_ = v_isSharedCheck_885_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_snd_857_);
lean_inc(v_fst_856_);
lean_dec(v_a_855_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_885_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
lean_inc_n(v___x_786_, 2);
v___x_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_861_, 0, v___x_786_);
lean_ctor_set(v___x_861_, 1, v_levelParams_798_);
lean_ctor_set(v___x_861_, 2, v_fst_856_);
if (v_isShared_860_ == 0)
{
lean_ctor_set_tag(v___x_859_, 1);
lean_ctor_set(v___x_859_, 1, v___x_802_);
lean_ctor_set(v___x_859_, 0, v___x_786_);
v___x_863_ = v___x_859_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_802_);
v___x_863_ = v_reuseFailAlloc_884_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_a_866_; lean_object* v___x_867_; 
v___x_864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_864_, 0, v___x_861_);
lean_ctor_set(v___x_864_, 1, v_snd_857_);
lean_ctor_set(v___x_864_, 2, v___x_863_);
v___x_865_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v___x_864_, v___y_781_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref(v___x_865_);
v___x_867_ = l_Lean_addDecl(v_a_866_, v___x_804_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v___x_867_, 0);
lean_dec(v_unused_875_);
v___x_869_ = v___x_867_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_dec(v___x_867_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_786_);
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_786_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v___x_786_);
v_a_876_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_867_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_867_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_levelParams_798_);
lean_dec(v___x_786_);
v_a_886_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_854_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_854_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
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
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec_ref(v___f_806_);
lean_dec(v_levelParams_798_);
lean_dec_ref(v_value_794_);
lean_dec(v___x_790_);
lean_dec(v___x_786_);
v_a_900_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_823_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_823_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
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
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v___f_806_);
lean_del_object(v___x_800_);
lean_dec(v_levelParams_798_);
lean_del_object(v___x_796_);
lean_dec_ref(v_value_794_);
lean_dec(v___x_790_);
lean_dec(v___x_786_);
v_a_912_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_807_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_807_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v___x_790_);
lean_dec(v___x_786_);
lean_dec_ref(v___f_777_);
lean_dec(v_declNameNonRec_776_);
v_a_926_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_791_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_791_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___boxed(lean_object* v_declNameNonRec_934_, lean_object* v___f_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2(v_declNameNonRec_934_, v___f_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(lean_object* v_declNameNonRec_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___f_948_; lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v_env_951_; uint8_t v___x_952_; lean_object* v___x_953_; 
lean_inc_n(v_declNameNonRec_942_, 2);
v___f_948_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___boxed), 8, 1);
lean_closure_set(v___f_948_, 0, v_declNameNonRec_942_);
v___f_949_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___boxed), 7, 2);
lean_closure_set(v___f_949_, 0, v_declNameNonRec_942_);
lean_closure_set(v___f_949_, 1, v___f_948_);
v___x_950_ = lean_st_ref_get(v_a_946_);
v_env_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc_ref(v_env_951_);
lean_dec(v___x_950_);
v___x_952_ = l_Lean_Environment_hasExposedBody(v_env_951_, v_declNameNonRec_942_);
v___x_953_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v___f_949_, v___x_952_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___boxed(lean_object* v_declNameNonRec_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(v_declNameNonRec_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0(lean_object* v_00_u03b1_961_, lean_object* v_msg_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v_msg_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___boxed(lean_object* v_00_u03b1_969_, lean_object* v_msg_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0(v_00_u03b1_969_, v_msg_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t v___x_977_, uint8_t v___x_978_, uint8_t v_____do__lift_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
if (v_____do__lift_979_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_box(v___x_977_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_box(v___x_978_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object* v___x_989_, lean_object* v___x_990_, lean_object* v_____do__lift_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v___x_4165__boxed_997_; uint8_t v___x_4166__boxed_998_; uint8_t v_____do__lift_4167__boxed_999_; lean_object* v_res_1000_; 
v___x_4165__boxed_997_ = lean_unbox(v___x_989_);
v___x_4166__boxed_998_ = lean_unbox(v___x_990_);
v_____do__lift_4167__boxed_999_ = lean_unbox(v_____do__lift_991_);
v_res_1000_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_4165__boxed_997_, v___x_4166__boxed_998_, v_____do__lift_4167__boxed_999_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_1000_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object* v_as_1001_, size_t v_i_1002_, size_t v_stop_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_usize_dec_eq(v_i_1002_, v_stop_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; uint8_t v_kind_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_array_uget_borrowed(v_as_1001_, v_i_1002_);
v_kind_1006_ = lean_ctor_get_uint8(v___x_1005_, sizeof(void*)*9);
v___x_1007_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1006_);
if (v___x_1007_ == 0)
{
uint8_t v___x_1008_; 
v___x_1008_ = 1;
return v___x_1008_;
}
else
{
size_t v___x_1009_; size_t v___x_1010_; 
v___x_1009_ = ((size_t)1ULL);
v___x_1010_ = lean_usize_add(v_i_1002_, v___x_1009_);
v_i_1002_ = v___x_1010_;
goto _start;
}
}
else
{
uint8_t v___x_1012_; 
v___x_1012_ = 0;
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object* v_as_1013_, lean_object* v_i_1014_, lean_object* v_stop_1015_){
_start:
{
size_t v_i_boxed_1016_; size_t v_stop_boxed_1017_; uint8_t v_res_1018_; lean_object* v_r_1019_; 
v_i_boxed_1016_ = lean_unbox_usize(v_i_1014_);
lean_dec(v_i_1014_);
v_stop_boxed_1017_ = lean_unbox_usize(v_stop_1015_);
lean_dec(v_stop_1015_);
v_res_1018_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_as_1013_, v_i_boxed_1016_, v_stop_boxed_1017_);
lean_dec_ref(v_as_1013_);
v_r_1019_ = lean_box(v_res_1018_);
return v_r_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t v_sz_1020_, size_t v_i_1021_, lean_object* v_bs_1022_){
_start:
{
uint8_t v___x_1023_; 
v___x_1023_ = lean_usize_dec_lt(v_i_1021_, v_sz_1020_);
if (v___x_1023_ == 0)
{
return v_bs_1022_;
}
else
{
lean_object* v_v_1024_; lean_object* v_declName_1025_; lean_object* v___x_1026_; lean_object* v_bs_x27_1027_; size_t v___x_1028_; size_t v___x_1029_; lean_object* v___x_1030_; 
v_v_1024_ = lean_array_uget_borrowed(v_bs_1022_, v_i_1021_);
v_declName_1025_ = lean_ctor_get(v_v_1024_, 3);
lean_inc(v_declName_1025_);
v___x_1026_ = lean_unsigned_to_nat(0u);
v_bs_x27_1027_ = lean_array_uset(v_bs_1022_, v_i_1021_, v___x_1026_);
v___x_1028_ = ((size_t)1ULL);
v___x_1029_ = lean_usize_add(v_i_1021_, v___x_1028_);
v___x_1030_ = lean_array_uset(v_bs_x27_1027_, v_i_1021_, v_declName_1025_);
v_i_1021_ = v___x_1029_;
v_bs_1022_ = v___x_1030_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object* v_sz_1032_, lean_object* v_i_1033_, lean_object* v_bs_1034_){
_start:
{
size_t v_sz_boxed_1035_; size_t v_i_boxed_1036_; lean_object* v_res_1037_; 
v_sz_boxed_1035_ = lean_unbox_usize(v_sz_1032_);
lean_dec(v_sz_1032_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1033_);
lean_dec(v_i_1033_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_boxed_1035_, v_i_boxed_1036_, v_bs_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object* v___x_1038_, lean_object* v_declNameNonRec_1039_, lean_object* v_fixedParamPerms_1040_, lean_object* v_fixpointType_1041_, lean_object* v_fixEq_x3f_1042_, uint8_t v_a_1043_, lean_object* v_as_1044_, size_t v_i_1045_, size_t v_stop_1046_, lean_object* v_b_1047_){
_start:
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_usize_dec_eq(v_i_1045_, v_stop_1046_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v_levelParams_1050_; lean_object* v_declName_1051_; lean_object* v_type_1052_; lean_object* v_value_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; 
v___x_1049_ = lean_array_uget_borrowed(v_as_1044_, v_i_1045_);
v_levelParams_1050_ = lean_ctor_get(v___x_1049_, 1);
v_declName_1051_ = lean_ctor_get(v___x_1049_, 3);
v_type_1052_ = lean_ctor_get(v___x_1049_, 6);
v_value_1053_ = lean_ctor_get(v___x_1049_, 7);
v___x_1054_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
lean_inc(v_fixEq_x3f_1042_);
lean_inc_ref(v_fixpointType_1041_);
lean_inc_ref(v_fixedParamPerms_1040_);
lean_inc(v_declNameNonRec_1039_);
lean_inc_ref(v___x_1038_);
lean_inc_ref(v_value_1053_);
lean_inc_ref(v_type_1052_);
lean_inc(v_levelParams_1050_);
lean_inc_n(v_declName_1051_, 2);
v___x_1055_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1055_, 0, v_declName_1051_);
lean_ctor_set(v___x_1055_, 1, v_levelParams_1050_);
lean_ctor_set(v___x_1055_, 2, v_type_1052_);
lean_ctor_set(v___x_1055_, 3, v_value_1053_);
lean_ctor_set(v___x_1055_, 4, v___x_1038_);
lean_ctor_set(v___x_1055_, 5, v_declNameNonRec_1039_);
lean_ctor_set(v___x_1055_, 6, v_fixedParamPerms_1040_);
lean_ctor_set(v___x_1055_, 7, v_fixpointType_1041_);
lean_ctor_set(v___x_1055_, 8, v_fixEq_x3f_1042_);
v___x_1056_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1054_, v_b_1047_, v_declName_1051_, v___x_1055_, v_a_1043_);
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1045_, v___x_1057_);
v_i_1045_ = v___x_1058_;
v_b_1047_ = v___x_1056_;
goto _start;
}
else
{
lean_dec(v_fixEq_x3f_1042_);
lean_dec_ref(v_fixpointType_1041_);
lean_dec_ref(v_fixedParamPerms_1040_);
lean_dec(v_declNameNonRec_1039_);
lean_dec_ref(v___x_1038_);
return v_b_1047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object* v___x_1060_, lean_object* v_declNameNonRec_1061_, lean_object* v_fixedParamPerms_1062_, lean_object* v_fixpointType_1063_, lean_object* v_fixEq_x3f_1064_, lean_object* v_a_1065_, lean_object* v_as_1066_, lean_object* v_i_1067_, lean_object* v_stop_1068_, lean_object* v_b_1069_){
_start:
{
uint8_t v_a_4226__boxed_1070_; size_t v_i_boxed_1071_; size_t v_stop_boxed_1072_; lean_object* v_res_1073_; 
v_a_4226__boxed_1070_ = lean_unbox(v_a_1065_);
v_i_boxed_1071_ = lean_unbox_usize(v_i_1067_);
lean_dec(v_i_1067_);
v_stop_boxed_1072_ = lean_unbox_usize(v_stop_1068_);
lean_dec(v_stop_1068_);
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_1060_, v_declNameNonRec_1061_, v_fixedParamPerms_1062_, v_fixpointType_1063_, v_fixEq_x3f_1064_, v_a_4226__boxed_1070_, v_as_1066_, v_i_boxed_1071_, v_stop_boxed_1072_, v_b_1069_);
lean_dec_ref(v_as_1066_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object* v_as_1074_, size_t v_i_1075_, size_t v_stop_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v___x_1081_; 
v___x_1081_ = lean_usize_dec_eq(v_i_1075_, v_stop_1076_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v_declName_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_array_uget_borrowed(v_as_1074_, v_i_1075_);
v_declName_1083_ = lean_ctor_get(v___x_1082_, 3);
lean_inc(v_declName_1083_);
v___x_1084_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_1083_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; size_t v___x_1086_; size_t v___x_1087_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = ((size_t)1ULL);
v___x_1087_ = lean_usize_add(v_i_1075_, v___x_1086_);
v_i_1075_ = v___x_1087_;
v_b_1077_ = v_a_1085_;
goto _start;
}
else
{
return v___x_1084_;
}
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v_b_1077_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object* v_as_1090_, lean_object* v_i_1091_, lean_object* v_stop_1092_, lean_object* v_b_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
size_t v_i_boxed_1097_; size_t v_stop_boxed_1098_; lean_object* v_res_1099_; 
v_i_boxed_1097_ = lean_unbox_usize(v_i_1091_);
lean_dec(v_i_1091_);
v_stop_boxed_1098_ = lean_unbox_usize(v_stop_1092_);
lean_dec(v_stop_1092_);
v_res_1099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_1090_, v_i_boxed_1097_, v_stop_boxed_1098_, v_b_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v_as_1090_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t v___x_1100_, lean_object* v_as_1101_, size_t v_i_1102_, size_t v_stop_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_usize_dec_eq(v_i_1102_, v_stop_1103_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v_type_1115_; uint8_t v___x_1116_; uint8_t v_a_1118_; lean_object* v___x_1121_; 
v___x_1114_ = lean_array_uget_borrowed(v_as_1101_, v_i_1102_);
v_type_1115_ = lean_ctor_get(v___x_1114_, 6);
v___x_1116_ = 1;
lean_inc_ref(v_type_1115_);
v___x_1121_ = l_Lean_Meta_isProp(v_type_1115_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; uint8_t v___x_1123_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = lean_unbox(v_a_1122_);
lean_dec(v_a_1122_);
if (v___x_1123_ == 0)
{
v_a_1118_ = v___x_1100_;
goto v___jp_1117_;
}
else
{
goto v___jp_1109_;
}
}
else
{
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1124_; uint8_t v___x_1125_; 
v_a_1124_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1125_ = lean_unbox(v_a_1124_);
lean_dec(v_a_1124_);
v_a_1118_ = v___x_1125_;
goto v___jp_1117_;
}
else
{
return v___x_1121_;
}
}
v___jp_1117_:
{
if (v_a_1118_ == 0)
{
goto v___jp_1109_;
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_box(v___x_1116_);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
}
else
{
uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = 0;
v___x_1127_ = lean_box(v___x_1126_);
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
v___jp_1109_:
{
size_t v___x_1110_; size_t v___x_1111_; 
v___x_1110_ = ((size_t)1ULL);
v___x_1111_ = lean_usize_add(v_i_1102_, v___x_1110_);
v_i_1102_ = v___x_1111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object* v___x_1129_, lean_object* v_as_1130_, lean_object* v_i_1131_, lean_object* v_stop_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
uint8_t v___x_4273__boxed_1138_; size_t v_i_boxed_1139_; size_t v_stop_boxed_1140_; lean_object* v_res_1141_; 
v___x_4273__boxed_1138_ = lean_unbox(v___x_1129_);
v_i_boxed_1139_ = lean_unbox_usize(v_i_1131_);
lean_dec(v_i_1131_);
v_stop_boxed_1140_ = lean_unbox_usize(v_stop_1132_);
lean_dec(v_stop_1132_);
v_res_1141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_4273__boxed_1138_, v_as_1130_, v_i_boxed_1139_, v_stop_boxed_1140_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec_ref(v_as_1130_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object* v_preDefs_1142_, lean_object* v_declNameNonRec_1143_, lean_object* v_fixedParamPerms_1144_, lean_object* v_fixpointType_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___y_1155_; lean_object* v_nextMacroScope_1156_; lean_object* v_ngen_1157_; lean_object* v_auxDeclNGen_1158_; lean_object* v_traceState_1159_; lean_object* v_recordedDeps_1160_; lean_object* v_messages_1161_; lean_object* v_infoState_1162_; lean_object* v_snapshotTasks_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; size_t v___y_1193_; lean_object* v___y_1194_; uint8_t v___y_1195_; lean_object* v_fixEq_x3f_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1216_; lean_object* v___y_1259_; uint8_t v___x_1260_; 
v___x_1189_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_array_get_size(v_preDefs_1142_);
v___x_1260_ = lean_nat_dec_lt(v___x_1190_, v___x_1191_);
if (v___x_1260_ == 0)
{
goto v___jp_1247_;
}
else
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_nat_dec_le(v___x_1191_, v___x_1191_);
if (v___x_1262_ == 0)
{
if (v___x_1260_ == 0)
{
goto v___jp_1247_;
}
else
{
size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = ((size_t)0ULL);
v___x_1264_ = lean_usize_of_nat(v___x_1191_);
v___x_1265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_1142_, v___x_1263_, v___x_1264_, v___x_1261_, v_a_1148_, v_a_1149_);
v___y_1259_ = v___x_1265_;
goto v___jp_1258_;
}
}
else
{
size_t v___x_1266_; size_t v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = ((size_t)0ULL);
v___x_1267_ = lean_usize_of_nat(v___x_1191_);
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_1142_, v___x_1266_, v___x_1267_, v___x_1261_, v_a_1148_, v_a_1149_);
v___y_1259_ = v___x_1268_;
goto v___jp_1258_;
}
}
v___jp_1151_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
v___jp_1154_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_mctx_1170_; lean_object* v_zetaDeltaFVarIds_1171_; lean_object* v_postponed_1172_; lean_object* v_diag_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1184_; 
v___x_1166_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
v___x_1167_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1167_, 0, v___y_1165_);
lean_ctor_set(v___x_1167_, 1, v_nextMacroScope_1156_);
lean_ctor_set(v___x_1167_, 2, v_ngen_1157_);
lean_ctor_set(v___x_1167_, 3, v_auxDeclNGen_1158_);
lean_ctor_set(v___x_1167_, 4, v_traceState_1159_);
lean_ctor_set(v___x_1167_, 5, v___x_1166_);
lean_ctor_set(v___x_1167_, 6, v_recordedDeps_1160_);
lean_ctor_set(v___x_1167_, 7, v_messages_1161_);
lean_ctor_set(v___x_1167_, 8, v_infoState_1162_);
lean_ctor_set(v___x_1167_, 9, v_snapshotTasks_1163_);
v___x_1168_ = lean_st_ref_put(v___y_1164_, v___x_1167_);
v___x_1169_ = lean_st_ref_take(v___y_1155_);
v_mctx_1170_ = lean_ctor_get(v___x_1169_, 0);
v_zetaDeltaFVarIds_1171_ = lean_ctor_get(v___x_1169_, 2);
v_postponed_1172_ = lean_ctor_get(v___x_1169_, 3);
v_diag_1173_ = lean_ctor_get(v___x_1169_, 4);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v___x_1169_, 1);
lean_dec(v_unused_1185_);
v___x_1175_ = v___x_1169_;
v_isShared_1176_ = v_isSharedCheck_1184_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_diag_1173_);
lean_inc(v_postponed_1172_);
lean_inc(v_zetaDeltaFVarIds_1171_);
lean_inc(v_mctx_1170_);
lean_dec(v___x_1169_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1184_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1178_);
v___x_1180_ = v___x_1175_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_mctx_1170_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_zetaDeltaFVarIds_1171_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_postponed_1172_);
lean_ctor_set(v_reuseFailAlloc_1183_, 4, v_diag_1173_);
v___x_1180_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_st_ref_put(v___y_1155_, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1177_);
return v___x_1182_;
}
}
}
v___jp_1186_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
v___jp_1192_:
{
lean_object* v___x_1199_; lean_object* v_env_1200_; lean_object* v_nextMacroScope_1201_; lean_object* v_ngen_1202_; lean_object* v_auxDeclNGen_1203_; lean_object* v_traceState_1204_; lean_object* v_recordedDeps_1205_; lean_object* v_messages_1206_; lean_object* v_infoState_1207_; lean_object* v_snapshotTasks_1208_; uint8_t v___x_1209_; 
v___x_1199_ = lean_st_ref_take(v___y_1198_);
v_env_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc_ref(v_env_1200_);
v_nextMacroScope_1201_ = lean_ctor_get(v___x_1199_, 1);
lean_inc(v_nextMacroScope_1201_);
v_ngen_1202_ = lean_ctor_get(v___x_1199_, 2);
lean_inc_ref(v_ngen_1202_);
v_auxDeclNGen_1203_ = lean_ctor_get(v___x_1199_, 3);
lean_inc_ref(v_auxDeclNGen_1203_);
v_traceState_1204_ = lean_ctor_get(v___x_1199_, 4);
lean_inc_ref(v_traceState_1204_);
v_recordedDeps_1205_ = lean_ctor_get(v___x_1199_, 6);
lean_inc_ref(v_recordedDeps_1205_);
v_messages_1206_ = lean_ctor_get(v___x_1199_, 7);
lean_inc_ref(v_messages_1206_);
v_infoState_1207_ = lean_ctor_get(v___x_1199_, 8);
lean_inc_ref(v_infoState_1207_);
v_snapshotTasks_1208_ = lean_ctor_get(v___x_1199_, 9);
lean_inc_ref(v_snapshotTasks_1208_);
lean_dec(v___x_1199_);
v___x_1209_ = lean_nat_dec_lt(v___x_1190_, v___x_1191_);
if (v___x_1209_ == 0)
{
lean_dec(v_fixEq_x3f_1196_);
lean_dec_ref(v___y_1194_);
lean_dec_ref(v_fixpointType_1145_);
lean_dec_ref(v_fixedParamPerms_1144_);
lean_dec(v_declNameNonRec_1143_);
lean_dec_ref(v_preDefs_1142_);
v___y_1155_ = v___y_1197_;
v_nextMacroScope_1156_ = v_nextMacroScope_1201_;
v_ngen_1157_ = v_ngen_1202_;
v_auxDeclNGen_1158_ = v_auxDeclNGen_1203_;
v_traceState_1159_ = v_traceState_1204_;
v_recordedDeps_1160_ = v_recordedDeps_1205_;
v_messages_1161_ = v_messages_1206_;
v_infoState_1162_ = v_infoState_1207_;
v_snapshotTasks_1163_ = v_snapshotTasks_1208_;
v___y_1164_ = v___y_1198_;
v___y_1165_ = v_env_1200_;
goto v___jp_1154_;
}
else
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_nat_dec_le(v___x_1191_, v___x_1191_);
if (v___x_1210_ == 0)
{
if (v___x_1209_ == 0)
{
lean_dec(v_fixEq_x3f_1196_);
lean_dec_ref(v___y_1194_);
lean_dec_ref(v_fixpointType_1145_);
lean_dec_ref(v_fixedParamPerms_1144_);
lean_dec(v_declNameNonRec_1143_);
lean_dec_ref(v_preDefs_1142_);
v___y_1155_ = v___y_1197_;
v_nextMacroScope_1156_ = v_nextMacroScope_1201_;
v_ngen_1157_ = v_ngen_1202_;
v_auxDeclNGen_1158_ = v_auxDeclNGen_1203_;
v_traceState_1159_ = v_traceState_1204_;
v_recordedDeps_1160_ = v_recordedDeps_1205_;
v_messages_1161_ = v_messages_1206_;
v_infoState_1162_ = v_infoState_1207_;
v_snapshotTasks_1163_ = v_snapshotTasks_1208_;
v___y_1164_ = v___y_1198_;
v___y_1165_ = v_env_1200_;
goto v___jp_1154_;
}
else
{
size_t v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_usize_of_nat(v___x_1191_);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___y_1194_, v_declNameNonRec_1143_, v_fixedParamPerms_1144_, v_fixpointType_1145_, v_fixEq_x3f_1196_, v___y_1195_, v_preDefs_1142_, v___y_1193_, v___x_1211_, v_env_1200_);
lean_dec_ref(v_preDefs_1142_);
v___y_1155_ = v___y_1197_;
v_nextMacroScope_1156_ = v_nextMacroScope_1201_;
v_ngen_1157_ = v_ngen_1202_;
v_auxDeclNGen_1158_ = v_auxDeclNGen_1203_;
v_traceState_1159_ = v_traceState_1204_;
v_recordedDeps_1160_ = v_recordedDeps_1205_;
v_messages_1161_ = v_messages_1206_;
v_infoState_1162_ = v_infoState_1207_;
v_snapshotTasks_1163_ = v_snapshotTasks_1208_;
v___y_1164_ = v___y_1198_;
v___y_1165_ = v___x_1212_;
goto v___jp_1154_;
}
}
else
{
size_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_usize_of_nat(v___x_1191_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___y_1194_, v_declNameNonRec_1143_, v_fixedParamPerms_1144_, v_fixpointType_1145_, v_fixEq_x3f_1196_, v___y_1195_, v_preDefs_1142_, v___y_1193_, v___x_1213_, v_env_1200_);
lean_dec_ref(v_preDefs_1142_);
v___y_1155_ = v___y_1197_;
v_nextMacroScope_1156_ = v_nextMacroScope_1201_;
v_ngen_1157_ = v_ngen_1202_;
v_auxDeclNGen_1158_ = v_auxDeclNGen_1203_;
v_traceState_1159_ = v_traceState_1204_;
v_recordedDeps_1160_ = v_recordedDeps_1205_;
v_messages_1161_ = v_messages_1206_;
v_infoState_1162_ = v_infoState_1207_;
v_snapshotTasks_1163_ = v_snapshotTasks_1208_;
v___y_1164_ = v___y_1198_;
v___y_1165_ = v___x_1214_;
goto v___jp_1154_;
}
}
}
v___jp_1215_:
{
if (lean_obj_tag(v___y_1216_) == 0)
{
lean_object* v_a_1217_; uint8_t v___x_1218_; 
v_a_1217_ = lean_ctor_get(v___y_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___y_1216_, 1);
v___x_1218_ = lean_unbox(v_a_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v_declName_1220_; size_t v_sz_1221_; size_t v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1219_ = lean_array_get_borrowed(v___x_1189_, v_preDefs_1142_, v___x_1190_);
v_declName_1220_ = lean_ctor_get(v___x_1219_, 3);
v_sz_1221_ = lean_array_size(v_preDefs_1142_);
v___x_1222_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_1142_);
v___x_1223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_1221_, v___x_1222_, v_preDefs_1142_);
v___x_1224_ = lean_name_eq(v_declNameNonRec_1143_, v_declName_1220_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_inc(v_declNameNonRec_1143_);
v___x_1225_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(v_declNameNonRec_1143_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1227_, 0, v_a_1226_);
v___x_1228_ = lean_unbox(v_a_1217_);
lean_dec(v_a_1217_);
v___y_1193_ = v___x_1222_;
v___y_1194_ = v___x_1223_;
v___y_1195_ = v___x_1228_;
v_fixEq_x3f_1196_ = v___x_1227_;
v___y_1197_ = v_a_1147_;
v___y_1198_ = v_a_1149_;
goto v___jp_1192_;
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref(v___x_1223_);
lean_dec(v_a_1217_);
lean_dec_ref(v_fixpointType_1145_);
lean_dec_ref(v_fixedParamPerms_1144_);
lean_dec(v_declNameNonRec_1143_);
lean_dec_ref(v_preDefs_1142_);
v_a_1229_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1225_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1225_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
else
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_unbox(v_a_1217_);
lean_dec(v_a_1217_);
v___y_1193_ = v___x_1222_;
v___y_1194_ = v___x_1223_;
v___y_1195_ = v___x_1238_;
v_fixEq_x3f_1196_ = v___x_1237_;
v___y_1197_ = v_a_1147_;
v___y_1198_ = v_a_1149_;
goto v___jp_1192_;
}
}
else
{
lean_dec(v_a_1217_);
lean_dec_ref(v_fixpointType_1145_);
lean_dec_ref(v_fixedParamPerms_1144_);
lean_dec(v_declNameNonRec_1143_);
lean_dec_ref(v_preDefs_1142_);
goto v___jp_1151_;
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v_fixpointType_1145_);
lean_dec_ref(v_fixedParamPerms_1144_);
lean_dec(v_declNameNonRec_1143_);
lean_dec_ref(v_preDefs_1142_);
v_a_1239_ = lean_ctor_get(v___y_1216_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___y_1216_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___y_1216_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___y_1216_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
v___jp_1247_:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_nat_dec_lt(v___x_1190_, v___x_1191_);
if (v___x_1248_ == 0)
{
lean_dec_ref(v_fixpointType_1145_);
lean_dec_ref(v_fixedParamPerms_1144_);
lean_dec(v_declNameNonRec_1143_);
lean_dec_ref(v_preDefs_1142_);
goto v___jp_1186_;
}
else
{
if (v___x_1248_ == 0)
{
lean_dec_ref(v_fixpointType_1145_);
lean_dec_ref(v_fixedParamPerms_1144_);
lean_dec(v_declNameNonRec_1143_);
lean_dec_ref(v_preDefs_1142_);
goto v___jp_1186_;
}
else
{
size_t v___x_1249_; size_t v___x_1250_; uint8_t v___x_1251_; 
v___x_1249_ = ((size_t)0ULL);
v___x_1250_ = lean_usize_of_nat(v___x_1191_);
v___x_1251_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_preDefs_1142_, v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec_ref(v_fixpointType_1145_);
lean_dec_ref(v_fixedParamPerms_1144_);
lean_dec(v_declNameNonRec_1143_);
lean_dec_ref(v_preDefs_1142_);
goto v___jp_1186_;
}
else
{
uint8_t v___x_1252_; 
v___x_1252_ = 0;
if (v___x_1248_ == 0)
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_1251_, v___x_1252_, v___x_1248_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
v___y_1216_ = v___x_1253_;
goto v___jp_1215_;
}
else
{
if (v___x_1248_ == 0)
{
lean_dec_ref(v_fixpointType_1145_);
lean_dec_ref(v_fixedParamPerms_1144_);
lean_dec(v_declNameNonRec_1143_);
lean_dec_ref(v_preDefs_1142_);
goto v___jp_1151_;
}
else
{
lean_object* v___x_1254_; 
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_1251_, v_preDefs_1142_, v___x_1249_, v___x_1250_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; uint8_t v___x_1256_; lean_object* v___x_1257_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = lean_unbox(v_a_1255_);
lean_dec(v_a_1255_);
v___x_1257_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_1251_, v___x_1252_, v___x_1256_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
v___y_1216_ = v___x_1257_;
goto v___jp_1215_;
}
else
{
v___y_1216_ = v___x_1254_;
goto v___jp_1215_;
}
}
}
}
}
}
}
v___jp_1258_:
{
if (lean_obj_tag(v___y_1259_) == 0)
{
lean_dec_ref_known(v___y_1259_, 1);
goto v___jp_1247_;
}
else
{
lean_dec_ref(v_fixpointType_1145_);
lean_dec_ref(v_fixedParamPerms_1144_);
lean_dec(v_declNameNonRec_1143_);
lean_dec_ref(v_preDefs_1142_);
return v___y_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(lean_object* v_preDefs_1269_, lean_object* v_declNameNonRec_1270_, lean_object* v_fixedParamPerms_1271_, lean_object* v_fixpointType_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_preDefs_1269_, v_declNameNonRec_1270_, v_fixedParamPerms_1271_, v_fixpointType_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object* v_as_1279_, size_t v_i_1280_, size_t v_stop_1281_, lean_object* v_b_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_1279_, v_i_1280_, v_stop_1281_, v_b_1282_, v___y_1285_, v___y_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object* v_as_1289_, lean_object* v_i_1290_, lean_object* v_stop_1291_, lean_object* v_b_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
size_t v_i_boxed_1298_; size_t v_stop_boxed_1299_; lean_object* v_res_1300_; 
v_i_boxed_1298_ = lean_unbox_usize(v_i_1290_);
lean_dec(v_i_1290_);
v_stop_boxed_1299_ = lean_unbox_usize(v_stop_1291_);
lean_dec(v_stop_1291_);
v_res_1300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(v_as_1289_, v_i_boxed_1298_, v_stop_boxed_1299_, v_b_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec_ref(v_as_1289_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(lean_object* v_mvarId_1301_, lean_object* v_x_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1301_, v_x_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
v_a_1317_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1308_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1308_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg___boxed(lean_object* v_mvarId_1325_, lean_object* v_x_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1325_, v_x_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(lean_object* v_00_u03b1_1333_, lean_object* v_mvarId_1334_, lean_object* v_x_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1334_, v_x_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_mvarId_1343_, lean_object* v_x_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(v_00_u03b1_1342_, v_mvarId_1343_, v_x_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1350_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object* v_declName_1351_, lean_object* v_declNameNonRec_1352_, lean_object* v_n_1353_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_name_eq(v_n_1353_, v_declName_1351_);
if (v___x_1354_ == 0)
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_name_eq(v_n_1353_, v_declNameNonRec_1352_);
return v___x_1355_;
}
else
{
return v___x_1354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object* v_declName_1356_, lean_object* v_declNameNonRec_1357_, lean_object* v_n_1358_){
_start:
{
uint8_t v_res_1359_; lean_object* v_r_1360_; 
v_res_1359_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(v_declName_1356_, v_declNameNonRec_1357_, v_n_1358_);
lean_dec(v_n_1358_);
lean_dec(v_declNameNonRec_1357_);
lean_dec(v_declName_1356_);
v_r_1360_ = lean_box(v_res_1359_);
return v_r_1360_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5));
v___x_1371_ = l_Lean_MessageData_ofFormat(v___x_1370_);
return v___x_1371_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6);
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object* v_mvarId_1374_, lean_object* v___f_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
lean_inc(v_mvarId_1374_);
v___x_1381_ = l_Lean_MVarId_getType_x27(v_mvarId_1374_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_1384_ = lean_unsigned_to_nat(3u);
v___x_1385_ = l_Lean_Expr_isAppOfArity(v_a_1382_, v___x_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec(v_a_1382_);
lean_dec_ref(v___f_1375_);
v___x_1386_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3));
v___x_1387_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7);
v___x_1388_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1386_, v_mvarId_1374_, v___x_1387_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1388_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; 
v___x_1389_ = l_Lean_Expr_appFn_x21(v_a_1382_);
v___x_1390_ = l_Lean_Expr_appArg_x21(v___x_1389_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = l_Lean_Expr_appArg_x21(v_a_1382_);
lean_dec(v_a_1382_);
v___x_1392_ = 0;
v___x_1393_ = l_Lean_Meta_deltaExpand(v___x_1390_, v___f_1375_, v___x_1392_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1395_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1395_ = l_Lean_Meta_mkEq(v_a_1394_, v___x_1391_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1374_, v_a_1396_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1397_;
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec(v_mvarId_1374_);
v_a_1398_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1395_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1395_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec_ref(v___x_1391_);
lean_dec(v_mvarId_1374_);
v_a_1406_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1393_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1393_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v___f_1375_);
lean_dec(v_mvarId_1374_);
v_a_1414_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1381_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1381_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed(lean_object* v_mvarId_1422_, lean_object* v___f_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(v_mvarId_1422_, v___f_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object* v_declName_1430_, lean_object* v_declNameNonRec_1431_, lean_object* v_mvarId_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___f_1438_; lean_object* v___f_1439_; lean_object* v___x_1440_; 
v___f_1438_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1438_, 0, v_declName_1430_);
lean_closure_set(v___f_1438_, 1, v_declNameNonRec_1431_);
lean_inc(v_mvarId_1432_);
v___f_1439_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1439_, 0, v_mvarId_1432_);
lean_closure_set(v___f_1439_, 1, v___f_1438_);
v___x_1440_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1432_, v___f_1439_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(lean_object* v_declName_1441_, lean_object* v_declNameNonRec_1442_, lean_object* v_mvarId_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_1441_, v_declNameNonRec_1442_, v_mvarId_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(lean_object* v_msg_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = l_Lean_instInhabitedExpr;
v___x_1452_ = lean_panic_fn_borrowed(v___x_1451_, v_msg_1450_);
return v___x_1452_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0));
v___x_1455_ = l_Lean_stringToMessageData(v___x_1454_);
return v___x_1455_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = l_Lean_Expr_bvar___override(v___x_1462_);
return v___x_1463_;
}
}
static size_t _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7(void){
_start:
{
lean_object* v___x_1464_; size_t v___x_1465_; 
v___x_1464_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
v___x_1465_ = lean_ptr_addr(v___x_1464_);
return v___x_1465_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1469_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10));
v___x_1470_ = lean_unsigned_to_nat(18u);
v___x_1471_ = lean_unsigned_to_nat(1913u);
v___x_1472_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9));
v___x_1473_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8));
v___x_1474_ = l_mkPanicMessageWithDecl(v___x_1473_, v___x_1472_, v___x_1471_, v___x_1470_, v___x_1469_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(lean_object* v_lhs_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1484_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6));
v___x_1485_ = lean_unsigned_to_nat(4u);
v___x_1486_ = l_Lean_Expr_isAppOfArity(v_lhs_1478_, v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8));
v___x_1488_ = l_Lean_Expr_isAppOfArity(v_lhs_1478_, v___x_1487_, v___x_1485_);
if (v___x_1488_ == 0)
{
uint8_t v___x_1489_; 
v___x_1489_ = l_Lean_Expr_isApp(v_lhs_1478_);
if (v___x_1489_ == 0)
{
uint8_t v___x_1490_; 
v___x_1490_ = l_Lean_Expr_isProj(v_lhs_1478_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1491_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1);
v___x_1492_ = l_Lean_MessageData_ofExpr(v_lhs_1478_);
v___x_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1491_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_1493_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
return v___x_1494_;
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = l_Lean_Expr_projExpr_x21(v_lhs_1478_);
lean_inc(v_a_1482_);
lean_inc_ref(v_a_1481_);
lean_inc(v_a_1480_);
lean_inc_ref(v_a_1479_);
lean_inc_ref(v___x_1495_);
v___x_1496_ = lean_infer_type(v___x_1495_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; lean_object* v___y_1501_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3));
v___x_1499_ = 0;
if (lean_obj_tag(v_lhs_1478_) == 11)
{
lean_object* v_typeName_1511_; lean_object* v_idx_1512_; lean_object* v_struct_1513_; lean_object* v___x_1514_; size_t v___x_1515_; size_t v___x_1516_; uint8_t v___x_1517_; 
v_typeName_1511_ = lean_ctor_get(v_lhs_1478_, 0);
v_idx_1512_ = lean_ctor_get(v_lhs_1478_, 1);
v_struct_1513_ = lean_ctor_get(v_lhs_1478_, 2);
v___x_1514_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
v___x_1515_ = lean_ptr_addr(v_struct_1513_);
v___x_1516_ = lean_usize_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7);
v___x_1517_ = lean_usize_dec_eq(v___x_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; 
lean_inc(v_idx_1512_);
lean_inc(v_typeName_1511_);
lean_dec_ref_known(v_lhs_1478_, 3);
v___x_1518_ = l_Lean_Expr_proj___override(v_typeName_1511_, v_idx_1512_, v___x_1514_);
v___y_1501_ = v___x_1518_;
goto v___jp_1500_;
}
else
{
v___y_1501_ = v_lhs_1478_;
goto v___jp_1500_;
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec_ref(v_lhs_1478_);
v___x_1519_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
v___x_1520_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(v___x_1519_);
v___y_1501_ = v___x_1520_;
goto v___jp_1500_;
}
v___jp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = l_Lean_mkLambda(v___x_1498_, v___x_1499_, v_a_1497_, v___y_1501_);
v___x_1503_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1495_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v___x_1505_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5));
v___x_1506_ = lean_unsigned_to_nat(2u);
v___x_1507_ = lean_mk_empty_array_with_capacity(v___x_1506_);
v___x_1508_ = lean_array_push(v___x_1507_, v___x_1502_);
v___x_1509_ = lean_array_push(v___x_1508_, v_a_1504_);
v___x_1510_ = l_Lean_Meta_mkAppM(v___x_1505_, v___x_1509_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
return v___x_1510_;
}
else
{
lean_dec_ref(v___x_1502_);
return v___x_1503_;
}
}
}
else
{
lean_dec_ref(v___x_1495_);
lean_dec_ref(v_lhs_1478_);
return v___x_1496_;
}
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = l_Lean_Expr_appFn_x21(v_lhs_1478_);
v___x_1522_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1521_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13));
v___x_1525_ = l_Lean_Expr_appArg_x21(v_lhs_1478_);
lean_dec_ref(v_lhs_1478_);
v___x_1526_ = lean_unsigned_to_nat(2u);
v___x_1527_ = lean_mk_empty_array_with_capacity(v___x_1526_);
v___x_1528_ = lean_array_push(v___x_1527_, v_a_1523_);
v___x_1529_ = lean_array_push(v___x_1528_, v___x_1525_);
v___x_1530_ = l_Lean_Meta_mkAppM(v___x_1524_, v___x_1529_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
return v___x_1530_;
}
else
{
lean_dec_ref(v_lhs_1478_);
return v___x_1522_;
}
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_dummy_1535_; lean_object* v_nargs_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2));
v___x_1532_ = l_Lean_Expr_getAppFn(v_lhs_1478_);
v___x_1533_ = l_Lean_Expr_constLevels_x21(v___x_1532_);
lean_dec_ref(v___x_1532_);
v___x_1534_ = l_Lean_mkConst(v___x_1531_, v___x_1533_);
v_dummy_1535_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_1536_ = l_Lean_Expr_getAppNumArgs(v_lhs_1478_);
lean_inc(v_nargs_1536_);
v___x_1537_ = lean_mk_array(v_nargs_1536_, v_dummy_1535_);
v___x_1538_ = lean_unsigned_to_nat(1u);
v___x_1539_ = lean_nat_sub(v_nargs_1536_, v___x_1538_);
lean_dec(v_nargs_1536_);
v___x_1540_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_1478_, v___x_1537_, v___x_1539_);
v___x_1541_ = l_Lean_mkAppN(v___x_1534_, v___x_1540_);
lean_dec_ref(v___x_1540_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v_dummy_1547_; lean_object* v_nargs_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4));
v___x_1544_ = l_Lean_Expr_getAppFn(v_lhs_1478_);
v___x_1545_ = l_Lean_Expr_constLevels_x21(v___x_1544_);
lean_dec_ref(v___x_1544_);
v___x_1546_ = l_Lean_mkConst(v___x_1543_, v___x_1545_);
v_dummy_1547_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_1548_ = l_Lean_Expr_getAppNumArgs(v_lhs_1478_);
lean_inc(v_nargs_1548_);
v___x_1549_ = lean_mk_array(v_nargs_1548_, v_dummy_1547_);
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_sub(v_nargs_1548_, v___x_1550_);
lean_dec(v_nargs_1548_);
v___x_1552_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_1478_, v___x_1549_, v___x_1551_);
v___x_1553_ = l_Lean_mkAppN(v___x_1546_, v___x_1552_);
lean_dec_ref(v___x_1552_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
return v___x_1554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(lean_object* v_lhs_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v_lhs_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(lean_object* v_msg_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___f_1569_; lean_object* v___x_1515__overap_1570_; lean_object* v___x_1571_; 
v___f_1569_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0));
v___x_1515__overap_1570_ = lean_panic_fn_borrowed(v___f_1569_, v_msg_1563_);
lean_inc(v___y_1567_);
lean_inc_ref(v___y_1566_);
lean_inc(v___y_1565_);
lean_inc_ref(v___y_1564_);
v___x_1571_ = lean_apply_5(v___x_1515__overap_1570_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, lean_box(0));
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(lean_object* v_msg_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v_msg_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1579_, lean_object* v_x_1580_, lean_object* v_x_1581_, lean_object* v_x_1582_){
_start:
{
lean_object* v_ks_1583_; lean_object* v_vs_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1608_; 
v_ks_1583_ = lean_ctor_get(v_x_1579_, 0);
v_vs_1584_ = lean_ctor_get(v_x_1579_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_x_1579_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1586_ = v_x_1579_;
v_isShared_1587_ = v_isSharedCheck_1608_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_vs_1584_);
lean_inc(v_ks_1583_);
lean_dec(v_x_1579_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1608_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1588_ = lean_array_get_size(v_ks_1583_);
v___x_1589_ = lean_nat_dec_lt(v_x_1580_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
lean_dec(v_x_1580_);
v___x_1590_ = lean_array_push(v_ks_1583_, v_x_1581_);
v___x_1591_ = lean_array_push(v_vs_1584_, v_x_1582_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v___x_1591_);
lean_ctor_set(v___x_1586_, 0, v___x_1590_);
v___x_1593_ = v___x_1586_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
else
{
lean_object* v_k_x27_1595_; uint8_t v___x_1596_; 
v_k_x27_1595_ = lean_array_fget_borrowed(v_ks_1583_, v_x_1580_);
v___x_1596_ = l_Lean_instBEqMVarId_beq(v_x_1581_, v_k_x27_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1598_; 
if (v_isShared_1587_ == 0)
{
v___x_1598_ = v___x_1586_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_ks_1583_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_vs_1584_);
v___x_1598_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_unsigned_to_nat(1u);
v___x_1600_ = lean_nat_add(v_x_1580_, v___x_1599_);
lean_dec(v_x_1580_);
v_x_1579_ = v___x_1598_;
v_x_1580_ = v___x_1600_;
goto _start;
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1603_ = lean_array_fset(v_ks_1583_, v_x_1580_, v_x_1581_);
v___x_1604_ = lean_array_fset(v_vs_1584_, v_x_1580_, v_x_1582_);
lean_dec(v_x_1580_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v___x_1604_);
lean_ctor_set(v___x_1586_, 0, v___x_1603_);
v___x_1606_ = v___x_1586_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_1609_, lean_object* v_k_1610_, lean_object* v_v_1611_){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_1609_, v___x_1612_, v_k_1610_, v_v_1611_);
return v___x_1613_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1615_, size_t v_x_1616_, size_t v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_){
_start:
{
if (lean_obj_tag(v_x_1615_) == 0)
{
lean_object* v_es_1620_; size_t v___x_1621_; size_t v___x_1622_; lean_object* v_j_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_es_1620_ = lean_ctor_get(v_x_1615_, 0);
v___x_1621_ = ((size_t)31ULL);
v___x_1622_ = lean_usize_land(v_x_1616_, v___x_1621_);
v_j_1623_ = lean_usize_to_nat(v___x_1622_);
v___x_1624_ = lean_array_get_size(v_es_1620_);
v___x_1625_ = lean_nat_dec_lt(v_j_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_dec(v_j_1623_);
lean_dec(v_x_1619_);
lean_dec(v_x_1618_);
return v_x_1615_;
}
else
{
lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1664_; 
lean_inc_ref(v_es_1620_);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_x_1615_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v_x_1615_, 0);
lean_dec(v_unused_1665_);
v___x_1627_ = v_x_1615_;
v_isShared_1628_ = v_isSharedCheck_1664_;
goto v_resetjp_1626_;
}
else
{
lean_dec(v_x_1615_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1664_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_v_1629_; lean_object* v___x_1630_; lean_object* v_xs_x27_1631_; lean_object* v___y_1633_; 
v_v_1629_ = lean_array_fget(v_es_1620_, v_j_1623_);
v___x_1630_ = lean_box(0);
v_xs_x27_1631_ = lean_array_fset(v_es_1620_, v_j_1623_, v___x_1630_);
switch(lean_obj_tag(v_v_1629_))
{
case 0:
{
lean_object* v_key_1638_; lean_object* v_val_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1649_; 
v_key_1638_ = lean_ctor_get(v_v_1629_, 0);
v_val_1639_ = lean_ctor_get(v_v_1629_, 1);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_v_1629_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1641_ = v_v_1629_;
v_isShared_1642_ = v_isSharedCheck_1649_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_val_1639_);
lean_inc(v_key_1638_);
lean_dec(v_v_1629_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1649_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
uint8_t v___x_1643_; 
v___x_1643_ = l_Lean_instBEqMVarId_beq(v_x_1618_, v_key_1638_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_del_object(v___x_1641_);
v___x_1644_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1638_, v_val_1639_, v_x_1618_, v_x_1619_);
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
v___y_1633_ = v___x_1645_;
goto v___jp_1632_;
}
else
{
lean_object* v___x_1647_; 
lean_dec(v_val_1639_);
lean_dec(v_key_1638_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 1, v_x_1619_);
lean_ctor_set(v___x_1641_, 0, v_x_1618_);
v___x_1647_ = v___x_1641_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_x_1618_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_x_1619_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
v___y_1633_ = v___x_1647_;
goto v___jp_1632_;
}
}
}
}
case 1:
{
lean_object* v_node_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1662_; 
v_node_1650_ = lean_ctor_get(v_v_1629_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_v_1629_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1652_ = v_v_1629_;
v_isShared_1653_ = v_isSharedCheck_1662_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_node_1650_);
lean_dec(v_v_1629_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1662_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
size_t v___x_1654_; size_t v___x_1655_; size_t v___x_1656_; size_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1654_ = ((size_t)5ULL);
v___x_1655_ = lean_usize_shift_right(v_x_1616_, v___x_1654_);
v___x_1656_ = ((size_t)1ULL);
v___x_1657_ = lean_usize_add(v_x_1617_, v___x_1656_);
v___x_1658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_node_1650_, v___x_1655_, v___x_1657_, v_x_1618_, v_x_1619_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1658_);
v___x_1660_ = v___x_1652_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
v___y_1633_ = v___x_1660_;
goto v___jp_1632_;
}
}
}
default: 
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v_x_1618_);
lean_ctor_set(v___x_1663_, 1, v_x_1619_);
v___y_1633_ = v___x_1663_;
goto v___jp_1632_;
}
}
v___jp_1632_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = lean_array_fset(v_xs_x27_1631_, v_j_1623_, v___y_1633_);
lean_dec(v_j_1623_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1634_);
v___x_1636_ = v___x_1627_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
else
{
lean_object* v_ks_1666_; lean_object* v_vs_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1685_; 
v_ks_1666_ = lean_ctor_get(v_x_1615_, 0);
v_vs_1667_ = lean_ctor_get(v_x_1615_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_x_1615_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1669_ = v_x_1615_;
v_isShared_1670_ = v_isSharedCheck_1685_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_vs_1667_);
lean_inc(v_ks_1666_);
lean_dec(v_x_1615_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1685_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_ks_1666_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_vs_1667_);
v___x_1672_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v_newNode_1673_; size_t v___x_1674_; uint8_t v___x_1675_; 
v_newNode_1673_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v___x_1672_, v_x_1618_, v_x_1619_);
v___x_1674_ = ((size_t)7ULL);
v___x_1675_ = lean_usize_dec_le(v___x_1674_, v_x_1617_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1676_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1673_);
v___x_1677_ = lean_unsigned_to_nat(4u);
v___x_1678_ = lean_nat_dec_lt(v___x_1676_, v___x_1677_);
lean_dec(v___x_1676_);
if (v___x_1678_ == 0)
{
lean_object* v_ks_1679_; lean_object* v_vs_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_ks_1679_ = lean_ctor_get(v_newNode_1673_, 0);
lean_inc_ref(v_ks_1679_);
v_vs_1680_ = lean_ctor_get(v_newNode_1673_, 1);
lean_inc_ref(v_vs_1680_);
lean_dec_ref(v_newNode_1673_);
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_1683_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_1617_, v_ks_1679_, v_vs_1680_, v___x_1681_, v___x_1682_);
lean_dec_ref(v_vs_1680_);
lean_dec_ref(v_ks_1679_);
return v___x_1683_;
}
else
{
return v_newNode_1673_;
}
}
else
{
return v_newNode_1673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_1686_, lean_object* v_keys_1687_, lean_object* v_vals_1688_, lean_object* v_i_1689_, lean_object* v_entries_1690_){
_start:
{
lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = lean_array_get_size(v_keys_1687_);
v___x_1692_ = lean_nat_dec_lt(v_i_1689_, v___x_1691_);
if (v___x_1692_ == 0)
{
lean_dec(v_i_1689_);
return v_entries_1690_;
}
else
{
lean_object* v_k_1693_; lean_object* v_v_1694_; uint64_t v___x_1695_; size_t v_h_1696_; size_t v___x_1697_; lean_object* v___x_1698_; size_t v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; size_t v_h_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_k_1693_ = lean_array_fget_borrowed(v_keys_1687_, v_i_1689_);
v_v_1694_ = lean_array_fget_borrowed(v_vals_1688_, v_i_1689_);
v___x_1695_ = l_Lean_instHashableMVarId_hash(v_k_1693_);
v_h_1696_ = lean_uint64_to_usize(v___x_1695_);
v___x_1697_ = ((size_t)5ULL);
v___x_1698_ = lean_unsigned_to_nat(1u);
v___x_1699_ = ((size_t)1ULL);
v___x_1700_ = lean_usize_sub(v_depth_1686_, v___x_1699_);
v___x_1701_ = lean_usize_mul(v___x_1697_, v___x_1700_);
v_h_1702_ = lean_usize_shift_right(v_h_1696_, v___x_1701_);
v___x_1703_ = lean_nat_add(v_i_1689_, v___x_1698_);
lean_dec(v_i_1689_);
lean_inc(v_v_1694_);
lean_inc(v_k_1693_);
v___x_1704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_entries_1690_, v_h_1702_, v_depth_1686_, v_k_1693_, v_v_1694_);
v_i_1689_ = v___x_1703_;
v_entries_1690_ = v___x_1704_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_1706_, lean_object* v_keys_1707_, lean_object* v_vals_1708_, lean_object* v_i_1709_, lean_object* v_entries_1710_){
_start:
{
size_t v_depth_boxed_1711_; lean_object* v_res_1712_; 
v_depth_boxed_1711_ = lean_unbox_usize(v_depth_1706_);
lean_dec(v_depth_1706_);
v_res_1712_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_1711_, v_keys_1707_, v_vals_1708_, v_i_1709_, v_entries_1710_);
lean_dec_ref(v_vals_1708_);
lean_dec_ref(v_keys_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1713_, lean_object* v_x_1714_, lean_object* v_x_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_){
_start:
{
size_t v_x_2106__boxed_1718_; size_t v_x_2107__boxed_1719_; lean_object* v_res_1720_; 
v_x_2106__boxed_1718_ = lean_unbox_usize(v_x_1714_);
lean_dec(v_x_1714_);
v_x_2107__boxed_1719_ = lean_unbox_usize(v_x_1715_);
lean_dec(v_x_1715_);
v_res_1720_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1713_, v_x_2106__boxed_1718_, v_x_2107__boxed_1719_, v_x_1716_, v_x_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
uint64_t v___x_1724_; size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1724_ = l_Lean_instHashableMVarId_hash(v_x_1722_);
v___x_1725_ = lean_uint64_to_usize(v___x_1724_);
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1721_, v___x_1725_, v___x_1726_, v_x_1722_, v_x_1723_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(lean_object* v_mvarId_1728_, lean_object* v_val_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; lean_object* v_mctx_1733_; lean_object* v_cache_1734_; lean_object* v_zetaDeltaFVarIds_1735_; lean_object* v_postponed_1736_; lean_object* v_diag_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1767_; 
v___x_1732_ = lean_st_ref_take(v___y_1730_);
v_mctx_1733_ = lean_ctor_get(v___x_1732_, 0);
v_cache_1734_ = lean_ctor_get(v___x_1732_, 1);
v_zetaDeltaFVarIds_1735_ = lean_ctor_get(v___x_1732_, 2);
v_postponed_1736_ = lean_ctor_get(v___x_1732_, 3);
v_diag_1737_ = lean_ctor_get(v___x_1732_, 4);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1739_ = v___x_1732_;
v_isShared_1740_ = v_isSharedCheck_1767_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_diag_1737_);
lean_inc(v_postponed_1736_);
lean_inc(v_zetaDeltaFVarIds_1735_);
lean_inc(v_cache_1734_);
lean_inc(v_mctx_1733_);
lean_dec(v___x_1732_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1767_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_depth_1741_; lean_object* v_levelAssignDepth_1742_; lean_object* v_lmvarCounter_1743_; lean_object* v_mvarCounter_1744_; lean_object* v_lDecls_1745_; lean_object* v_decls_1746_; lean_object* v_userNames_1747_; lean_object* v_lAssignment_1748_; lean_object* v_eAssignment_1749_; lean_object* v_dAssignment_1750_; lean_object* v_instanceTypedMVars_1751_; lean_object* v_synthNormMemo_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1766_; 
v_depth_1741_ = lean_ctor_get(v_mctx_1733_, 0);
v_levelAssignDepth_1742_ = lean_ctor_get(v_mctx_1733_, 1);
v_lmvarCounter_1743_ = lean_ctor_get(v_mctx_1733_, 2);
v_mvarCounter_1744_ = lean_ctor_get(v_mctx_1733_, 3);
v_lDecls_1745_ = lean_ctor_get(v_mctx_1733_, 4);
v_decls_1746_ = lean_ctor_get(v_mctx_1733_, 5);
v_userNames_1747_ = lean_ctor_get(v_mctx_1733_, 6);
v_lAssignment_1748_ = lean_ctor_get(v_mctx_1733_, 7);
v_eAssignment_1749_ = lean_ctor_get(v_mctx_1733_, 8);
v_dAssignment_1750_ = lean_ctor_get(v_mctx_1733_, 9);
v_instanceTypedMVars_1751_ = lean_ctor_get(v_mctx_1733_, 10);
v_synthNormMemo_1752_ = lean_ctor_get(v_mctx_1733_, 11);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_mctx_1733_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1754_ = v_mctx_1733_;
v_isShared_1755_ = v_isSharedCheck_1766_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_synthNormMemo_1752_);
lean_inc(v_instanceTypedMVars_1751_);
lean_inc(v_dAssignment_1750_);
lean_inc(v_eAssignment_1749_);
lean_inc(v_lAssignment_1748_);
lean_inc(v_userNames_1747_);
lean_inc(v_decls_1746_);
lean_inc(v_lDecls_1745_);
lean_inc(v_mvarCounter_1744_);
lean_inc(v_lmvarCounter_1743_);
lean_inc(v_levelAssignDepth_1742_);
lean_inc(v_depth_1741_);
lean_dec(v_mctx_1733_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1766_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1756_ = lean_box(0);
v___x_1757_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_1749_, v_mvarId_1728_, v_val_1729_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 8, v___x_1757_);
v___x_1759_ = v___x_1754_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_depth_1741_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_levelAssignDepth_1742_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_lmvarCounter_1743_);
lean_ctor_set(v_reuseFailAlloc_1765_, 3, v_mvarCounter_1744_);
lean_ctor_set(v_reuseFailAlloc_1765_, 4, v_lDecls_1745_);
lean_ctor_set(v_reuseFailAlloc_1765_, 5, v_decls_1746_);
lean_ctor_set(v_reuseFailAlloc_1765_, 6, v_userNames_1747_);
lean_ctor_set(v_reuseFailAlloc_1765_, 7, v_lAssignment_1748_);
lean_ctor_set(v_reuseFailAlloc_1765_, 8, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1765_, 9, v_dAssignment_1750_);
lean_ctor_set(v_reuseFailAlloc_1765_, 10, v_instanceTypedMVars_1751_);
lean_ctor_set(v_reuseFailAlloc_1765_, 11, v_synthNormMemo_1752_);
v___x_1759_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1759_);
v___x_1761_ = v___x_1739_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_cache_1734_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_zetaDeltaFVarIds_1735_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_postponed_1736_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v_diag_1737_);
v___x_1761_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_st_ref_put(v___y_1730_, v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1756_);
return v___x_1763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object* v_mvarId_1768_, lean_object* v_val_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1768_, v_val_1769_, v___y_1770_);
lean_dec(v___y_1770_);
return v_res_1772_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1775_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1776_ = lean_unsigned_to_nat(41u);
v___x_1777_ = lean_unsigned_to_nat(113u);
v___x_1778_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_1779_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1780_ = l_mkPanicMessageWithDecl(v___x_1779_, v___x_1778_, v___x_1777_, v___x_1776_, v___x_1775_);
return v___x_1780_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1781_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1782_ = lean_unsigned_to_nat(51u);
v___x_1783_ = lean_unsigned_to_nat(115u);
v___x_1784_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_1785_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1786_ = l_mkPanicMessageWithDecl(v___x_1785_, v___x_1784_, v___x_1783_, v___x_1782_, v___x_1781_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object* v_mvarId_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
lean_inc(v_mvarId_1787_);
v___x_1793_ = l_Lean_MVarId_getType_x27(v_mvarId_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___x_1795_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_1796_ = lean_unsigned_to_nat(3u);
v___x_1797_ = l_Lean_Expr_isAppOfArity(v_a_1794_, v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec(v_a_1794_);
lean_dec(v_mvarId_1787_);
v___x_1798_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2);
v___x_1799_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_1798_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1800_ = l_Lean_Expr_appFn_x21(v_a_1794_);
v___x_1801_ = l_Lean_Expr_appArg_x21(v___x_1800_);
lean_dec_ref(v___x_1800_);
v___x_1802_ = l_Lean_Expr_appArg_x21(v_a_1794_);
lean_dec(v_a_1794_);
v___x_1803_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1801_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1805_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc_n(v_a_1804_, 2);
lean_dec_ref_known(v___x_1803_, 1);
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1790_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1788_);
v___x_1805_ = lean_infer_type(v_a_1804_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; uint8_t v___x_1807_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v___x_1807_ = l_Lean_Expr_isAppOfArity(v_a_1806_, v___x_1795_, v___x_1796_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v_a_1806_);
lean_dec(v_a_1804_);
lean_dec_ref(v___x_1802_);
lean_dec(v_mvarId_1787_);
v___x_1808_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
v___x_1809_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_1808_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = l_Lean_Expr_appArg_x21(v_a_1806_);
lean_dec(v_a_1806_);
v___x_1811_ = l_Lean_Meta_mkEq(v___x_1810_, v___x_1802_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1811_, 1);
v___x_1813_ = lean_box(0);
v___x_1814_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1812_, v___x_1813_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1816_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc_n(v_a_1815_, 2);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1816_ = l_Lean_Meta_mkEqTrans(v_a_1804_, v_a_1815_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___y_1788_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1826_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v___x_1816_, 1);
v___x_1818_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1787_, v_a_1817_, v___y_1789_);
lean_dec(v___y_1789_);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; 
v_unused_1827_ = lean_ctor_get(v___x_1818_, 0);
lean_dec(v_unused_1827_);
v___x_1820_ = v___x_1818_;
v_isShared_1821_ = v_isSharedCheck_1826_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v___x_1818_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1826_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = l_Lean_Expr_mvarId_x21(v_a_1815_);
lean_dec(v_a_1815_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1822_);
v___x_1824_ = v___x_1820_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_a_1815_);
lean_dec(v___y_1789_);
lean_dec(v_mvarId_1787_);
v_a_1828_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1816_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1816_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_a_1804_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v_mvarId_1787_);
v_a_1836_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1814_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1814_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_a_1804_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v_mvarId_1787_);
v_a_1844_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1811_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1811_);
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
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_a_1804_);
lean_dec_ref(v___x_1802_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v_mvarId_1787_);
v_a_1852_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1805_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1805_);
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
lean_dec_ref(v___x_1802_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v_mvarId_1787_);
v_a_1860_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1803_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1803_);
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
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v_mvarId_1787_);
v_a_1868_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1793_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1793_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object* v_mvarId_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object* v_mvarId_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___f_1889_; lean_object* v___x_1890_; 
lean_inc(v_mvarId_1883_);
v___f_1889_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1889_, 0, v_mvarId_1883_);
v___x_1890_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1883_, v___f_1889_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object* v_mvarId_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object* v_mvarId_1898_, lean_object* v_val_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1898_, v_val_1899_, v___y_1901_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object* v_mvarId_1906_, lean_object* v_val_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_1906_, v_val_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object* v_00_u03b2_1914_, lean_object* v_x_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_1915_, v_x_1916_, v_x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1919_, lean_object* v_x_1920_, size_t v_x_1921_, size_t v_x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1920_, v_x_1921_, v_x_1922_, v_x_1923_, v_x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_){
_start:
{
size_t v_x_2580__boxed_1932_; size_t v_x_2581__boxed_1933_; lean_object* v_res_1934_; 
v_x_2580__boxed_1932_ = lean_unbox_usize(v_x_1928_);
lean_dec(v_x_1928_);
v_x_2581__boxed_1933_ = lean_unbox_usize(v_x_1929_);
lean_dec(v_x_1929_);
v_res_1934_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_1926_, v_x_1927_, v_x_2580__boxed_1932_, v_x_2581__boxed_1933_, v_x_1930_, v_x_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1935_, lean_object* v_n_1936_, lean_object* v_k_1937_, lean_object* v_v_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1936_, v_k_1937_, v_v_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1940_, size_t v_depth_1941_, lean_object* v_keys_1942_, lean_object* v_vals_1943_, lean_object* v_heq_1944_, lean_object* v_i_1945_, lean_object* v_entries_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1941_, v_keys_1942_, v_vals_1943_, v_i_1945_, v_entries_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1948_, lean_object* v_depth_1949_, lean_object* v_keys_1950_, lean_object* v_vals_1951_, lean_object* v_heq_1952_, lean_object* v_i_1953_, lean_object* v_entries_1954_){
_start:
{
size_t v_depth_boxed_1955_; lean_object* v_res_1956_; 
v_depth_boxed_1955_ = lean_unbox_usize(v_depth_1949_);
lean_dec(v_depth_1949_);
v_res_1956_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1948_, v_depth_boxed_1955_, v_keys_1950_, v_vals_1951_, v_heq_1952_, v_i_1953_, v_entries_1954_);
lean_dec_ref(v_vals_1951_);
lean_dec_ref(v_keys_1950_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1957_, lean_object* v_x_1958_, lean_object* v_x_1959_, lean_object* v_x_1960_, lean_object* v_x_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1958_, v_x_1959_, v_x_1960_, v_x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0(lean_object* v_declNameNonRec_1963_, lean_object* v_numFixed_1964_, lean_object* v_x_1965_){
_start:
{
uint8_t v___x_1966_; 
v___x_1966_ = l_Lean_Expr_isAppOfArity(v_x_1965_, v_declNameNonRec_1963_, v_numFixed_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0___boxed(lean_object* v_declNameNonRec_1967_, lean_object* v_numFixed_1968_, lean_object* v_x_1969_){
_start:
{
uint8_t v_res_1970_; lean_object* v_r_1971_; 
v_res_1970_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0(v_declNameNonRec_1967_, v_numFixed_1968_, v_x_1969_);
lean_dec_ref(v_x_1969_);
lean_dec(v_declNameNonRec_1967_);
v_r_1971_ = lean_box(v_res_1970_);
return v_r_1971_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1973_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1974_ = lean_unsigned_to_nat(41u);
v___x_1975_ = lean_unsigned_to_nat(128u);
v___x_1976_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__0));
v___x_1977_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1978_ = l_mkPanicMessageWithDecl(v___x_1977_, v___x_1976_, v___x_1975_, v___x_1974_, v___x_1973_);
return v___x_1978_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1979_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1980_ = lean_unsigned_to_nat(51u);
v___x_1981_ = lean_unsigned_to_nat(134u);
v___x_1982_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__0));
v___x_1983_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1984_ = l_mkPanicMessageWithDecl(v___x_1983_, v___x_1982_, v___x_1981_, v___x_1980_, v___x_1979_);
return v___x_1984_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__5));
v___x_1990_ = l_Lean_stringToMessageData(v___x_1989_);
return v___x_1990_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__7));
v___x_1993_ = l_Lean_stringToMessageData(v___x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1(lean_object* v_mvarId_1994_, lean_object* v___f_1995_, lean_object* v_fixEq_1996_, lean_object* v_declNameNonRec_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; 
lean_inc(v_mvarId_1994_);
v___x_2003_ = l_Lean_MVarId_getType_x27(v_mvarId_1994_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_2006_ = lean_unsigned_to_nat(3u);
v___x_2007_ = l_Lean_Expr_isAppOfArity(v_a_2004_, v___x_2005_, v___x_2006_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec(v_a_2004_);
lean_dec(v_declNameNonRec_1997_);
lean_dec(v_fixEq_1996_);
lean_dec(v_mvarId_1994_);
v___x_2008_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1);
v___x_2009_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_2008_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = l_Lean_Expr_appFn_x21(v_a_2004_);
v___x_2011_ = l_Lean_Expr_appArg_x21(v___x_2010_);
lean_dec_ref(v___x_2010_);
v___x_2012_ = lean_find_expr(v___f_1995_, v___x_2011_);
if (lean_obj_tag(v___x_2012_) == 1)
{
lean_object* v_val_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec(v_declNameNonRec_1997_);
v_val_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc_n(v_val_2013_, 2);
lean_dec_ref_known(v___x_2012_, 1);
v___x_2014_ = l_Lean_Expr_appArg_x21(v_a_2004_);
lean_dec(v_a_2004_);
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1998_);
v___x_2015_ = lean_infer_type(v_val_2013_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = lean_box(0);
lean_inc(v_val_2013_);
v___x_2018_ = l_Lean_Meta_kabstract(v___x_2011_, v_val_2013_, v___x_2017_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v_dummy_2026_; lean_object* v_nargs_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2020_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3));
v___x_2021_ = 0;
v___x_2022_ = l_Lean_mkLambda(v___x_2020_, v___x_2021_, v_a_2016_, v_a_2019_);
v___x_2023_ = l_Lean_Expr_getAppFn(v_val_2013_);
v___x_2024_ = l_Lean_Expr_constLevels_x21(v___x_2023_);
lean_dec_ref(v___x_2023_);
v___x_2025_ = l_Lean_mkConst(v_fixEq_1996_, v___x_2024_);
v_dummy_2026_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_2027_ = l_Lean_Expr_getAppNumArgs(v_val_2013_);
lean_inc(v_nargs_2027_);
v___x_2028_ = lean_mk_array(v_nargs_2027_, v_dummy_2026_);
v___x_2029_ = lean_unsigned_to_nat(1u);
v___x_2030_ = lean_nat_sub(v_nargs_2027_, v___x_2029_);
lean_dec(v_nargs_2027_);
v___x_2031_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_2013_, v___x_2028_, v___x_2030_);
v___x_2032_ = l_Lean_mkAppN(v___x_2025_, v___x_2031_);
lean_dec_ref(v___x_2031_);
v___x_2033_ = l_Lean_Meta_mkCongrArg(v___x_2022_, v___x_2032_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc_n(v_a_2034_, 2);
lean_dec_ref_known(v___x_2033_, 1);
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1998_);
v___x_2035_ = lean_infer_type(v_a_2034_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; uint8_t v___x_2037_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v___x_2037_ = l_Lean_Expr_isAppOfArity(v_a_2036_, v___x_2005_, v___x_2006_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v_a_2036_);
lean_dec(v_a_2034_);
lean_dec_ref(v___x_2014_);
lean_dec(v_mvarId_1994_);
v___x_2038_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2);
v___x_2039_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_2038_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = l_Lean_Expr_appArg_x21(v_a_2036_);
lean_dec(v_a_2036_);
v___x_2041_ = l_Lean_Expr_headBeta(v___x_2040_);
v___x_2042_ = l_Lean_Meta_mkEq(v___x_2041_, v___x_2014_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = lean_box(0);
v___x_2045_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2043_, v___x_2044_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc_n(v_a_2046_, 2);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = l_Lean_Meta_mkEqTrans(v_a_2034_, v_a_2046_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec_ref(v___y_1998_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2057_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1994_, v_a_2048_, v___y_1999_);
lean_dec(v___y_1999_);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v___x_2049_, 0);
lean_dec(v_unused_2058_);
v___x_2051_ = v___x_2049_;
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
else
{
lean_dec(v___x_2049_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2053_ = l_Lean_Expr_mvarId_x21(v_a_2046_);
lean_dec(v_a_2046_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2053_);
v___x_2055_ = v___x_2051_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_a_2046_);
lean_dec(v___y_1999_);
lean_dec(v_mvarId_1994_);
v_a_2059_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2047_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2047_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_a_2034_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v_mvarId_1994_);
v_a_2067_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2045_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2045_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_2034_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v_mvarId_1994_);
v_a_2075_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2042_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2042_);
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
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_a_2034_);
lean_dec_ref(v___x_2014_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v_mvarId_1994_);
v_a_2083_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2035_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2035_);
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
lean_dec_ref(v___x_2014_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v_mvarId_1994_);
v_a_2091_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2033_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2033_);
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
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_a_2016_);
lean_dec_ref(v___x_2014_);
lean_dec(v_val_2013_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v_fixEq_1996_);
lean_dec(v_mvarId_1994_);
v_a_2099_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2018_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2018_);
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
lean_dec_ref(v___x_2014_);
lean_dec(v_val_2013_);
lean_dec_ref(v___x_2011_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v_fixEq_1996_);
lean_dec(v_mvarId_1994_);
v_a_2107_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2015_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2015_);
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
lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_dec(v___x_2012_);
lean_dec_ref(v___x_2011_);
lean_dec(v_a_2004_);
lean_dec(v_fixEq_1996_);
v___x_2115_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__4));
v___x_2116_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6);
v___x_2117_ = 0;
v___x_2118_ = l_Lean_MessageData_ofConstName(v_declNameNonRec_1997_, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2116_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8);
v___x_2121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
v___x_2123_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2115_, v_mvarId_1994_, v___x_2122_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v___x_2123_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v_declNameNonRec_1997_);
lean_dec(v_fixEq_1996_);
lean_dec(v_mvarId_1994_);
v_a_2124_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2003_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2003_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___boxed(lean_object* v_mvarId_2132_, lean_object* v___f_2133_, lean_object* v_fixEq_2134_, lean_object* v_declNameNonRec_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1(v_mvarId_2132_, v___f_2133_, v_fixEq_2134_, v_declNameNonRec_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
lean_dec_ref(v___f_2133_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(lean_object* v_declNameNonRec_2142_, lean_object* v_fixEq_2143_, lean_object* v_numFixed_2144_, lean_object* v_mvarId_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v___f_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; 
lean_inc(v_declNameNonRec_2142_);
v___f_2151_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2151_, 0, v_declNameNonRec_2142_);
lean_closure_set(v___f_2151_, 1, v_numFixed_2144_);
lean_inc(v_mvarId_2145_);
v___f_2152_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___boxed), 9, 4);
lean_closure_set(v___f_2152_, 0, v_mvarId_2145_);
lean_closure_set(v___f_2152_, 1, v___f_2151_);
lean_closure_set(v___f_2152_, 2, v_fixEq_2143_);
lean_closure_set(v___f_2152_, 3, v_declNameNonRec_2142_);
v___x_2153_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_2145_, v___f_2152_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___boxed(lean_object* v_declNameNonRec_2154_, lean_object* v_fixEq_2155_, lean_object* v_numFixed_2156_, lean_object* v_mvarId_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(v_declNameNonRec_2154_, v_fixEq_2155_, v_numFixed_2156_, v_mvarId_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(lean_object* v_e_2164_, lean_object* v___y_2165_){
_start:
{
uint8_t v___x_2167_; 
v___x_2167_ = l_Lean_Expr_hasMVar(v_e_2164_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v_e_2164_);
return v___x_2168_;
}
else
{
lean_object* v___x_2169_; lean_object* v_mctx_2170_; lean_object* v___x_2171_; lean_object* v_fst_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; lean_object* v_cache_2175_; lean_object* v_zetaDeltaFVarIds_2176_; lean_object* v_postponed_2177_; lean_object* v_diag_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2187_; 
v___x_2169_ = lean_st_ref_get(v___y_2165_);
v_mctx_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc_ref(v_mctx_2170_);
lean_dec(v___x_2169_);
v___x_2171_ = l_Lean_instantiateMVarsCore(v_mctx_2170_, v_e_2164_);
v_fst_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_fst_2172_);
v_snd_2173_ = lean_ctor_get(v___x_2171_, 1);
lean_inc(v_snd_2173_);
lean_dec_ref(v___x_2171_);
v___x_2174_ = lean_st_ref_take(v___y_2165_);
v_cache_2175_ = lean_ctor_get(v___x_2174_, 1);
v_zetaDeltaFVarIds_2176_ = lean_ctor_get(v___x_2174_, 2);
v_postponed_2177_ = lean_ctor_get(v___x_2174_, 3);
v_diag_2178_ = lean_ctor_get(v___x_2174_, 4);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v___x_2174_, 0);
lean_dec(v_unused_2188_);
v___x_2180_ = v___x_2174_;
v_isShared_2181_ = v_isSharedCheck_2187_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_diag_2178_);
lean_inc(v_postponed_2177_);
lean_inc(v_zetaDeltaFVarIds_2176_);
lean_inc(v_cache_2175_);
lean_dec(v___x_2174_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2187_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v_snd_2173_);
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_snd_2173_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_cache_2175_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_zetaDeltaFVarIds_2176_);
lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_postponed_2177_);
lean_ctor_set(v_reuseFailAlloc_2186_, 4, v_diag_2178_);
v___x_2183_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_st_ref_put(v___y_2165_, v___x_2183_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_fst_2172_);
return v___x_2185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg___boxed(lean_object* v_e_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_e_2189_, v___y_2190_);
lean_dec(v___y_2190_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object* v_e_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_e_2193_, v___y_2195_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___boxed(lean_object* v_e_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_e_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_2207_, lean_object* v_opt_2208_){
_start:
{
lean_object* v_name_2209_; lean_object* v_defValue_2210_; lean_object* v_map_2211_; lean_object* v___x_2212_; 
v_name_2209_ = lean_ctor_get(v_opt_2208_, 0);
v_defValue_2210_ = lean_ctor_get(v_opt_2208_, 1);
v_map_2211_ = lean_ctor_get(v_opts_2207_, 0);
v___x_2212_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2211_, v_name_2209_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_inc(v_defValue_2210_);
return v_defValue_2210_;
}
else
{
lean_object* v_val_2213_; 
v_val_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_val_2213_);
lean_dec_ref_known(v___x_2212_, 1);
if (lean_obj_tag(v_val_2213_) == 3)
{
lean_object* v_v_2214_; 
v_v_2214_ = lean_ctor_get(v_val_2213_, 0);
lean_inc(v_v_2214_);
lean_dec_ref_known(v_val_2213_, 1);
return v_v_2214_;
}
else
{
lean_dec(v_val_2213_);
lean_inc(v_defValue_2210_);
return v_defValue_2210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_2215_, lean_object* v_opt_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_2215_, v_opt_2216_);
lean_dec_ref(v_opt_2216_);
lean_dec_ref(v_opts_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(lean_object* v_k_2218_, uint8_t v_allowLevelAssignments_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2219_, v_k_2218_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_a_2234_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2225_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2225_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg___boxed(lean_object* v_k_2242_, lean_object* v_allowLevelAssignments_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2249_; lean_object* v_res_2250_; 
v_allowLevelAssignments_boxed_2249_ = lean_unbox(v_allowLevelAssignments_2243_);
v_res_2250_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_k_2242_, v_allowLevelAssignments_boxed_2249_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object* v_00_u03b1_2251_, lean_object* v_k_2252_, uint8_t v_allowLevelAssignments_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_k_2252_, v_allowLevelAssignments_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object* v_00_u03b1_2260_, lean_object* v_k_2261_, lean_object* v_allowLevelAssignments_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2268_; lean_object* v_res_2269_; 
v_allowLevelAssignments_boxed_2268_ = lean_unbox(v_allowLevelAssignments_2262_);
v_res_2269_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v_00_u03b1_2260_, v_k_2261_, v_allowLevelAssignments_boxed_2268_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object* v___x_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_toCold_2279_; lean_object* v_options_2280_; uint8_t v_hasTrace_2281_; 
v_toCold_2279_ = lean_ctor_get(v___y_2276_, 0);
v_options_2280_ = lean_ctor_get(v_toCold_2279_, 2);
v_hasTrace_2281_ = lean_ctor_get_uint8(v_options_2280_, sizeof(void*)*1);
if (v_hasTrace_2281_ == 0)
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
lean_dec(v___x_2273_);
v___x_2282_ = lean_box(v_hasTrace_2281_);
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
return v___x_2283_;
}
else
{
lean_object* v_inheritedTraceOptions_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v_inheritedTraceOptions_2284_ = lean_ctor_get(v_toCold_2279_, 11);
v___x_2285_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_2286_ = l_Lean_Name_append(v___x_2285_, v___x_2273_);
v___x_2287_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2284_, v_options_2280_, v___x_2286_);
lean_dec(v___x_2286_);
v___x_2288_ = lean_box(v___x_2287_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v___x_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(lean_object* v_o_2297_, lean_object* v_k_2298_, uint8_t v_v_2299_){
_start:
{
lean_object* v_map_2300_; uint8_t v_hasTrace_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2315_; 
v_map_2300_ = lean_ctor_get(v_o_2297_, 0);
v_hasTrace_2301_ = lean_ctor_get_uint8(v_o_2297_, sizeof(void*)*1);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_o_2297_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2303_ = v_o_2297_;
v_isShared_2304_ = v_isSharedCheck_2315_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_map_2300_);
lean_dec(v_o_2297_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2315_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2305_, 0, v_v_2299_);
lean_inc(v_k_2298_);
v___x_2306_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2298_, v___x_2305_, v_map_2300_);
if (v_hasTrace_2301_ == 0)
{
lean_object* v___x_2307_; uint8_t v___x_2308_; lean_object* v___x_2310_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_2308_ = l_Lean_Name_isPrefixOf(v___x_2307_, v_k_2298_);
lean_dec(v_k_2298_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2306_);
v___x_2310_ = v___x_2303_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2306_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*1, v___x_2308_);
return v___x_2310_;
}
}
else
{
lean_object* v___x_2313_; 
lean_dec(v_k_2298_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2306_);
v___x_2313_ = v___x_2303_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*1, v_hasTrace_2301_);
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
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3___boxed(lean_object* v_o_2316_, lean_object* v_k_2317_, lean_object* v_v_2318_){
_start:
{
uint8_t v_v_boxed_2319_; lean_object* v_res_2320_; 
v_v_boxed_2319_ = lean_unbox(v_v_2318_);
v_res_2320_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(v_o_2316_, v_k_2317_, v_v_boxed_2319_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_2321_, lean_object* v_opt_2322_, uint8_t v_val_2323_){
_start:
{
lean_object* v_name_2324_; lean_object* v___x_2325_; 
v_name_2324_ = lean_ctor_get(v_opt_2322_, 0);
lean_inc(v_name_2324_);
lean_dec_ref(v_opt_2322_);
v___x_2325_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(v_opts_2321_, v_name_2324_, v_val_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_2326_, lean_object* v_opt_2327_, lean_object* v_val_2328_){
_start:
{
uint8_t v_val_boxed_2329_; lean_object* v_res_2330_; 
v_val_boxed_2329_ = lean_unbox(v_val_2328_);
v_res_2330_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_2326_, v_opt_2327_, v_val_boxed_2329_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object* v_mvarId_2331_, uint8_t v___x_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___y_2339_; uint16_t v___y_2340_; lean_object* v_fileName_2341_; lean_object* v_fileMap_2342_; lean_object* v_currNamespace_2343_; lean_object* v_openDecls_2344_; lean_object* v_initHeartbeats_2345_; lean_object* v_maxHeartbeats_2346_; lean_object* v_quotContext_2347_; lean_object* v_currMacroScope_2348_; lean_object* v_cancelTk_x3f_2349_; lean_object* v_inheritedTraceOptions_2350_; lean_object* v_currRecDepth_2351_; lean_object* v_ref_2352_; uint8_t v_suppressElabErrors_2353_; uint8_t v_isRecordingDeps_2354_; lean_object* v___y_2355_; lean_object* v_toCold_2361_; lean_object* v_currRecDepth_2362_; lean_object* v_ref_2363_; uint8_t v_suppressElabErrors_2364_; uint8_t v_isRecordingDeps_2365_; lean_object* v_fileName_2366_; lean_object* v_fileMap_2367_; lean_object* v_options_2368_; lean_object* v_currNamespace_2369_; lean_object* v_openDecls_2370_; lean_object* v_initHeartbeats_2371_; lean_object* v_maxHeartbeats_2372_; lean_object* v_quotContext_2373_; lean_object* v_currMacroScope_2374_; lean_object* v_cancelTk_x3f_2375_; lean_object* v_inheritedTraceOptions_2376_; uint8_t v___y_2378_; lean_object* v___y_2379_; uint16_t v___y_2380_; lean_object* v___y_2403_; 
v_toCold_2361_ = lean_ctor_get(v___y_2335_, 0);
v_currRecDepth_2362_ = lean_ctor_get(v___y_2335_, 1);
v_ref_2363_ = lean_ctor_get(v___y_2335_, 2);
v_suppressElabErrors_2364_ = lean_ctor_get_uint8(v___y_2335_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2365_ = lean_ctor_get_uint8(v___y_2335_, sizeof(void*)*3 + 3);
v_fileName_2366_ = lean_ctor_get(v_toCold_2361_, 0);
v_fileMap_2367_ = lean_ctor_get(v_toCold_2361_, 1);
v_options_2368_ = lean_ctor_get(v_toCold_2361_, 2);
v_currNamespace_2369_ = lean_ctor_get(v_toCold_2361_, 4);
v_openDecls_2370_ = lean_ctor_get(v_toCold_2361_, 5);
v_initHeartbeats_2371_ = lean_ctor_get(v_toCold_2361_, 6);
v_maxHeartbeats_2372_ = lean_ctor_get(v_toCold_2361_, 7);
v_quotContext_2373_ = lean_ctor_get(v_toCold_2361_, 8);
v_currMacroScope_2374_ = lean_ctor_get(v_toCold_2361_, 9);
v_cancelTk_x3f_2375_ = lean_ctor_get(v_toCold_2361_, 10);
v_inheritedTraceOptions_2376_ = lean_ctor_get(v_toCold_2361_, 11);
if (v_isRecordingDeps_2365_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = l_Lean_Meta_smartUnfolding;
lean_inc_ref(v_options_2368_);
v___x_2414_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_options_2368_, v___x_2413_, v_isRecordingDeps_2365_);
v___y_2403_ = v___x_2414_;
goto v___jp_2402_;
}
else
{
lean_object* v___x_2415_; 
lean_inc_ref(v_options_2368_);
v___x_2415_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2368_);
v___y_2403_ = v___x_2415_;
goto v___jp_2402_;
}
v___jp_2338_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2356_ = l_Lean_maxRecDepth;
v___x_2357_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___y_2339_, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2358_, 0, v_fileName_2341_);
lean_ctor_set(v___x_2358_, 1, v_fileMap_2342_);
lean_ctor_set(v___x_2358_, 2, v___y_2339_);
lean_ctor_set(v___x_2358_, 3, v___x_2357_);
lean_ctor_set(v___x_2358_, 4, v_currNamespace_2343_);
lean_ctor_set(v___x_2358_, 5, v_openDecls_2344_);
lean_ctor_set(v___x_2358_, 6, v_initHeartbeats_2345_);
lean_ctor_set(v___x_2358_, 7, v_maxHeartbeats_2346_);
lean_ctor_set(v___x_2358_, 8, v_quotContext_2347_);
lean_ctor_set(v___x_2358_, 9, v_currMacroScope_2348_);
lean_ctor_set(v___x_2358_, 10, v_cancelTk_x3f_2349_);
lean_ctor_set(v___x_2358_, 11, v_inheritedTraceOptions_2350_);
lean_inc(v_ref_2352_);
lean_inc(v_currRecDepth_2351_);
v___x_2359_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v_currRecDepth_2351_);
lean_ctor_set(v___x_2359_, 2, v_ref_2352_);
lean_ctor_set_uint16(v___x_2359_, sizeof(void*)*3, v___y_2340_);
lean_ctor_set_uint8(v___x_2359_, sizeof(void*)*3 + 2, v_suppressElabErrors_2353_);
lean_ctor_set_uint8(v___x_2359_, sizeof(void*)*3 + 3, v_isRecordingDeps_2354_);
v___x_2360_ = l_Lean_MVarId_refl(v_mvarId_2331_, v___x_2332_, v___y_2333_, v___y_2334_, v___x_2359_, v___y_2355_);
lean_dec_ref_known(v___x_2359_, 3);
return v___x_2360_;
}
v___jp_2377_:
{
lean_object* v___x_2381_; lean_object* v_env_2382_; lean_object* v_nextMacroScope_2383_; lean_object* v_ngen_2384_; lean_object* v_auxDeclNGen_2385_; lean_object* v_traceState_2386_; lean_object* v_recordedDeps_2387_; lean_object* v_messages_2388_; lean_object* v_infoState_2389_; lean_object* v_snapshotTasks_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2400_; 
v___x_2381_ = lean_st_ref_take(v___y_2336_);
v_env_2382_ = lean_ctor_get(v___x_2381_, 0);
v_nextMacroScope_2383_ = lean_ctor_get(v___x_2381_, 1);
v_ngen_2384_ = lean_ctor_get(v___x_2381_, 2);
v_auxDeclNGen_2385_ = lean_ctor_get(v___x_2381_, 3);
v_traceState_2386_ = lean_ctor_get(v___x_2381_, 4);
v_recordedDeps_2387_ = lean_ctor_get(v___x_2381_, 6);
v_messages_2388_ = lean_ctor_get(v___x_2381_, 7);
v_infoState_2389_ = lean_ctor_get(v___x_2381_, 8);
v_snapshotTasks_2390_ = lean_ctor_get(v___x_2381_, 9);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2400_ == 0)
{
lean_object* v_unused_2401_; 
v_unused_2401_ = lean_ctor_get(v___x_2381_, 5);
lean_dec(v_unused_2401_);
v___x_2392_ = v___x_2381_;
v_isShared_2393_ = v_isSharedCheck_2400_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_snapshotTasks_2390_);
lean_inc(v_infoState_2389_);
lean_inc(v_messages_2388_);
lean_inc(v_recordedDeps_2387_);
lean_inc(v_traceState_2386_);
lean_inc(v_auxDeclNGen_2385_);
lean_inc(v_ngen_2384_);
lean_inc(v_nextMacroScope_2383_);
lean_inc(v_env_2382_);
lean_dec(v___x_2381_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2400_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2394_ = l_Lean_Kernel_enableDiag(v_env_2382_, v___y_2378_);
v___x_2395_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 5, v___x_2395_);
lean_ctor_set(v___x_2392_, 0, v___x_2394_);
v___x_2397_ = v___x_2392_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_nextMacroScope_2383_);
lean_ctor_set(v_reuseFailAlloc_2399_, 2, v_ngen_2384_);
lean_ctor_set(v_reuseFailAlloc_2399_, 3, v_auxDeclNGen_2385_);
lean_ctor_set(v_reuseFailAlloc_2399_, 4, v_traceState_2386_);
lean_ctor_set(v_reuseFailAlloc_2399_, 5, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2399_, 6, v_recordedDeps_2387_);
lean_ctor_set(v_reuseFailAlloc_2399_, 7, v_messages_2388_);
lean_ctor_set(v_reuseFailAlloc_2399_, 8, v_infoState_2389_);
lean_ctor_set(v_reuseFailAlloc_2399_, 9, v_snapshotTasks_2390_);
v___x_2397_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_st_ref_put(v___y_2336_, v___x_2397_);
lean_inc_ref(v_inheritedTraceOptions_2376_);
lean_inc(v_cancelTk_x3f_2375_);
lean_inc(v_currMacroScope_2374_);
lean_inc(v_quotContext_2373_);
lean_inc(v_maxHeartbeats_2372_);
lean_inc(v_initHeartbeats_2371_);
lean_inc(v_openDecls_2370_);
lean_inc(v_currNamespace_2369_);
lean_inc_ref(v_fileMap_2367_);
lean_inc_ref(v_fileName_2366_);
v___y_2339_ = v___y_2379_;
v___y_2340_ = v___y_2380_;
v_fileName_2341_ = v_fileName_2366_;
v_fileMap_2342_ = v_fileMap_2367_;
v_currNamespace_2343_ = v_currNamespace_2369_;
v_openDecls_2344_ = v_openDecls_2370_;
v_initHeartbeats_2345_ = v_initHeartbeats_2371_;
v_maxHeartbeats_2346_ = v_maxHeartbeats_2372_;
v_quotContext_2347_ = v_quotContext_2373_;
v_currMacroScope_2348_ = v_currMacroScope_2374_;
v_cancelTk_x3f_2349_ = v_cancelTk_x3f_2375_;
v_inheritedTraceOptions_2350_ = v_inheritedTraceOptions_2376_;
v_currRecDepth_2351_ = v_currRecDepth_2362_;
v_ref_2352_ = v_ref_2363_;
v_suppressElabErrors_2353_ = v_suppressElabErrors_2364_;
v_isRecordingDeps_2354_ = v_isRecordingDeps_2365_;
v___y_2355_ = v___y_2336_;
goto v___jp_2338_;
}
}
}
v___jp_2402_:
{
uint16_t v___x_2404_; lean_object* v___x_2405_; lean_object* v_env_2406_; uint8_t v___x_2407_; uint16_t v___x_2408_; uint16_t v___x_2409_; uint16_t v___x_2410_; uint8_t v___x_2411_; 
v___x_2404_ = l_Lean_OptionFlags_ofOptions(v___y_2403_);
v___x_2405_ = lean_st_ref_get(v___y_2336_);
v_env_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc_ref(v_env_2406_);
lean_dec(v___x_2405_);
v___x_2407_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2406_);
lean_dec_ref(v_env_2406_);
v___x_2408_ = 512;
v___x_2409_ = lean_uint16_land(v___x_2404_, v___x_2408_);
v___x_2410_ = 0;
v___x_2411_ = lean_uint16_dec_eq(v___x_2409_, v___x_2410_);
if (v___x_2411_ == 0)
{
if (v___x_2407_ == 0)
{
v___y_2378_ = v___x_2332_;
v___y_2379_ = v___y_2403_;
v___y_2380_ = v___x_2404_;
goto v___jp_2377_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2376_);
lean_inc(v_cancelTk_x3f_2375_);
lean_inc(v_currMacroScope_2374_);
lean_inc(v_quotContext_2373_);
lean_inc(v_maxHeartbeats_2372_);
lean_inc(v_initHeartbeats_2371_);
lean_inc(v_openDecls_2370_);
lean_inc(v_currNamespace_2369_);
lean_inc_ref(v_fileMap_2367_);
lean_inc_ref(v_fileName_2366_);
v___y_2339_ = v___y_2403_;
v___y_2340_ = v___x_2404_;
v_fileName_2341_ = v_fileName_2366_;
v_fileMap_2342_ = v_fileMap_2367_;
v_currNamespace_2343_ = v_currNamespace_2369_;
v_openDecls_2344_ = v_openDecls_2370_;
v_initHeartbeats_2345_ = v_initHeartbeats_2371_;
v_maxHeartbeats_2346_ = v_maxHeartbeats_2372_;
v_quotContext_2347_ = v_quotContext_2373_;
v_currMacroScope_2348_ = v_currMacroScope_2374_;
v_cancelTk_x3f_2349_ = v_cancelTk_x3f_2375_;
v_inheritedTraceOptions_2350_ = v_inheritedTraceOptions_2376_;
v_currRecDepth_2351_ = v_currRecDepth_2362_;
v_ref_2352_ = v_ref_2363_;
v_suppressElabErrors_2353_ = v_suppressElabErrors_2364_;
v_isRecordingDeps_2354_ = v_isRecordingDeps_2365_;
v___y_2355_ = v___y_2336_;
goto v___jp_2338_;
}
}
else
{
if (v___x_2407_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2376_);
lean_inc(v_cancelTk_x3f_2375_);
lean_inc(v_currMacroScope_2374_);
lean_inc(v_quotContext_2373_);
lean_inc(v_maxHeartbeats_2372_);
lean_inc(v_initHeartbeats_2371_);
lean_inc(v_openDecls_2370_);
lean_inc(v_currNamespace_2369_);
lean_inc_ref(v_fileMap_2367_);
lean_inc_ref(v_fileName_2366_);
v___y_2339_ = v___y_2403_;
v___y_2340_ = v___x_2404_;
v_fileName_2341_ = v_fileName_2366_;
v_fileMap_2342_ = v_fileMap_2367_;
v_currNamespace_2343_ = v_currNamespace_2369_;
v_openDecls_2344_ = v_openDecls_2370_;
v_initHeartbeats_2345_ = v_initHeartbeats_2371_;
v_maxHeartbeats_2346_ = v_maxHeartbeats_2372_;
v_quotContext_2347_ = v_quotContext_2373_;
v_currMacroScope_2348_ = v_currMacroScope_2374_;
v_cancelTk_x3f_2349_ = v_cancelTk_x3f_2375_;
v_inheritedTraceOptions_2350_ = v_inheritedTraceOptions_2376_;
v_currRecDepth_2351_ = v_currRecDepth_2362_;
v_ref_2352_ = v_ref_2363_;
v_suppressElabErrors_2353_ = v_suppressElabErrors_2364_;
v_isRecordingDeps_2354_ = v_isRecordingDeps_2365_;
v___y_2355_ = v___y_2336_;
goto v___jp_2338_;
}
else
{
uint8_t v___x_2412_; 
v___x_2412_ = 0;
v___y_2378_ = v___x_2412_;
v___y_2379_ = v___y_2403_;
v___y_2380_ = v___x_2404_;
goto v___jp_2377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object* v_mvarId_2416_, lean_object* v___x_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
uint8_t v___x_10246__boxed_2423_; lean_object* v_res_2424_; 
v___x_10246__boxed_2423_ = lean_unbox(v___x_2417_);
v_res_2424_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_mvarId_2416_, v___x_10246__boxed_2423_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
return v_res_2424_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2425_; double v___x_2426_; 
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_float_of_nat(v___x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object* v_cls_2430_, lean_object* v_msg_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_ref_2437_; lean_object* v___x_2438_; lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2484_; 
v_ref_2437_ = lean_ctor_get(v___y_2434_, 2);
v___x_2438_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msg_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2441_ = v___x_2438_;
v_isShared_2442_ = v_isSharedCheck_2484_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2438_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2484_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v_traceState_2444_; lean_object* v_env_2445_; lean_object* v_nextMacroScope_2446_; lean_object* v_ngen_2447_; lean_object* v_auxDeclNGen_2448_; lean_object* v_cache_2449_; lean_object* v_recordedDeps_2450_; lean_object* v_messages_2451_; lean_object* v_infoState_2452_; lean_object* v_snapshotTasks_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2483_; 
v___x_2443_ = lean_st_ref_take(v___y_2435_);
v_traceState_2444_ = lean_ctor_get(v___x_2443_, 4);
v_env_2445_ = lean_ctor_get(v___x_2443_, 0);
v_nextMacroScope_2446_ = lean_ctor_get(v___x_2443_, 1);
v_ngen_2447_ = lean_ctor_get(v___x_2443_, 2);
v_auxDeclNGen_2448_ = lean_ctor_get(v___x_2443_, 3);
v_cache_2449_ = lean_ctor_get(v___x_2443_, 5);
v_recordedDeps_2450_ = lean_ctor_get(v___x_2443_, 6);
v_messages_2451_ = lean_ctor_get(v___x_2443_, 7);
v_infoState_2452_ = lean_ctor_get(v___x_2443_, 8);
v_snapshotTasks_2453_ = lean_ctor_get(v___x_2443_, 9);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2455_ = v___x_2443_;
v_isShared_2456_ = v_isSharedCheck_2483_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_snapshotTasks_2453_);
lean_inc(v_infoState_2452_);
lean_inc(v_messages_2451_);
lean_inc(v_recordedDeps_2450_);
lean_inc(v_cache_2449_);
lean_inc(v_traceState_2444_);
lean_inc(v_auxDeclNGen_2448_);
lean_inc(v_ngen_2447_);
lean_inc(v_nextMacroScope_2446_);
lean_inc(v_env_2445_);
lean_dec(v___x_2443_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2483_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
uint64_t v_tid_2457_; lean_object* v_traces_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2482_; 
v_tid_2457_ = lean_ctor_get_uint64(v_traceState_2444_, sizeof(void*)*1);
v_traces_2458_ = lean_ctor_get(v_traceState_2444_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_traceState_2444_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2460_ = v_traceState_2444_;
v_isShared_2461_ = v_isSharedCheck_2482_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_traces_2458_);
lean_dec(v_traceState_2444_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2482_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; double v___x_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2462_ = lean_box(0);
v___x_2463_ = lean_box(0);
v___x_2464_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0);
v___x_2465_ = 0;
v___x_2466_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__1));
v___x_2467_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2467_, 0, v_cls_2430_);
lean_ctor_set(v___x_2467_, 1, v___x_2463_);
lean_ctor_set(v___x_2467_, 2, v___x_2466_);
lean_ctor_set_float(v___x_2467_, sizeof(void*)*3, v___x_2464_);
lean_ctor_set_float(v___x_2467_, sizeof(void*)*3 + 8, v___x_2464_);
lean_ctor_set_uint8(v___x_2467_, sizeof(void*)*3 + 16, v___x_2465_);
v___x_2468_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__2));
v___x_2469_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v_a_2439_);
lean_ctor_set(v___x_2469_, 2, v___x_2468_);
lean_inc(v_ref_2437_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_ref_2437_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = l_Lean_PersistentArray_push___redArg(v_traces_2458_, v___x_2470_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2471_);
v___x_2473_ = v___x_2460_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2471_);
lean_ctor_set_uint64(v_reuseFailAlloc_2481_, sizeof(void*)*1, v_tid_2457_);
v___x_2473_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2475_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 4, v___x_2473_);
v___x_2475_ = v___x_2455_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_env_2445_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_nextMacroScope_2446_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_ngen_2447_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_auxDeclNGen_2448_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2480_, 5, v_cache_2449_);
lean_ctor_set(v_reuseFailAlloc_2480_, 6, v_recordedDeps_2450_);
lean_ctor_set(v_reuseFailAlloc_2480_, 7, v_messages_2451_);
lean_ctor_set(v_reuseFailAlloc_2480_, 8, v_infoState_2452_);
lean_ctor_set(v_reuseFailAlloc_2480_, 9, v_snapshotTasks_2453_);
v___x_2475_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2476_ = lean_st_ref_put(v___y_2435_, v___x_2475_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2462_);
v___x_2478_ = v___x_2441_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2462_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_cls_2485_, lean_object* v_msg_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_cls_2485_, v_msg_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
return v_res_2492_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0));
v___x_2495_ = l_Lean_stringToMessageData(v___x_2494_);
return v___x_2495_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2));
v___x_2498_ = l_Lean_stringToMessageData(v___x_2497_);
return v___x_2498_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4));
v___x_2501_ = l_Lean_stringToMessageData(v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object* v_a_2502_, lean_object* v___x_2503_, lean_object* v___f_2504_, lean_object* v_fixEq_x3f_2505_, lean_object* v_declName_2506_, lean_object* v___x_2507_, lean_object* v___x_2508_, lean_object* v_fixedParamPerms_2509_, lean_object* v_declNameNonRec_2510_, lean_object* v_____r_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v_mvarId_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; 
if (lean_obj_tag(v_fixEq_x3f_2505_) == 1)
{
lean_object* v_val_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2661_; 
v_val_2606_ = lean_ctor_get(v_fixEq_x3f_2505_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_fixEq_x3f_2505_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2608_ = v_fixEq_x3f_2505_;
v_isShared_2609_ = v_isSharedCheck_2661_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_val_2606_);
lean_dec(v_fixEq_x3f_2505_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2661_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; 
v___x_2610_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_2506_, v___x_2507_, v___x_2508_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___x_2628_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
lean_inc_ref(v___f_2504_);
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
lean_inc(v___y_2513_);
lean_inc_ref(v___y_2512_);
v___x_2628_ = lean_apply_5(v___f_2504_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, lean_box(0));
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; uint8_t v___x_2630_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
v___x_2630_ = lean_unbox(v_a_2629_);
lean_dec(v_a_2629_);
if (v___x_2630_ == 0)
{
lean_del_object(v___x_2608_);
v___y_2613_ = v___y_2512_;
v___y_2614_ = v___y_2513_;
v___y_2615_ = v___y_2514_;
v___y_2616_ = v___y_2515_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2631_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5);
lean_inc(v_a_2611_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v_a_2611_);
v___x_2633_ = v___x_2608_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2611_);
v___x_2633_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2631_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
lean_inc(v___x_2503_);
v___x_2635_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2503_, v___x_2634_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_dec_ref_known(v___x_2635_, 1);
v___y_2613_ = v___y_2512_;
v___y_2614_ = v___y_2513_;
v___y_2615_ = v___y_2514_;
v___y_2616_ = v___y_2515_;
goto v___jp_2612_;
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec(v_a_2611_);
lean_dec(v_val_2606_);
lean_dec(v_declNameNonRec_2510_);
lean_dec_ref(v_fixedParamPerms_2509_);
lean_dec_ref(v___f_2504_);
lean_dec(v___x_2503_);
lean_dec_ref(v_a_2502_);
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec(v_declNameNonRec_2510_);
lean_dec_ref(v_fixedParamPerms_2509_);
lean_dec_ref(v___f_2504_);
lean_dec(v___x_2503_);
lean_dec_ref(v_a_2502_);
v_a_2645_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2628_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2628_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
v___jp_2612_:
{
lean_object* v_numFixed_2617_; lean_object* v___x_2618_; 
v_numFixed_2617_ = lean_ctor_get(v_fixedParamPerms_2509_, 0);
lean_inc(v_numFixed_2617_);
lean_dec_ref(v_fixedParamPerms_2509_);
v___x_2618_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(v_declNameNonRec_2510_, v_val_2606_, v_numFixed_2617_, v_a_2611_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v_mvarId_2578_ = v_a_2619_;
v___y_2579_ = v___y_2613_;
v___y_2580_ = v___y_2614_;
v___y_2581_ = v___y_2615_;
v___y_2582_ = v___y_2616_;
goto v___jp_2577_;
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref(v___f_2504_);
lean_dec(v___x_2503_);
lean_dec_ref(v_a_2502_);
v_a_2620_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2618_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2618_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec(v_declNameNonRec_2510_);
lean_dec_ref(v_fixedParamPerms_2509_);
lean_dec_ref(v___f_2504_);
lean_dec(v___x_2503_);
lean_dec_ref(v_a_2502_);
v_a_2653_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2610_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2610_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
else
{
lean_object* v___x_2662_; 
lean_dec_ref(v_fixedParamPerms_2509_);
lean_dec(v___x_2507_);
lean_dec(v_fixEq_x3f_2505_);
v___x_2662_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_2506_, v_declNameNonRec_2510_, v___x_2508_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___x_2679_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
lean_inc_ref(v___f_2504_);
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
lean_inc(v___y_2513_);
lean_inc_ref(v___y_2512_);
v___x_2679_ = lean_apply_5(v___f_2504_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, lean_box(0));
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; uint8_t v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2681_ = lean_unbox(v_a_2680_);
lean_dec(v_a_2680_);
if (v___x_2681_ == 0)
{
v___y_2665_ = v___y_2512_;
v___y_2666_ = v___y_2513_;
v___y_2667_ = v___y_2514_;
v___y_2668_ = v___y_2515_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2682_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5);
lean_inc(v_a_2663_);
v___x_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_a_2663_);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
lean_inc(v___x_2503_);
v___x_2685_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2503_, v___x_2684_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_dec_ref_known(v___x_2685_, 1);
v___y_2665_ = v___y_2512_;
v___y_2666_ = v___y_2513_;
v___y_2667_ = v___y_2514_;
v___y_2668_ = v___y_2515_;
goto v___jp_2664_;
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v_a_2663_);
lean_dec_ref(v___f_2504_);
lean_dec(v___x_2503_);
lean_dec_ref(v_a_2502_);
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v_a_2663_);
lean_dec_ref(v___f_2504_);
lean_dec(v___x_2503_);
lean_dec_ref(v_a_2502_);
v_a_2694_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2679_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2679_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
v___jp_2664_:
{
lean_object* v___x_2669_; 
v___x_2669_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_a_2663_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v_mvarId_2578_ = v_a_2670_;
v___y_2579_ = v___y_2665_;
v___y_2580_ = v___y_2666_;
v___y_2581_ = v___y_2667_;
v___y_2582_ = v___y_2668_;
goto v___jp_2577_;
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v___f_2504_);
lean_dec(v___x_2503_);
lean_dec_ref(v_a_2502_);
v_a_2671_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2669_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2669_);
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
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v___f_2504_);
lean_dec(v___x_2503_);
lean_dec_ref(v_a_2502_);
v_a_2702_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2662_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2662_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
v___jp_2517_:
{
if (lean_obj_tag(v___y_2522_) == 0)
{
lean_object* v_toCold_2523_; lean_object* v_options_2524_; uint8_t v_hasTrace_2525_; 
lean_dec_ref_known(v___y_2522_, 1);
v_toCold_2523_ = lean_ctor_get(v___y_2521_, 0);
v_options_2524_ = lean_ctor_get(v_toCold_2523_, 2);
v_hasTrace_2525_ = lean_ctor_get_uint8(v_options_2524_, sizeof(void*)*1);
if (v_hasTrace_2525_ == 0)
{
lean_object* v___x_2526_; 
lean_dec(v___x_2503_);
v___x_2526_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2502_, v___y_2519_);
return v___x_2526_;
}
else
{
lean_object* v_inheritedTraceOptions_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v_inheritedTraceOptions_2527_ = lean_ctor_get(v_toCold_2523_, 11);
v___x_2528_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
lean_inc(v___x_2503_);
v___x_2529_ = l_Lean_Name_append(v___x_2528_, v___x_2503_);
v___x_2530_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2527_, v_options_2524_, v___x_2529_);
lean_dec(v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
lean_dec(v___x_2503_);
v___x_2531_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2502_, v___y_2519_);
return v___x_2531_;
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1);
v___x_2533_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2503_, v___x_2532_, v___y_2518_, v___y_2519_, v___y_2521_, v___y_2520_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v___x_2534_; 
lean_dec_ref_known(v___x_2533_, 1);
v___x_2534_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2502_, v___y_2519_);
return v___x_2534_;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v_a_2502_);
v_a_2535_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2533_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2533_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec(v___x_2503_);
lean_dec_ref(v_a_2502_);
v_a_2543_ = lean_ctor_get(v___y_2522_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___y_2522_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___y_2522_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___y_2522_);
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
v___jp_2551_:
{
lean_object* v___x_2557_; uint8_t v_transparency_2558_; uint8_t v___x_2559_; uint8_t v___x_2560_; uint8_t v___x_2561_; 
v___x_2557_ = l_Lean_Meta_Context_config(v___y_2555_);
v_transparency_2558_ = lean_ctor_get_uint8(v___x_2557_, 9);
lean_dec_ref(v___x_2557_);
v___x_2559_ = 0;
v___x_2560_ = 1;
v___x_2561_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2558_, v___x_2559_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v___y_2552_, v___x_2560_, v___y_2555_, v___y_2556_, v___y_2554_, v___y_2553_);
v___y_2518_ = v___y_2555_;
v___y_2519_ = v___y_2556_;
v___y_2520_ = v___y_2553_;
v___y_2521_ = v___y_2554_;
v___y_2522_ = v___x_2562_;
goto v___jp_2517_;
}
else
{
lean_object* v_keyedConfig_2563_; uint8_t v_trackZetaDelta_2564_; lean_object* v_zetaDeltaSet_2565_; lean_object* v_lctx_2566_; lean_object* v_localInstances_2567_; lean_object* v_defEqCtx_x3f_2568_; lean_object* v_synthPendingDepth_2569_; lean_object* v_customCanUnfoldPredicate_x3f_2570_; uint8_t v_univApprox_2571_; uint8_t v_inTypeClassResolution_2572_; uint8_t v_cacheInferType_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_keyedConfig_2563_ = lean_ctor_get(v___y_2555_, 0);
v_trackZetaDelta_2564_ = lean_ctor_get_uint8(v___y_2555_, sizeof(void*)*7);
v_zetaDeltaSet_2565_ = lean_ctor_get(v___y_2555_, 1);
v_lctx_2566_ = lean_ctor_get(v___y_2555_, 2);
v_localInstances_2567_ = lean_ctor_get(v___y_2555_, 3);
v_defEqCtx_x3f_2568_ = lean_ctor_get(v___y_2555_, 4);
v_synthPendingDepth_2569_ = lean_ctor_get(v___y_2555_, 5);
v_customCanUnfoldPredicate_x3f_2570_ = lean_ctor_get(v___y_2555_, 6);
v_univApprox_2571_ = lean_ctor_get_uint8(v___y_2555_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2572_ = lean_ctor_get_uint8(v___y_2555_, sizeof(void*)*7 + 2);
v_cacheInferType_2573_ = lean_ctor_get_uint8(v___y_2555_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2563_);
v___x_2574_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2559_, v_keyedConfig_2563_);
lean_inc(v_customCanUnfoldPredicate_x3f_2570_);
lean_inc(v_synthPendingDepth_2569_);
lean_inc(v_defEqCtx_x3f_2568_);
lean_inc_ref(v_localInstances_2567_);
lean_inc_ref(v_lctx_2566_);
lean_inc(v_zetaDeltaSet_2565_);
v___x_2575_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v_zetaDeltaSet_2565_);
lean_ctor_set(v___x_2575_, 2, v_lctx_2566_);
lean_ctor_set(v___x_2575_, 3, v_localInstances_2567_);
lean_ctor_set(v___x_2575_, 4, v_defEqCtx_x3f_2568_);
lean_ctor_set(v___x_2575_, 5, v_synthPendingDepth_2569_);
lean_ctor_set(v___x_2575_, 6, v_customCanUnfoldPredicate_x3f_2570_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*7, v_trackZetaDelta_2564_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*7 + 1, v_univApprox_2571_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2572_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*7 + 3, v_cacheInferType_2573_);
v___x_2576_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v___y_2552_, v___x_2560_, v___x_2575_, v___y_2556_, v___y_2554_, v___y_2553_);
lean_dec_ref_known(v___x_2575_, 7);
v___y_2518_ = v___y_2555_;
v___y_2519_ = v___y_2556_;
v___y_2520_ = v___y_2553_;
v___y_2521_ = v___y_2554_;
v___y_2522_ = v___x_2576_;
goto v___jp_2517_;
}
}
v___jp_2577_:
{
lean_object* v___x_2583_; 
lean_inc(v___y_2582_);
lean_inc_ref(v___y_2581_);
lean_inc(v___y_2580_);
lean_inc_ref(v___y_2579_);
v___x_2583_ = lean_apply_5(v___f_2504_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, lean_box(0));
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; uint8_t v___x_2585_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v___x_2585_ = lean_unbox(v_a_2584_);
lean_dec(v_a_2584_);
if (v___x_2585_ == 0)
{
v___y_2552_ = v_mvarId_2578_;
v___y_2553_ = v___y_2582_;
v___y_2554_ = v___y_2581_;
v___y_2555_ = v___y_2579_;
v___y_2556_ = v___y_2580_;
goto v___jp_2551_;
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2586_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3);
lean_inc(v_mvarId_2578_);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_mvarId_2578_);
v___x_2588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
lean_inc(v___x_2503_);
v___x_2589_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2503_, v___x_2588_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_dec_ref_known(v___x_2589_, 1);
v___y_2552_ = v_mvarId_2578_;
v___y_2553_ = v___y_2582_;
v___y_2554_ = v___y_2581_;
v___y_2555_ = v___y_2579_;
v___y_2556_ = v___y_2580_;
goto v___jp_2551_;
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_mvarId_2578_);
lean_dec(v___x_2503_);
lean_dec_ref(v_a_2502_);
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v_mvarId_2578_);
lean_dec(v___x_2503_);
lean_dec_ref(v_a_2502_);
v_a_2598_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2583_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2583_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object* v_a_2710_, lean_object* v___x_2711_, lean_object* v___f_2712_, lean_object* v_fixEq_x3f_2713_, lean_object* v_declName_2714_, lean_object* v___x_2715_, lean_object* v___x_2716_, lean_object* v_fixedParamPerms_2717_, lean_object* v_declNameNonRec_2718_, lean_object* v_____r_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2710_, v___x_2711_, v___f_2712_, v_fixEq_x3f_2713_, v_declName_2714_, v___x_2715_, v___x_2716_, v_fixedParamPerms_2717_, v_declNameNonRec_2718_, v_____r_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
return v_res_2725_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__0));
v___x_2728_ = l_Lean_stringToMessageData(v___x_2727_);
return v___x_2728_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__2));
v___x_2731_ = l_Lean_stringToMessageData(v___x_2730_);
return v___x_2731_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9(void){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__8));
v___x_2742_ = l_Lean_stringToMessageData(v___x_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(lean_object* v_declName_2743_, lean_object* v_a_2744_, lean_object* v___x_2745_, lean_object* v_fixEq_x3f_2746_, lean_object* v_fixedParamPerms_2747_, lean_object* v_declNameNonRec_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___y_2755_; lean_object* v___y_2756_; uint8_t v___y_2757_; lean_object* v___y_2767_; lean_object* v_a_2768_; lean_object* v___y_2772_; lean_object* v___x_2774_; 
lean_inc(v___x_2745_);
v___x_2774_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2744_, v___x_2745_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___f_2778_; lean_object* v___x_2779_; lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2803_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
v___x_2776_ = l_Lean_Expr_mvarId_x21(v_a_2775_);
v___x_2777_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6));
v___f_2778_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__7));
v___x_2779_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_2777_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2803_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2803_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
uint8_t v___x_2784_; 
v___x_2784_ = lean_unbox(v_a_2780_);
lean_dec(v_a_2780_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_del_object(v___x_2782_);
v___x_2785_ = lean_box(0);
lean_inc(v_declName_2743_);
v___x_2786_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2775_, v___x_2777_, v___f_2778_, v_fixEq_x3f_2746_, v_declName_2743_, v___x_2745_, v___x_2776_, v_fixedParamPerms_2747_, v_declNameNonRec_2748_, v___x_2785_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
v___y_2772_ = v___x_2786_;
goto v___jp_2771_;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2787_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9);
lean_inc(v___x_2776_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 1);
lean_ctor_set(v___x_2782_, 0, v___x_2776_);
v___x_2789_ = v___x_2782_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2776_);
v___x_2789_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2787_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2777_, v___x_2790_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
lean_inc(v_declName_2743_);
v___x_2793_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2775_, v___x_2777_, v___f_2778_, v_fixEq_x3f_2746_, v_declName_2743_, v___x_2745_, v___x_2776_, v_fixedParamPerms_2747_, v_declNameNonRec_2748_, v_a_2792_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
v___y_2772_ = v___x_2793_;
goto v___jp_2771_;
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec(v___x_2776_);
lean_dec(v_a_2775_);
lean_dec(v_declNameNonRec_2748_);
lean_dec_ref(v_fixedParamPerms_2747_);
lean_dec(v_fixEq_x3f_2746_);
lean_dec(v___x_2745_);
v_a_2794_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2791_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2791_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
lean_inc(v_a_2794_);
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
v___y_2767_ = v___x_2799_;
v_a_2768_ = v_a_2794_;
goto v___jp_2766_;
}
}
}
}
}
}
}
else
{
lean_dec(v_declNameNonRec_2748_);
lean_dec_ref(v_fixedParamPerms_2747_);
lean_dec(v_fixEq_x3f_2746_);
lean_dec(v___x_2745_);
v___y_2772_ = v___x_2774_;
goto v___jp_2771_;
}
v___jp_2754_:
{
if (v___y_2757_ == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_dec_ref(v___y_2755_);
v___x_2758_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1);
v___x_2759_ = l_Lean_MessageData_ofConstName(v_declName_2743_, v___y_2757_);
v___x_2760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3);
v___x_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = l_Lean_Exception_toMessageData(v___y_2756_);
v___x_2764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_2764_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
return v___x_2765_;
}
else
{
lean_dec_ref(v___y_2756_);
lean_dec(v_declName_2743_);
return v___y_2755_;
}
}
v___jp_2766_:
{
uint8_t v___x_2769_; 
v___x_2769_ = l_Lean_Exception_isInterrupt(v_a_2768_);
if (v___x_2769_ == 0)
{
uint8_t v___x_2770_; 
lean_inc_ref(v_a_2768_);
v___x_2770_ = l_Lean_Exception_isRuntime(v_a_2768_);
v___y_2755_ = v___y_2767_;
v___y_2756_ = v_a_2768_;
v___y_2757_ = v___x_2770_;
goto v___jp_2754_;
}
else
{
v___y_2755_ = v___y_2767_;
v___y_2756_ = v_a_2768_;
v___y_2757_ = v___x_2769_;
goto v___jp_2754_;
}
}
v___jp_2771_:
{
if (lean_obj_tag(v___y_2772_) == 0)
{
lean_dec(v_declName_2743_);
return v___y_2772_;
}
else
{
lean_object* v_a_2773_; 
v_a_2773_ = lean_ctor_get(v___y_2772_, 0);
lean_inc(v_a_2773_);
v___y_2767_ = v___y_2772_;
v_a_2768_ = v_a_2773_;
goto v___jp_2766_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed(lean_object* v_declName_2804_, lean_object* v_a_2805_, lean_object* v___x_2806_, lean_object* v_fixEq_x3f_2807_, lean_object* v_fixedParamPerms_2808_, lean_object* v_declNameNonRec_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(v_declName_2804_, v_a_2805_, v___x_2806_, v_fixEq_x3f_2807_, v_fixedParamPerms_2808_, v_declNameNonRec_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4(lean_object* v_levelParams_2816_, lean_object* v_declName_2817_, lean_object* v_fixEq_x3f_2818_, lean_object* v_fixedParamPerms_2819_, lean_object* v_declNameNonRec_2820_, lean_object* v_name_2821_, lean_object* v_xs_2822_, lean_object* v_body_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; lean_object* v_us_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2829_ = lean_box(0);
lean_inc(v_levelParams_2816_);
v_us_2830_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(v_levelParams_2816_, v___x_2829_);
lean_inc(v_declName_2817_);
v___x_2831_ = l_Lean_mkConst(v_declName_2817_, v_us_2830_);
v___x_2832_ = l_Lean_mkAppN(v___x_2831_, v_xs_2822_);
v___x_2833_ = l_Lean_Meta_mkEq(v___x_2832_, v_body_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2835_; lean_object* v___f_2836_; uint8_t v___x_2837_; lean_object* v___x_2838_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc_n(v_a_2834_, 2);
lean_dec_ref_known(v___x_2833_, 1);
v___x_2835_ = lean_box(0);
v___f_2836_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed), 11, 6);
lean_closure_set(v___f_2836_, 0, v_declName_2817_);
lean_closure_set(v___f_2836_, 1, v_a_2834_);
lean_closure_set(v___f_2836_, 2, v___x_2835_);
lean_closure_set(v___f_2836_, 3, v_fixEq_x3f_2818_);
lean_closure_set(v___f_2836_, 4, v_fixedParamPerms_2819_);
lean_closure_set(v___f_2836_, 5, v_declNameNonRec_2820_);
v___x_2837_ = 0;
v___x_2838_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v___f_2836_, v___x_2837_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; uint8_t v___x_2840_; uint8_t v___x_2841_; lean_object* v___x_2842_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = 1;
v___x_2841_ = 1;
v___x_2842_ = l_Lean_Meta_mkForallFVars(v_xs_2822_, v_a_2834_, v___x_2837_, v___x_2840_, v___x_2840_, v___x_2841_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v___x_2842_, 1);
v___x_2844_ = l_Lean_Meta_letToHave(v_a_2843_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = l_Lean_Meta_mkLambdaFVars(v_xs_2822_, v_a_2839_, v___x_2837_, v___x_2840_, v___x_2837_, v___x_2840_, v___x_2841_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v_a_2852_; lean_object* v___x_2853_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
lean_inc(v_name_2821_);
v___x_2848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2848_, 0, v_name_2821_);
lean_ctor_set(v___x_2848_, 1, v_levelParams_2816_);
lean_ctor_set(v___x_2848_, 2, v_a_2845_);
v___x_2849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2849_, 0, v_name_2821_);
lean_ctor_set(v___x_2849_, 1, v___x_2829_);
v___x_2850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2848_);
lean_ctor_set(v___x_2850_, 1, v_a_2847_);
lean_ctor_set(v___x_2850_, 2, v___x_2849_);
v___x_2851_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v___x_2850_, v___y_2827_);
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v___x_2851_);
v___x_2853_ = l_Lean_addDecl(v_a_2852_, v___x_2837_, v___y_2826_, v___y_2827_);
return v___x_2853_;
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v_a_2845_);
lean_dec(v_name_2821_);
lean_dec(v_levelParams_2816_);
v_a_2854_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2846_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2846_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v_a_2839_);
lean_dec(v_name_2821_);
lean_dec(v_levelParams_2816_);
v_a_2862_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2844_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2844_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v_a_2839_);
lean_dec(v_name_2821_);
lean_dec(v_levelParams_2816_);
v_a_2870_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2842_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2842_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec(v_a_2834_);
lean_dec(v_name_2821_);
lean_dec(v_levelParams_2816_);
v_a_2878_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2838_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2838_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec(v_name_2821_);
lean_dec(v_declNameNonRec_2820_);
lean_dec_ref(v_fixedParamPerms_2819_);
lean_dec(v_fixEq_x3f_2818_);
lean_dec(v_declName_2817_);
lean_dec(v_levelParams_2816_);
v_a_2886_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2833_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2833_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4___boxed(lean_object* v_levelParams_2894_, lean_object* v_declName_2895_, lean_object* v_fixEq_x3f_2896_, lean_object* v_fixedParamPerms_2897_, lean_object* v_declNameNonRec_2898_, lean_object* v_name_2899_, lean_object* v_xs_2900_, lean_object* v_body_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4(v_levelParams_2894_, v_declName_2895_, v_fixEq_x3f_2896_, v_fixedParamPerms_2897_, v_declNameNonRec_2898_, v_name_2899_, v_xs_2900_, v_body_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec_ref(v_xs_2900_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object* v_declName_2908_, lean_object* v_info_2909_, lean_object* v_name_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_toCold_2916_; lean_object* v_levelParams_2917_; lean_object* v_value_2918_; lean_object* v_declNameNonRec_2919_; lean_object* v_fixedParamPerms_2920_; lean_object* v_fixEq_x3f_2921_; lean_object* v_currRecDepth_2922_; lean_object* v_ref_2923_; uint8_t v_suppressElabErrors_2924_; uint8_t v_isRecordingDeps_2925_; lean_object* v_fileName_2926_; lean_object* v_fileMap_2927_; lean_object* v_options_2928_; lean_object* v_currNamespace_2929_; lean_object* v_openDecls_2930_; lean_object* v_initHeartbeats_2931_; lean_object* v_maxHeartbeats_2932_; lean_object* v_quotContext_2933_; lean_object* v_currMacroScope_2934_; lean_object* v_cancelTk_x3f_2935_; lean_object* v_inheritedTraceOptions_2936_; lean_object* v___f_2937_; uint8_t v___x_2938_; uint16_t v___y_2940_; lean_object* v___y_2941_; lean_object* v_fileName_2942_; lean_object* v_fileMap_2943_; lean_object* v_currNamespace_2944_; lean_object* v_openDecls_2945_; lean_object* v_initHeartbeats_2946_; lean_object* v_maxHeartbeats_2947_; lean_object* v_quotContext_2948_; lean_object* v_currMacroScope_2949_; lean_object* v_cancelTk_x3f_2950_; lean_object* v_inheritedTraceOptions_2951_; lean_object* v_currRecDepth_2952_; lean_object* v_ref_2953_; uint8_t v_suppressElabErrors_2954_; uint8_t v_isRecordingDeps_2955_; lean_object* v___y_2956_; uint16_t v___y_2963_; uint8_t v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2988_; 
v_toCold_2916_ = lean_ctor_get(v_a_2913_, 0);
v_levelParams_2917_ = lean_ctor_get(v_info_2909_, 1);
lean_inc(v_levelParams_2917_);
v_value_2918_ = lean_ctor_get(v_info_2909_, 3);
lean_inc_ref(v_value_2918_);
v_declNameNonRec_2919_ = lean_ctor_get(v_info_2909_, 5);
lean_inc(v_declNameNonRec_2919_);
v_fixedParamPerms_2920_ = lean_ctor_get(v_info_2909_, 6);
lean_inc_ref(v_fixedParamPerms_2920_);
v_fixEq_x3f_2921_ = lean_ctor_get(v_info_2909_, 8);
lean_inc(v_fixEq_x3f_2921_);
lean_dec_ref(v_info_2909_);
v_currRecDepth_2922_ = lean_ctor_get(v_a_2913_, 1);
v_ref_2923_ = lean_ctor_get(v_a_2913_, 2);
v_suppressElabErrors_2924_ = lean_ctor_get_uint8(v_a_2913_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2925_ = lean_ctor_get_uint8(v_a_2913_, sizeof(void*)*3 + 3);
v_fileName_2926_ = lean_ctor_get(v_toCold_2916_, 0);
v_fileMap_2927_ = lean_ctor_get(v_toCold_2916_, 1);
v_options_2928_ = lean_ctor_get(v_toCold_2916_, 2);
v_currNamespace_2929_ = lean_ctor_get(v_toCold_2916_, 4);
v_openDecls_2930_ = lean_ctor_get(v_toCold_2916_, 5);
v_initHeartbeats_2931_ = lean_ctor_get(v_toCold_2916_, 6);
v_maxHeartbeats_2932_ = lean_ctor_get(v_toCold_2916_, 7);
v_quotContext_2933_ = lean_ctor_get(v_toCold_2916_, 8);
v_currMacroScope_2934_ = lean_ctor_get(v_toCold_2916_, 9);
v_cancelTk_x3f_2935_ = lean_ctor_get(v_toCold_2916_, 10);
v_inheritedTraceOptions_2936_ = lean_ctor_get(v_toCold_2916_, 11);
v___f_2937_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4___boxed), 13, 6);
lean_closure_set(v___f_2937_, 0, v_levelParams_2917_);
lean_closure_set(v___f_2937_, 1, v_declName_2908_);
lean_closure_set(v___f_2937_, 2, v_fixEq_x3f_2921_);
lean_closure_set(v___f_2937_, 3, v_fixedParamPerms_2920_);
lean_closure_set(v___f_2937_, 4, v_declNameNonRec_2919_);
lean_closure_set(v___f_2937_, 5, v_name_2910_);
v___x_2938_ = 0;
if (v_isRecordingDeps_2925_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_2928_);
v___x_2999_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_options_2928_, v___x_2998_, v_isRecordingDeps_2925_);
v___y_2988_ = v___x_2999_;
goto v___jp_2987_;
}
else
{
lean_object* v___x_3000_; 
lean_inc_ref(v_options_2928_);
v___x_3000_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2928_);
v___y_2988_ = v___x_3000_;
goto v___jp_2987_;
}
v___jp_2939_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2957_ = l_Lean_maxRecDepth;
v___x_2958_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___y_2941_, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2959_, 0, v_fileName_2942_);
lean_ctor_set(v___x_2959_, 1, v_fileMap_2943_);
lean_ctor_set(v___x_2959_, 2, v___y_2941_);
lean_ctor_set(v___x_2959_, 3, v___x_2958_);
lean_ctor_set(v___x_2959_, 4, v_currNamespace_2944_);
lean_ctor_set(v___x_2959_, 5, v_openDecls_2945_);
lean_ctor_set(v___x_2959_, 6, v_initHeartbeats_2946_);
lean_ctor_set(v___x_2959_, 7, v_maxHeartbeats_2947_);
lean_ctor_set(v___x_2959_, 8, v_quotContext_2948_);
lean_ctor_set(v___x_2959_, 9, v_currMacroScope_2949_);
lean_ctor_set(v___x_2959_, 10, v_cancelTk_x3f_2950_);
lean_ctor_set(v___x_2959_, 11, v_inheritedTraceOptions_2951_);
lean_inc(v_ref_2953_);
lean_inc(v_currRecDepth_2952_);
v___x_2960_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v_currRecDepth_2952_);
lean_ctor_set(v___x_2960_, 2, v_ref_2953_);
lean_ctor_set_uint16(v___x_2960_, sizeof(void*)*3, v___y_2940_);
lean_ctor_set_uint8(v___x_2960_, sizeof(void*)*3 + 2, v_suppressElabErrors_2954_);
lean_ctor_set_uint8(v___x_2960_, sizeof(void*)*3 + 3, v_isRecordingDeps_2955_);
v___x_2961_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_2918_, v___f_2937_, v___x_2938_, v_a_2911_, v_a_2912_, v___x_2960_, v___y_2956_);
lean_dec_ref_known(v___x_2960_, 3);
return v___x_2961_;
}
v___jp_2962_:
{
lean_object* v___x_2966_; lean_object* v_env_2967_; lean_object* v_nextMacroScope_2968_; lean_object* v_ngen_2969_; lean_object* v_auxDeclNGen_2970_; lean_object* v_traceState_2971_; lean_object* v_recordedDeps_2972_; lean_object* v_messages_2973_; lean_object* v_infoState_2974_; lean_object* v_snapshotTasks_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2985_; 
v___x_2966_ = lean_st_ref_take(v_a_2914_);
v_env_2967_ = lean_ctor_get(v___x_2966_, 0);
v_nextMacroScope_2968_ = lean_ctor_get(v___x_2966_, 1);
v_ngen_2969_ = lean_ctor_get(v___x_2966_, 2);
v_auxDeclNGen_2970_ = lean_ctor_get(v___x_2966_, 3);
v_traceState_2971_ = lean_ctor_get(v___x_2966_, 4);
v_recordedDeps_2972_ = lean_ctor_get(v___x_2966_, 6);
v_messages_2973_ = lean_ctor_get(v___x_2966_, 7);
v_infoState_2974_ = lean_ctor_get(v___x_2966_, 8);
v_snapshotTasks_2975_ = lean_ctor_get(v___x_2966_, 9);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; 
v_unused_2986_ = lean_ctor_get(v___x_2966_, 5);
lean_dec(v_unused_2986_);
v___x_2977_ = v___x_2966_;
v_isShared_2978_ = v_isSharedCheck_2985_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_snapshotTasks_2975_);
lean_inc(v_infoState_2974_);
lean_inc(v_messages_2973_);
lean_inc(v_recordedDeps_2972_);
lean_inc(v_traceState_2971_);
lean_inc(v_auxDeclNGen_2970_);
lean_inc(v_ngen_2969_);
lean_inc(v_nextMacroScope_2968_);
lean_inc(v_env_2967_);
lean_dec(v___x_2966_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2985_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2979_ = l_Lean_Kernel_enableDiag(v_env_2967_, v___y_2964_);
v___x_2980_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 5, v___x_2980_);
lean_ctor_set(v___x_2977_, 0, v___x_2979_);
v___x_2982_ = v___x_2977_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_nextMacroScope_2968_);
lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_ngen_2969_);
lean_ctor_set(v_reuseFailAlloc_2984_, 3, v_auxDeclNGen_2970_);
lean_ctor_set(v_reuseFailAlloc_2984_, 4, v_traceState_2971_);
lean_ctor_set(v_reuseFailAlloc_2984_, 5, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_2984_, 6, v_recordedDeps_2972_);
lean_ctor_set(v_reuseFailAlloc_2984_, 7, v_messages_2973_);
lean_ctor_set(v_reuseFailAlloc_2984_, 8, v_infoState_2974_);
lean_ctor_set(v_reuseFailAlloc_2984_, 9, v_snapshotTasks_2975_);
v___x_2982_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; 
v___x_2983_ = lean_st_ref_put(v_a_2914_, v___x_2982_);
lean_inc_ref(v_inheritedTraceOptions_2936_);
lean_inc(v_cancelTk_x3f_2935_);
lean_inc(v_currMacroScope_2934_);
lean_inc(v_quotContext_2933_);
lean_inc(v_maxHeartbeats_2932_);
lean_inc(v_initHeartbeats_2931_);
lean_inc(v_openDecls_2930_);
lean_inc(v_currNamespace_2929_);
lean_inc_ref(v_fileMap_2927_);
lean_inc_ref(v_fileName_2926_);
v___y_2940_ = v___y_2963_;
v___y_2941_ = v___y_2965_;
v_fileName_2942_ = v_fileName_2926_;
v_fileMap_2943_ = v_fileMap_2927_;
v_currNamespace_2944_ = v_currNamespace_2929_;
v_openDecls_2945_ = v_openDecls_2930_;
v_initHeartbeats_2946_ = v_initHeartbeats_2931_;
v_maxHeartbeats_2947_ = v_maxHeartbeats_2932_;
v_quotContext_2948_ = v_quotContext_2933_;
v_currMacroScope_2949_ = v_currMacroScope_2934_;
v_cancelTk_x3f_2950_ = v_cancelTk_x3f_2935_;
v_inheritedTraceOptions_2951_ = v_inheritedTraceOptions_2936_;
v_currRecDepth_2952_ = v_currRecDepth_2922_;
v_ref_2953_ = v_ref_2923_;
v_suppressElabErrors_2954_ = v_suppressElabErrors_2924_;
v_isRecordingDeps_2955_ = v_isRecordingDeps_2925_;
v___y_2956_ = v_a_2914_;
goto v___jp_2939_;
}
}
}
v___jp_2987_:
{
uint16_t v___x_2989_; lean_object* v___x_2990_; lean_object* v_env_2991_; uint8_t v___x_2992_; uint16_t v___x_2993_; uint16_t v___x_2994_; uint16_t v___x_2995_; uint8_t v___x_2996_; 
v___x_2989_ = l_Lean_OptionFlags_ofOptions(v___y_2988_);
v___x_2990_ = lean_st_ref_get(v_a_2914_);
v_env_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc_ref(v_env_2991_);
lean_dec(v___x_2990_);
v___x_2992_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2991_);
lean_dec_ref(v_env_2991_);
v___x_2993_ = 512;
v___x_2994_ = lean_uint16_land(v___x_2989_, v___x_2993_);
v___x_2995_ = 0;
v___x_2996_ = lean_uint16_dec_eq(v___x_2994_, v___x_2995_);
if (v___x_2996_ == 0)
{
if (v___x_2992_ == 0)
{
uint8_t v___x_2997_; 
v___x_2997_ = 1;
v___y_2963_ = v___x_2989_;
v___y_2964_ = v___x_2997_;
v___y_2965_ = v___y_2988_;
goto v___jp_2962_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2936_);
lean_inc(v_cancelTk_x3f_2935_);
lean_inc(v_currMacroScope_2934_);
lean_inc(v_quotContext_2933_);
lean_inc(v_maxHeartbeats_2932_);
lean_inc(v_initHeartbeats_2931_);
lean_inc(v_openDecls_2930_);
lean_inc(v_currNamespace_2929_);
lean_inc_ref(v_fileMap_2927_);
lean_inc_ref(v_fileName_2926_);
v___y_2940_ = v___x_2989_;
v___y_2941_ = v___y_2988_;
v_fileName_2942_ = v_fileName_2926_;
v_fileMap_2943_ = v_fileMap_2927_;
v_currNamespace_2944_ = v_currNamespace_2929_;
v_openDecls_2945_ = v_openDecls_2930_;
v_initHeartbeats_2946_ = v_initHeartbeats_2931_;
v_maxHeartbeats_2947_ = v_maxHeartbeats_2932_;
v_quotContext_2948_ = v_quotContext_2933_;
v_currMacroScope_2949_ = v_currMacroScope_2934_;
v_cancelTk_x3f_2950_ = v_cancelTk_x3f_2935_;
v_inheritedTraceOptions_2951_ = v_inheritedTraceOptions_2936_;
v_currRecDepth_2952_ = v_currRecDepth_2922_;
v_ref_2953_ = v_ref_2923_;
v_suppressElabErrors_2954_ = v_suppressElabErrors_2924_;
v_isRecordingDeps_2955_ = v_isRecordingDeps_2925_;
v___y_2956_ = v_a_2914_;
goto v___jp_2939_;
}
}
else
{
if (v___x_2992_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2936_);
lean_inc(v_cancelTk_x3f_2935_);
lean_inc(v_currMacroScope_2934_);
lean_inc(v_quotContext_2933_);
lean_inc(v_maxHeartbeats_2932_);
lean_inc(v_initHeartbeats_2931_);
lean_inc(v_openDecls_2930_);
lean_inc(v_currNamespace_2929_);
lean_inc_ref(v_fileMap_2927_);
lean_inc_ref(v_fileName_2926_);
v___y_2940_ = v___x_2989_;
v___y_2941_ = v___y_2988_;
v_fileName_2942_ = v_fileName_2926_;
v_fileMap_2943_ = v_fileMap_2927_;
v_currNamespace_2944_ = v_currNamespace_2929_;
v_openDecls_2945_ = v_openDecls_2930_;
v_initHeartbeats_2946_ = v_initHeartbeats_2931_;
v_maxHeartbeats_2947_ = v_maxHeartbeats_2932_;
v_quotContext_2948_ = v_quotContext_2933_;
v_currMacroScope_2949_ = v_currMacroScope_2934_;
v_cancelTk_x3f_2950_ = v_cancelTk_x3f_2935_;
v_inheritedTraceOptions_2951_ = v_inheritedTraceOptions_2936_;
v_currRecDepth_2952_ = v_currRecDepth_2922_;
v_ref_2953_ = v_ref_2923_;
v_suppressElabErrors_2954_ = v_suppressElabErrors_2924_;
v_isRecordingDeps_2955_ = v_isRecordingDeps_2925_;
v___y_2956_ = v_a_2914_;
goto v___jp_2939_;
}
else
{
v___y_2963_ = v___x_2989_;
v___y_2964_ = v___x_2938_;
v___y_2965_ = v___y_2988_;
goto v___jp_2962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3001_, lean_object* v_info_3002_, lean_object* v_name_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_3001_, v_info_3002_, v_name_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec(v_a_3005_);
lean_dec_ref(v_a_3004_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* v_declName_3010_, lean_object* v_info_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v___x_3017_; lean_object* v_env_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3017_ = lean_st_ref_get(v_a_3015_);
v_env_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc_ref(v_env_3018_);
lean_dec(v___x_3017_);
v___x_3019_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc_n(v_declName_3010_, 2);
v___x_3020_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3018_, v_declName_3010_, v___x_3019_);
lean_inc_n(v___x_3020_, 2);
v___x_3021_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3021_, 0, v_declName_3010_);
lean_closure_set(v___x_3021_, 1, v_info_3011_);
lean_closure_set(v___x_3021_, 2, v___x_3020_);
v___x_3022_ = l_Lean_Meta_realizeConst(v_declName_3010_, v___x_3020_, v___x_3021_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3029_ == 0)
{
lean_object* v_unused_3030_; 
v_unused_3030_ = lean_ctor_get(v___x_3022_, 0);
lean_dec(v_unused_3030_);
v___x_3024_ = v___x_3022_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_dec(v___x_3022_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3020_);
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3020_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec(v___x_3020_);
v_a_3031_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3022_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3022_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object* v_declName_3039_, lean_object* v_info_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_3039_, v_info_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* v_declName_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v_env_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v_env_3059_; uint8_t v___x_3060_; uint8_t v___x_3061_; 
v___x_3053_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
v___x_3054_ = lean_st_ref_get(v_a_3051_);
v_env_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc_ref(v_env_3055_);
lean_dec(v___x_3054_);
v___x_3056_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3047_);
v___x_3057_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3055_, v_declName_3047_, v___x_3056_);
v___x_3058_ = lean_st_ref_get(v_a_3051_);
v_env_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc_ref_n(v_env_3059_, 2);
lean_dec(v___x_3058_);
v___x_3060_ = 1;
lean_inc(v___x_3057_);
v___x_3061_ = l_Lean_Environment_contains(v_env_3059_, v___x_3057_, v___x_3060_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; lean_object* v_toEnvExtension_3063_; lean_object* v_asyncMode_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; 
lean_dec(v___x_3057_);
v___x_3062_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
v_toEnvExtension_3063_ = lean_ctor_get(v___x_3062_, 0);
v_asyncMode_3064_ = lean_ctor_get(v_toEnvExtension_3063_, 2);
v___x_3065_ = 0;
lean_inc(v_declName_3047_);
v___x_3066_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3053_, v___x_3062_, v_env_3059_, v_declName_3047_, v_asyncMode_3064_, v___x_3065_);
if (lean_obj_tag(v___x_3066_) == 1)
{
lean_object* v_val_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3091_; 
v_val_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3091_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_val_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3091_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; 
v___x_3071_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_3047_, v_val_3067_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3082_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3074_ = v___x_3071_;
v_isShared_3075_ = v_isSharedCheck_3082_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3071_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3082_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v_a_3072_);
v___x_3077_ = v___x_3069_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
lean_object* v___x_3079_; 
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 0, v___x_3077_);
v___x_3079_ = v___x_3074_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_del_object(v___x_3069_);
v_a_3083_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3071_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3071_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
else
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_dec(v___x_3066_);
lean_dec(v_declName_3047_);
v___x_3092_ = lean_box(0);
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
return v___x_3093_;
}
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec_ref(v_env_3059_);
lean_dec(v_declName_3047_);
v___x_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3057_);
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
return v___x_3095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object* v_declName_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
lean_dec(v_a_3100_);
lean_dec_ref(v_a_3099_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_));
v___x_3106_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object* v_a_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
return v_res_3108_;
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
