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
uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_(lean_object* v_env_18_, lean_object* v_n_19_, lean_object* v_x_20_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = l_Lean_Environment_hasExposedBody(v_env_18_, v_n_19_);
return v___x_21_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_env_18_ = stack[0].m_obj;
lean_object* v_n_19_ = stack[1].m_obj;
lean_object* v_x_20_ = stack[2].m_obj;
uint8_t v_res_22_;
v_res_22_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_(v_env_18_, v_n_19_, v_x_20_);
stack->m_num = v_res_22_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object* v_env_23_, lean_object* v_n_24_, lean_object* v_x_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_(v_env_23_, v_n_24_, v_x_25_);
lean_dec_ref(v_x_25_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_28_, lean_object* v_x_29_){
_start:
{
if (lean_obj_tag(v_x_29_) == 0)
{
lean_object* v_k_30_; lean_object* v_v_31_; lean_object* v_l_32_; lean_object* v_r_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_k_30_ = lean_ctor_get(v_x_29_, 1);
v_v_31_ = lean_ctor_get(v_x_29_, 2);
v_l_32_ = lean_ctor_get(v_x_29_, 3);
v_r_33_ = lean_ctor_get(v_x_29_, 4);
v___x_34_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_28_, v_l_32_);
lean_inc(v_v_31_);
lean_inc(v_k_30_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_k_30_);
lean_ctor_set(v___x_35_, 1, v_v_31_);
v___x_36_ = lean_array_push(v___x_34_, v___x_35_);
v_init_28_ = v___x_36_;
v_x_29_ = v_r_33_;
goto _start;
}
else
{
return v_init_28_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_38_, v_x_39_);
lean_dec(v_x_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_(lean_object* v_env_43_, lean_object* v_s_44_){
_start:
{
lean_object* v___f_45_; lean_object* v___x_46_; lean_object* v_all_47_; lean_object* v___x_48_; lean_object* v_exported_49_; lean_object* v___x_50_; 
v___f_45_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_45_, 0, v_env_43_);
v___x_46_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_));
v_all_47_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v___x_46_, v_s_44_);
v___x_48_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_45_, v_s_44_);
v_exported_49_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v___x_46_, v___x_48_);
lean_dec(v___x_48_);
lean_inc_ref(v_exported_49_);
v___x_50_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_50_, 0, v_exported_49_);
lean_ctor_set(v___x_50_, 1, v_exported_49_);
lean_ctor_set(v___x_50_, 2, v_all_47_);
return v___x_50_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; 
v___f_64_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_));
v___x_65_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_));
v___x_66_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_));
v___x_67_ = 1;
v___x_68_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_65_, v___x_66_, v___x_67_, v___f_64_);
return v___x_68_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_69_;
v_res_69_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_();
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2_();
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0(lean_object* v_init_72_, lean_object* v_t_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_72_, v_t_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_75_, lean_object* v_t_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_2576816323____hygCtx___hyg_2__spec__0(v_init_75_, v_t_76_);
lean_dec(v_t_76_);
return v_res_77_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0(lean_object* v_k_78_, lean_object* v_b_79_, lean_object* v_c_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; 
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
v___x_86_ = lean_apply_7(v_k_78_, v_b_79_, v_c_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, lean_box(0));
return v___x_86_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_78_ = stack[0].m_obj;
lean_object* v_b_79_ = stack[1].m_obj;
lean_object* v_c_80_ = stack[2].m_obj;
lean_object* v___y_81_ = stack[3].m_obj;
lean_object* v___y_82_ = stack[4].m_obj;
lean_object* v___y_83_ = stack[5].m_obj;
lean_object* v___y_84_ = stack[6].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0(v_k_78_, v_b_79_, v_c_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0___boxed(lean_object* v_k_88_, lean_object* v_b_89_, lean_object* v_c_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0(v_k_88_, v_b_89_, v_c_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_96_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(lean_object* v_e_97_, lean_object* v_k_98_, uint8_t v_cleanupAnnotations_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___f_105_; uint8_t v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___f_105_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_105_, 0, v_k_98_);
v___x_106_ = 1;
v___x_107_ = 0;
v___x_108_ = lean_box(0);
v___x_109_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_97_, v___x_106_, v___x_107_, v___x_106_, v___x_107_, v___x_108_, v___f_105_, v_cleanupAnnotations_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
v_a_118_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_109_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_109_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_97_ = stack[0].m_obj;
lean_object* v_k_98_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_99_ = stack[2].m_num;
lean_object* v___y_100_ = stack[3].m_obj;
lean_object* v___y_101_ = stack[4].m_obj;
lean_object* v___y_102_ = stack[5].m_obj;
lean_object* v___y_103_ = stack[6].m_obj;
lean_object* v_res_126_;
v_res_126_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_e_97_, v_k_98_, v_cleanupAnnotations_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg___boxed(lean_object* v_e_127_, lean_object* v_k_128_, lean_object* v_cleanupAnnotations_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_135_; lean_object* v_res_136_; 
v_cleanupAnnotations_boxed_135_ = lean_unbox(v_cleanupAnnotations_129_);
v_res_136_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_e_127_, v_k_128_, v_cleanupAnnotations_boxed_135_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
return v_res_136_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3(lean_object* v_00_u03b1_137_, lean_object* v_e_138_, lean_object* v_k_139_, uint8_t v_cleanupAnnotations_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_e_138_, v_k_139_, v_cleanupAnnotations_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
return v___x_146_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_138_ = stack[1].m_obj;
lean_object* v_k_139_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_140_ = stack[3].m_num;
lean_object* v___y_141_ = stack[4].m_obj;
lean_object* v___y_142_ = stack[5].m_obj;
lean_object* v___y_143_ = stack[6].m_obj;
lean_object* v___y_144_ = stack[7].m_obj;
lean_object* v_res_147_;
v_res_147_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3(lean_box(0), v_e_138_, v_k_139_, v_cleanupAnnotations_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
stack->m_obj
 = v_res_147_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___boxed(lean_object* v_00_u03b1_148_, lean_object* v_e_149_, lean_object* v_k_150_, lean_object* v_cleanupAnnotations_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_157_; lean_object* v_res_158_; 
v_cleanupAnnotations_boxed_157_ = lean_unbox(v_cleanupAnnotations_151_);
v_res_158_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3(v_00_u03b1_148_, v_e_149_, v_k_150_, v_cleanupAnnotations_boxed_157_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_158_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(lean_object* v_thm_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; lean_object* v_env_163_; lean_object* v_toConstantVal_164_; lean_object* v_value_165_; lean_object* v_all_166_; uint8_t v___y_168_; lean_object* v_type_176_; uint8_t v___x_177_; 
v___x_162_ = lean_st_ref_get(v___y_160_);
v_env_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc_ref_n(v_env_163_, 2);
lean_dec(v___x_162_);
v_toConstantVal_164_ = lean_ctor_get(v_thm_159_, 0);
v_value_165_ = lean_ctor_get(v_thm_159_, 1);
v_all_166_ = lean_ctor_get(v_thm_159_, 2);
v_type_176_ = lean_ctor_get(v_toConstantVal_164_, 2);
v___x_177_ = l_Lean_Environment_hasUnsafe(v_env_163_, v_type_176_);
if (v___x_177_ == 0)
{
uint8_t v___x_178_; 
v___x_178_ = l_Lean_Environment_hasUnsafe(v_env_163_, v_value_165_);
v___y_168_ = v___x_178_;
goto v___jp_167_;
}
else
{
lean_dec_ref(v_env_163_);
v___y_168_ = v___x_177_;
goto v___jp_167_;
}
v___jp_167_:
{
if (v___y_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_169_, 0, v_thm_159_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
lean_inc(v_all_166_);
lean_inc_ref(v_value_165_);
lean_inc_ref(v_toConstantVal_164_);
lean_dec_ref(v_thm_159_);
v___x_171_ = lean_box(0);
v___x_172_ = 0;
v___x_173_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_173_, 0, v_toConstantVal_164_);
lean_ctor_set(v___x_173_, 1, v_value_165_);
lean_ctor_set(v___x_173_, 2, v___x_171_);
lean_ctor_set(v___x_173_, 3, v_all_166_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*4, v___x_172_);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_159_ = stack[0].m_obj;
lean_object* v___y_160_ = stack[1].m_obj;
lean_object* v_res_179_;
v_res_179_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v_thm_159_, v___y_160_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg___boxed(lean_object* v_thm_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v_thm_180_, v___y_181_);
lean_dec(v___y_181_);
return v_res_183_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4(lean_object* v_thm_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v_thm_184_, v___y_188_);
return v___x_190_;
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_184_ = stack[0].m_obj;
lean_object* v___y_185_ = stack[1].m_obj;
lean_object* v___y_186_ = stack[2].m_obj;
lean_object* v___y_187_ = stack[3].m_obj;
lean_object* v___y_188_ = stack[4].m_obj;
lean_object* v_res_191_;
v_res_191_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4(v_thm_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
stack->m_obj
 = v_res_191_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___boxed(lean_object* v_thm_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4(v_thm_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
return v_res_198_;
}
}
lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(lean_object* v___y_199_, uint8_t v_isExporting_200_, lean_object* v___x_201_, lean_object* v___y_202_, lean_object* v___x_203_, lean_object* v_a_x3f_204_){
_start:
{
lean_object* v___x_206_; lean_object* v_env_207_; lean_object* v_nextMacroScope_208_; lean_object* v_ngen_209_; lean_object* v_auxDeclNGen_210_; lean_object* v_traceState_211_; lean_object* v_recordedDeps_212_; lean_object* v_messages_213_; lean_object* v_infoState_214_; lean_object* v_snapshotTasks_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_240_; 
v___x_206_ = lean_st_ref_take(v___y_199_);
v_env_207_ = lean_ctor_get(v___x_206_, 0);
v_nextMacroScope_208_ = lean_ctor_get(v___x_206_, 1);
v_ngen_209_ = lean_ctor_get(v___x_206_, 2);
v_auxDeclNGen_210_ = lean_ctor_get(v___x_206_, 3);
v_traceState_211_ = lean_ctor_get(v___x_206_, 4);
v_recordedDeps_212_ = lean_ctor_get(v___x_206_, 6);
v_messages_213_ = lean_ctor_get(v___x_206_, 7);
v_infoState_214_ = lean_ctor_get(v___x_206_, 8);
v_snapshotTasks_215_ = lean_ctor_get(v___x_206_, 9);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v___x_206_, 5);
lean_dec(v_unused_241_);
v___x_217_ = v___x_206_;
v_isShared_218_ = v_isSharedCheck_240_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snapshotTasks_215_);
lean_inc(v_infoState_214_);
lean_inc(v_messages_213_);
lean_inc(v_recordedDeps_212_);
lean_inc(v_traceState_211_);
lean_inc(v_auxDeclNGen_210_);
lean_inc(v_ngen_209_);
lean_inc(v_nextMacroScope_208_);
lean_inc(v_env_207_);
lean_dec(v___x_206_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_240_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = l_Lean_Environment_setExporting(v_env_207_, v_isExporting_200_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 5, v___x_201_);
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_nextMacroScope_208_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_ngen_209_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_auxDeclNGen_210_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v_traceState_211_);
lean_ctor_set(v_reuseFailAlloc_239_, 5, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_239_, 6, v_recordedDeps_212_);
lean_ctor_set(v_reuseFailAlloc_239_, 7, v_messages_213_);
lean_ctor_set(v_reuseFailAlloc_239_, 8, v_infoState_214_);
lean_ctor_set(v_reuseFailAlloc_239_, 9, v_snapshotTasks_215_);
v___x_221_ = v_reuseFailAlloc_239_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_mctx_224_; lean_object* v_zetaDeltaFVarIds_225_; lean_object* v_postponed_226_; lean_object* v_diag_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_237_; 
v___x_222_ = lean_st_ref_put(v___y_199_, v___x_221_);
v___x_223_ = lean_st_ref_take(v___y_202_);
v_mctx_224_ = lean_ctor_get(v___x_223_, 0);
v_zetaDeltaFVarIds_225_ = lean_ctor_get(v___x_223_, 2);
v_postponed_226_ = lean_ctor_get(v___x_223_, 3);
v_diag_227_ = lean_ctor_get(v___x_223_, 4);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v___x_223_, 1);
lean_dec(v_unused_238_);
v___x_229_ = v___x_223_;
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_diag_227_);
lean_inc(v_postponed_226_);
lean_inc(v_zetaDeltaFVarIds_225_);
lean_inc(v_mctx_224_);
lean_dec(v___x_223_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_231_ = lean_box(0);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___x_203_);
v___x_233_ = v___x_229_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_mctx_224_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_zetaDeltaFVarIds_225_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_postponed_226_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_diag_227_);
v___x_233_ = v_reuseFailAlloc_236_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_st_ref_put(v___y_202_, v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_231_);
return v___x_235_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_199_ = stack[0].m_obj;
uint8_t v_isExporting_200_ = stack[1].m_num;
lean_object* v___x_201_ = stack[2].m_obj;
lean_object* v___y_202_ = stack[3].m_obj;
lean_object* v___x_203_ = stack[4].m_obj;
lean_object* v_a_x3f_204_ = stack[5].m_obj;
lean_object* v_res_242_;
v_res_242_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(v___y_199_, v_isExporting_200_, v___x_201_, v___y_202_, v___x_203_, v_a_x3f_204_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0___boxed(lean_object* v___y_243_, lean_object* v_isExporting_244_, lean_object* v___x_245_, lean_object* v___y_246_, lean_object* v___x_247_, lean_object* v_a_x3f_248_, lean_object* v___y_249_){
_start:
{
uint8_t v_isExporting_boxed_250_; lean_object* v_res_251_; 
v_isExporting_boxed_250_ = lean_unbox(v_isExporting_244_);
v_res_251_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(v___y_243_, v_isExporting_boxed_250_, v___x_245_, v___y_246_, v___x_247_, v_a_x3f_248_);
lean_dec(v_a_x3f_248_);
lean_dec(v___y_246_);
lean_dec(v___y_243_);
return v_res_251_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_252_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__0);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__1);
v___x_258_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
lean_ctor_set(v___x_258_, 2, v___x_257_);
lean_ctor_set(v___x_258_, 3, v___x_257_);
lean_ctor_set(v___x_258_, 4, v___x_257_);
lean_ctor_set(v___x_258_, 5, v___x_257_);
return v___x_258_;
}
}
lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(lean_object* v_x_259_, uint8_t v_isExporting_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; lean_object* v_env_267_; lean_object* v___x_268_; uint8_t v_isModule_269_; 
v___x_266_ = lean_st_ref_get(v___y_264_);
v_env_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc_ref(v_env_267_);
lean_dec(v___x_266_);
v___x_268_ = l_Lean_Environment_header(v_env_267_);
v_isModule_269_ = lean_ctor_get_uint8(v___x_268_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_268_);
if (v_isModule_269_ == 0)
{
lean_object* v___x_270_; 
lean_dec_ref(v_env_267_);
lean_inc(v___y_264_);
lean_inc_ref(v___y_263_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
v___x_270_ = lean_apply_5(v_x_259_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, lean_box(0));
return v___x_270_;
}
else
{
uint8_t v_isExporting_271_; 
v_isExporting_271_ = lean_ctor_get_uint8(v_env_267_, sizeof(void*)*13);
lean_dec_ref(v_env_267_);
if (v_isExporting_260_ == 0)
{
if (v_isExporting_271_ == 0)
{
lean_object* v___x_338_; 
lean_inc(v___y_264_);
lean_inc_ref(v___y_263_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
v___x_338_ = lean_apply_5(v_x_259_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, lean_box(0));
return v___x_338_;
}
else
{
goto v___jp_272_;
}
}
else
{
if (v_isExporting_271_ == 0)
{
goto v___jp_272_;
}
else
{
lean_object* v___x_339_; 
lean_inc(v___y_264_);
lean_inc_ref(v___y_263_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
v___x_339_ = lean_apply_5(v_x_259_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, lean_box(0));
return v___x_339_;
}
}
v___jp_272_:
{
lean_object* v___x_273_; lean_object* v_env_274_; lean_object* v_nextMacroScope_275_; lean_object* v_ngen_276_; lean_object* v_auxDeclNGen_277_; lean_object* v_traceState_278_; lean_object* v_recordedDeps_279_; lean_object* v_messages_280_; lean_object* v_infoState_281_; lean_object* v_snapshotTasks_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_336_; 
v___x_273_ = lean_st_ref_take(v___y_264_);
v_env_274_ = lean_ctor_get(v___x_273_, 0);
v_nextMacroScope_275_ = lean_ctor_get(v___x_273_, 1);
v_ngen_276_ = lean_ctor_get(v___x_273_, 2);
v_auxDeclNGen_277_ = lean_ctor_get(v___x_273_, 3);
v_traceState_278_ = lean_ctor_get(v___x_273_, 4);
v_recordedDeps_279_ = lean_ctor_get(v___x_273_, 6);
v_messages_280_ = lean_ctor_get(v___x_273_, 7);
v_infoState_281_ = lean_ctor_get(v___x_273_, 8);
v_snapshotTasks_282_ = lean_ctor_get(v___x_273_, 9);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v___x_273_, 5);
lean_dec(v_unused_337_);
v___x_284_ = v___x_273_;
v_isShared_285_ = v_isSharedCheck_336_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_snapshotTasks_282_);
lean_inc(v_infoState_281_);
lean_inc(v_messages_280_);
lean_inc(v_recordedDeps_279_);
lean_inc(v_traceState_278_);
lean_inc(v_auxDeclNGen_277_);
lean_inc(v_ngen_276_);
lean_inc(v_nextMacroScope_275_);
lean_inc(v_env_274_);
lean_dec(v___x_273_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_336_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_286_ = l_Lean_Environment_setExporting(v_env_274_, v_isExporting_260_);
v___x_287_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 5, v___x_287_);
lean_ctor_set(v___x_284_, 0, v___x_286_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_nextMacroScope_275_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_ngen_276_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v_auxDeclNGen_277_);
lean_ctor_set(v_reuseFailAlloc_335_, 4, v_traceState_278_);
lean_ctor_set(v_reuseFailAlloc_335_, 5, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_335_, 6, v_recordedDeps_279_);
lean_ctor_set(v_reuseFailAlloc_335_, 7, v_messages_280_);
lean_ctor_set(v_reuseFailAlloc_335_, 8, v_infoState_281_);
lean_ctor_set(v_reuseFailAlloc_335_, 9, v_snapshotTasks_282_);
v___x_289_ = v_reuseFailAlloc_335_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_mctx_292_; lean_object* v_zetaDeltaFVarIds_293_; lean_object* v_postponed_294_; lean_object* v_diag_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_333_; 
v___x_290_ = lean_st_ref_put(v___y_264_, v___x_289_);
v___x_291_ = lean_st_ref_take(v___y_262_);
v_mctx_292_ = lean_ctor_get(v___x_291_, 0);
v_zetaDeltaFVarIds_293_ = lean_ctor_get(v___x_291_, 2);
v_postponed_294_ = lean_ctor_get(v___x_291_, 3);
v_diag_295_ = lean_ctor_get(v___x_291_, 4);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v___x_291_, 1);
lean_dec(v_unused_334_);
v___x_297_ = v___x_291_;
v_isShared_298_ = v_isSharedCheck_333_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_diag_295_);
lean_inc(v_postponed_294_);
lean_inc(v_zetaDeltaFVarIds_293_);
lean_inc(v_mctx_292_);
lean_dec(v___x_291_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_333_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_mctx_292_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_zetaDeltaFVarIds_293_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v_postponed_294_);
lean_ctor_set(v_reuseFailAlloc_332_, 4, v_diag_295_);
v___x_301_ = v_reuseFailAlloc_332_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v_r_303_; 
v___x_302_ = lean_st_ref_put(v___y_262_, v___x_301_);
lean_inc(v___y_264_);
lean_inc_ref(v___y_263_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
v_r_303_ = lean_apply_5(v_x_259_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, lean_box(0));
if (lean_obj_tag(v_r_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_320_; 
v_a_304_ = lean_ctor_get(v_r_303_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_r_303_);
if (v_isSharedCheck_320_ == 0)
{
v___x_306_ = v_r_303_;
v_isShared_307_ = v_isSharedCheck_320_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v_r_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_320_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
lean_inc(v_a_304_);
if (v_isShared_307_ == 0)
{
lean_ctor_set_tag(v___x_306_, 1);
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_319_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v___x_310_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(v___y_264_, v_isExporting_271_, v___x_287_, v___y_262_, v___x_299_, v___x_309_);
lean_dec_ref(v___x_309_);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v___x_310_, 0);
lean_dec(v_unused_318_);
v___x_312_ = v___x_310_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_dec(v___x_310_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v_a_304_);
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_304_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
v_a_321_ = lean_ctor_get(v_r_303_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v_r_303_, 1);
v___x_322_ = lean_box(0);
v___x_323_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___lam__0(v___y_264_, v_isExporting_271_, v___x_287_, v___y_262_, v___x_299_, v___x_322_);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v___x_323_, 0);
lean_dec(v_unused_331_);
v___x_325_ = v___x_323_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_dec(v___x_323_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 1);
lean_ctor_set(v___x_325_, 0, v_a_321_);
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_321_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_259_ = stack[0].m_obj;
uint8_t v_isExporting_260_ = stack[1].m_num;
lean_object* v___y_261_ = stack[2].m_obj;
lean_object* v___y_262_ = stack[3].m_obj;
lean_object* v___y_263_ = stack[4].m_obj;
lean_object* v___y_264_ = stack[5].m_obj;
lean_object* v_res_340_;
v_res_340_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v_x_259_, v_isExporting_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___boxed(lean_object* v_x_341_, lean_object* v_isExporting_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
uint8_t v_isExporting_boxed_348_; lean_object* v_res_349_; 
v_isExporting_boxed_348_ = lean_unbox(v_isExporting_342_);
v_res_349_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v_x_341_, v_isExporting_boxed_348_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_349_;
}
}
lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5(lean_object* v_00_u03b1_350_, lean_object* v_x_351_, uint8_t v_isExporting_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v_x_351_, v_isExporting_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
return v___x_358_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_351_ = stack[1].m_obj;
uint8_t v_isExporting_352_ = stack[2].m_num;
lean_object* v___y_353_ = stack[3].m_obj;
lean_object* v___y_354_ = stack[4].m_obj;
lean_object* v___y_355_ = stack[5].m_obj;
lean_object* v___y_356_ = stack[6].m_obj;
lean_object* v_res_359_;
v_res_359_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5(lean_box(0), v_x_351_, v_isExporting_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___boxed(lean_object* v_00_u03b1_360_, lean_object* v_x_361_, lean_object* v_isExporting_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
uint8_t v_isExporting_boxed_368_; lean_object* v_res_369_; 
v_isExporting_boxed_368_ = lean_unbox(v_isExporting_362_);
v_res_369_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5(v_00_u03b1_360_, v_x_361_, v_isExporting_boxed_368_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_369_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(lean_object* v_msgData_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; lean_object* v_env_377_; uint8_t v___x_378_; lean_object* v_env_379_; lean_object* v___x_380_; lean_object* v_toCold_381_; lean_object* v_mctx_382_; lean_object* v_lctx_383_; lean_object* v_options_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_376_ = lean_st_ref_get(v___y_374_);
v_env_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc_ref(v_env_377_);
lean_dec(v___x_376_);
v___x_378_ = 0;
v_env_379_ = l_Lean_Environment_setRecordingDeps(v_env_377_, v___x_378_);
v___x_380_ = lean_st_ref_get(v___y_372_);
v_toCold_381_ = lean_ctor_get(v___y_373_, 0);
v_mctx_382_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_mctx_382_);
lean_dec(v___x_380_);
v_lctx_383_ = lean_ctor_get(v___y_371_, 2);
v_options_384_ = lean_ctor_get(v_toCold_381_, 2);
lean_inc_ref(v_options_384_);
lean_inc_ref(v_lctx_383_);
v___x_385_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_385_, 0, v_env_379_);
lean_ctor_set(v___x_385_, 1, v_mctx_382_);
lean_ctor_set(v___x_385_, 2, v_lctx_383_);
lean_ctor_set(v___x_385_, 3, v_options_384_);
v___x_386_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v_msgData_370_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_370_ = stack[0].m_obj;
lean_object* v___y_371_ = stack[1].m_obj;
lean_object* v___y_372_ = stack[2].m_obj;
lean_object* v___y_373_ = stack[3].m_obj;
lean_object* v___y_374_ = stack[4].m_obj;
lean_object* v_res_388_;
v_res_388_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msgData_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
stack->m_obj
 = v_res_388_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0___boxed(lean_object* v_msgData_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msgData_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_395_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(lean_object* v_msg_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_ref_402_; lean_object* v___x_403_; lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_ref_402_ = lean_ctor_get(v___y_399_, 2);
v___x_403_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msg_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
lean_inc(v_ref_402_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_ref_402_);
lean_ctor_set(v___x_408_, 1, v_a_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 1);
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
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
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_396_ = stack[0].m_obj;
lean_object* v___y_397_ = stack[1].m_obj;
lean_object* v___y_398_ = stack[2].m_obj;
lean_object* v___y_399_ = stack[3].m_obj;
lean_object* v___y_400_ = stack[4].m_obj;
lean_object* v_res_413_;
v_res_413_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v_msg_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
stack->m_obj
 = v_res_413_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg___boxed(lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v_msg_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_420_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__0));
v___x_423_ = l_Lean_stringToMessageData(v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__2));
v___x_426_ = l_Lean_stringToMessageData(v___x_425_);
return v___x_426_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0(lean_object* v_declNameNonRec_438_, lean_object* v_xs_439_, lean_object* v_body_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
uint8_t v___y_491_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_508_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6));
v___x_509_ = lean_unsigned_to_nat(4u);
v___x_510_ = l_Lean_Expr_isAppOfArity(v_body_440_, v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8));
v___x_512_ = l_Lean_Expr_isAppOfArity(v_body_440_, v___x_511_, v___x_509_);
v___y_491_ = v___x_512_;
goto v___jp_490_;
}
else
{
v___y_491_ = v___x_510_;
goto v___jp_490_;
}
v___jp_446_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = l_Lean_Expr_appFn_x21(v_body_440_);
lean_dec_ref(v_body_440_);
v___x_448_ = l_Lean_Expr_appArg_x21(v___x_447_);
lean_dec_ref(v___x_447_);
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
lean_inc_ref(v___x_448_);
v___x_449_ = lean_infer_type(v___x_448_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; uint8_t v___x_451_; uint8_t v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = 0;
v___x_452_ = 1;
v___x_453_ = 1;
v___x_454_ = l_Lean_Meta_mkForallFVars(v_xs_439_, v_a_450_, v___x_451_, v___x_452_, v___x_452_, v___x_453_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_456_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v___x_456_ = l_Lean_Meta_mkLambdaFVars(v_xs_439_, v___x_448_, v___x_451_, v___x_452_, v___x_451_, v___x_452_, v___x_453_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_465_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_465_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_a_455_);
lean_ctor_set(v___x_461_, 1, v_a_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v_a_455_);
v_a_466_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_456_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_456_);
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
lean_dec_ref(v___x_448_);
v_a_474_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_454_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_454_);
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
lean_dec_ref(v___x_448_);
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
v___jp_490_:
{
if (v___y_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
v___x_492_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__1);
v___x_493_ = l_Lean_MessageData_ofConstName(v_declNameNonRec_438_, v___y_491_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__3);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = l_Lean_indentExpr(v_body_440_);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_498_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
else
{
lean_dec(v_declNameNonRec_438_);
goto v___jp_446_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNameNonRec_438_ = stack[0].m_obj;
lean_object* v_xs_439_ = stack[1].m_obj;
lean_object* v_body_440_ = stack[2].m_obj;
lean_object* v___y_441_ = stack[3].m_obj;
lean_object* v___y_442_ = stack[4].m_obj;
lean_object* v___y_443_ = stack[5].m_obj;
lean_object* v___y_444_ = stack[6].m_obj;
lean_object* v_res_513_;
v_res_513_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0(v_declNameNonRec_438_, v_xs_439_, v_body_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___boxed(lean_object* v_declNameNonRec_514_, lean_object* v_xs_515_, lean_object* v_body_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0(v_declNameNonRec_514_, v_xs_515_, v_body_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v_xs_515_);
return v_res_522_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0(void){
_start:
{
lean_object* v___x_523_; lean_object* v_dummy_524_; 
v___x_523_ = lean_box(0);
v_dummy_524_ = l_Lean_Expr_sort___override(v___x_523_);
return v_dummy_524_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1(lean_object* v_declNameNonRec_535_, lean_object* v___x_536_, lean_object* v___x_537_, uint8_t v___x_538_, lean_object* v_xs_539_, lean_object* v_body_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; uint8_t v___x_553_; lean_object* v___y_555_; 
lean_inc(v___x_536_);
v___x_546_ = l_Lean_mkConst(v_declNameNonRec_535_, v___x_536_);
v___x_547_ = l_Lean_mkAppN(v___x_546_, v_xs_539_);
v___x_548_ = l_Lean_mkConst(v___x_537_, v___x_536_);
v___x_549_ = l_Lean_mkAppN(v___x_548_, v_xs_539_);
lean_inc_ref(v___x_547_);
v___x_550_ = l_Lean_Expr_app___override(v___x_549_, v___x_547_);
v___x_551_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6));
v___x_552_ = l_Lean_Expr_isAppOf(v_body_540_, v___x_551_);
v___x_553_ = 1;
if (v___x_552_ == 0)
{
lean_object* v___x_605_; 
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2));
v___y_555_ = v___x_605_;
goto v___jp_554_;
}
else
{
lean_object* v___x_606_; 
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4));
v___y_555_ = v___x_606_;
goto v___jp_554_;
}
v___jp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_dummy_559_; lean_object* v_nargs_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_556_ = l_Lean_Expr_getAppFn(v_body_540_);
v___x_557_ = l_Lean_Expr_constLevels_x21(v___x_556_);
lean_dec_ref(v___x_556_);
lean_inc(v___y_555_);
v___x_558_ = l_Lean_mkConst(v___y_555_, v___x_557_);
v_dummy_559_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_560_ = l_Lean_Expr_getAppNumArgs(v_body_540_);
lean_inc(v_nargs_560_);
v___x_561_ = lean_mk_array(v_nargs_560_, v_dummy_559_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_sub(v_nargs_560_, v___x_562_);
lean_dec(v_nargs_560_);
v___x_564_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_body_540_, v___x_561_, v___x_563_);
v___x_565_ = l_Lean_mkAppN(v___x_558_, v___x_564_);
lean_dec_ref(v___x_564_);
v___x_566_ = l_Lean_Meta_mkEq(v___x_547_, v___x_550_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; uint8_t v___x_568_; lean_object* v___x_569_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v___x_568_ = 1;
v___x_569_ = l_Lean_Meta_mkForallFVars(v_xs_539_, v_a_567_, v___x_538_, v___x_553_, v___x_553_, v___x_568_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v___x_571_ = l_Lean_Meta_mkLambdaFVars(v_xs_539_, v___x_565_, v___x_538_, v___x_553_, v___x_538_, v___x_553_, v___x_568_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_580_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_580_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_a_570_);
lean_ctor_set(v___x_576_, 1, v_a_572_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec(v_a_570_);
v_a_581_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_571_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_571_);
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
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v___x_565_);
v_a_589_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_569_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_569_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v___x_565_);
v_a_597_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_566_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_566_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
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
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNameNonRec_535_ = stack[0].m_obj;
lean_object* v___x_536_ = stack[1].m_obj;
lean_object* v___x_537_ = stack[2].m_obj;
uint8_t v___x_538_ = stack[3].m_num;
lean_object* v_xs_539_ = stack[4].m_obj;
lean_object* v_body_540_ = stack[5].m_obj;
lean_object* v___y_541_ = stack[6].m_obj;
lean_object* v___y_542_ = stack[7].m_obj;
lean_object* v___y_543_ = stack[8].m_obj;
lean_object* v___y_544_ = stack[9].m_obj;
lean_object* v_res_607_;
v_res_607_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1(v_declNameNonRec_535_, v___x_536_, v___x_537_, v___x_538_, v_xs_539_, v_body_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
stack->m_obj
 = v_res_607_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___boxed(lean_object* v_declNameNonRec_608_, lean_object* v___x_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v_xs_612_, lean_object* v_body_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
uint8_t v___x_10376__boxed_619_; lean_object* v_res_620_; 
v___x_10376__boxed_619_ = lean_unbox(v___x_611_);
v_res_620_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1(v_declNameNonRec_608_, v___x_609_, v___x_610_, v___x_10376__boxed_619_, v_xs_612_, v_body_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec_ref(v_xs_612_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
if (lean_obj_tag(v_a_621_) == 0)
{
lean_object* v___x_623_; 
v___x_623_ = l_List_reverse___redArg(v_a_622_);
return v___x_623_;
}
else
{
lean_object* v_head_624_; lean_object* v_tail_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_634_; 
v_head_624_ = lean_ctor_get(v_a_621_, 0);
v_tail_625_ = lean_ctor_get(v_a_621_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_a_621_);
if (v_isSharedCheck_634_ == 0)
{
v___x_627_ = v_a_621_;
v_isShared_628_ = v_isSharedCheck_634_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_tail_625_);
lean_inc(v_head_624_);
lean_dec(v_a_621_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_634_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = l_Lean_mkLevelParam(v_head_624_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_a_622_);
lean_ctor_set(v___x_627_, 0, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_a_622_);
v___x_631_ = v_reuseFailAlloc_633_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
v_a_621_ = v_tail_625_;
v_a_622_ = v___x_631_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_instMonadEIO___redArg();
return v___x_635_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(lean_object* v_msg_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_toApplicative_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_709_; 
v___x_646_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0, &l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__0);
v___x_647_ = l_StateRefT_x27_instMonad___redArg(v___x_646_);
v_toApplicative_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v___x_647_, 1);
lean_dec(v_unused_710_);
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_709_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_toApplicative_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_709_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v_toFunctor_652_; lean_object* v_toSeq_653_; lean_object* v_toSeqLeft_654_; lean_object* v_toSeqRight_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_707_; 
v_toFunctor_652_ = lean_ctor_get(v_toApplicative_648_, 0);
v_toSeq_653_ = lean_ctor_get(v_toApplicative_648_, 2);
v_toSeqLeft_654_ = lean_ctor_get(v_toApplicative_648_, 3);
v_toSeqRight_655_ = lean_ctor_get(v_toApplicative_648_, 4);
v_isSharedCheck_707_ = !lean_is_exclusive(v_toApplicative_648_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_toApplicative_648_, 1);
lean_dec(v_unused_708_);
v___x_657_ = v_toApplicative_648_;
v_isShared_658_ = v_isSharedCheck_707_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_toSeqRight_655_);
lean_inc(v_toSeqLeft_654_);
lean_inc(v_toSeq_653_);
lean_inc(v_toFunctor_652_);
lean_dec(v_toApplicative_648_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_707_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___f_661_; lean_object* v___f_662_; lean_object* v___x_663_; lean_object* v___f_664_; lean_object* v___f_665_; lean_object* v___f_666_; lean_object* v___x_668_; 
v___f_659_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__1));
v___f_660_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__2));
lean_inc_ref(v_toFunctor_652_);
v___f_661_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_661_, 0, v_toFunctor_652_);
v___f_662_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_662_, 0, v_toFunctor_652_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___f_661_);
lean_ctor_set(v___x_663_, 1, v___f_662_);
v___f_664_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_664_, 0, v_toSeqRight_655_);
v___f_665_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_665_, 0, v_toSeqLeft_654_);
v___f_666_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_666_, 0, v_toSeq_653_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v___f_664_);
lean_ctor_set(v___x_657_, 3, v___f_665_);
lean_ctor_set(v___x_657_, 2, v___f_666_);
lean_ctor_set(v___x_657_, 1, v___f_659_);
lean_ctor_set(v___x_657_, 0, v___x_663_);
v___x_668_ = v___x_657_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___f_659_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v___f_666_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v___f_665_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v___f_664_);
v___x_668_ = v_reuseFailAlloc_706_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_670_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___f_660_);
lean_ctor_set(v___x_650_, 0, v___x_668_);
v___x_670_ = v___x_650_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___f_660_);
v___x_670_ = v_reuseFailAlloc_705_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; lean_object* v_toApplicative_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_703_; 
v___x_671_ = l_StateRefT_x27_instMonad___redArg(v___x_670_);
v_toApplicative_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v___x_671_, 1);
lean_dec(v_unused_704_);
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_703_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_toApplicative_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_703_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_toFunctor_676_; lean_object* v_toSeq_677_; lean_object* v_toSeqLeft_678_; lean_object* v_toSeqRight_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_701_; 
v_toFunctor_676_ = lean_ctor_get(v_toApplicative_672_, 0);
v_toSeq_677_ = lean_ctor_get(v_toApplicative_672_, 2);
v_toSeqLeft_678_ = lean_ctor_get(v_toApplicative_672_, 3);
v_toSeqRight_679_ = lean_ctor_get(v_toApplicative_672_, 4);
v_isSharedCheck_701_ = !lean_is_exclusive(v_toApplicative_672_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v_toApplicative_672_, 1);
lean_dec(v_unused_702_);
v___x_681_ = v_toApplicative_672_;
v_isShared_682_ = v_isSharedCheck_701_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_toSeqRight_679_);
lean_inc(v_toSeqLeft_678_);
lean_inc(v_toSeq_677_);
lean_inc(v_toFunctor_676_);
lean_dec(v_toApplicative_672_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_701_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___f_683_; lean_object* v___f_684_; lean_object* v___f_685_; lean_object* v___f_686_; lean_object* v___x_687_; lean_object* v___f_688_; lean_object* v___f_689_; lean_object* v___f_690_; lean_object* v___x_692_; 
v___f_683_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__3));
v___f_684_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___closed__4));
lean_inc_ref(v_toFunctor_676_);
v___f_685_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_685_, 0, v_toFunctor_676_);
v___f_686_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_686_, 0, v_toFunctor_676_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___f_685_);
lean_ctor_set(v___x_687_, 1, v___f_686_);
v___f_688_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_688_, 0, v_toSeqRight_679_);
v___f_689_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_689_, 0, v_toSeqLeft_678_);
v___f_690_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_690_, 0, v_toSeq_677_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 4, v___f_688_);
lean_ctor_set(v___x_681_, 3, v___f_689_);
lean_ctor_set(v___x_681_, 2, v___f_690_);
lean_ctor_set(v___x_681_, 1, v___f_683_);
lean_ctor_set(v___x_681_, 0, v___x_687_);
v___x_692_ = v___x_681_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___f_683_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v___f_690_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v___f_689_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v___f_688_);
v___x_692_ = v_reuseFailAlloc_700_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___f_684_);
lean_ctor_set(v___x_674_, 0, v___x_692_);
v___x_694_ = v___x_674_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___f_684_);
v___x_694_ = v_reuseFailAlloc_699_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_9043__overap_697_; lean_object* v___x_698_; 
v___x_695_ = lean_box(0);
v___x_696_ = l_instInhabitedOfMonad___redArg(v___x_694_, v___x_695_);
v___x_9043__overap_697_ = lean_panic_fn_borrowed(v___x_696_, v_msg_640_);
lean_dec(v___x_696_);
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
lean_inc(v___y_642_);
lean_inc_ref(v___y_641_);
v___x_698_ = lean_apply_5(v___x_9043__overap_697_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, lean_box(0));
return v___x_698_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_640_ = stack[0].m_obj;
lean_object* v___y_641_ = stack[1].m_obj;
lean_object* v___y_642_ = stack[2].m_obj;
lean_object* v___y_643_ = stack[3].m_obj;
lean_object* v___y_644_ = stack[4].m_obj;
lean_object* v_res_711_;
v_res_711_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(v_msg_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
stack->m_obj
 = v_res_711_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2___boxed(lean_object* v_msg_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(v_msg_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_718_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__0));
v___x_721_ = l_Lean_stringToMessageData(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__2));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_728_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_729_ = lean_unsigned_to_nat(11u);
v___x_730_ = lean_unsigned_to_nat(115u);
v___x_731_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__5));
v___x_732_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__4));
v___x_733_ = l_mkPanicMessageWithDecl(v___x_732_, v___x_731_, v___x_730_, v___x_729_, v___x_728_);
return v___x_733_;
}
}
lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(lean_object* v_constName_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_748_; lean_object* v_env_749_; uint8_t v___x_750_; lean_object* v___x_751_; 
v___x_748_ = lean_st_ref_get(v___y_738_);
v_env_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc_ref(v_env_749_);
lean_dec(v___x_748_);
v___x_750_ = 0;
lean_inc(v_constName_734_);
v___x_751_ = l_Lean_Environment_findAsync_x3f(v_env_749_, v_constName_734_, v___x_750_);
if (lean_obj_tag(v___x_751_) == 1)
{
lean_object* v_val_752_; uint8_t v_kind_753_; 
v_val_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v___x_751_, 1);
v_kind_753_ = lean_ctor_get_uint8(v_val_752_, sizeof(void*)*3);
if (v_kind_753_ == 0)
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_752_);
if (lean_obj_tag(v___x_754_) == 1)
{
lean_object* v_val_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_constName_734_);
v_val_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_val_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 0);
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_val_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v___x_754_);
v___x_763_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__7);
v___x_764_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_spec__2(v___x_763_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_773_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_773_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
if (lean_obj_tag(v_a_765_) == 0)
{
lean_del_object(v___x_767_);
goto v___jp_740_;
}
else
{
lean_object* v_val_769_; lean_object* v___x_771_; 
lean_dec(v_constName_734_);
v_val_769_ = lean_ctor_get(v_a_765_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v_a_765_, 1);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v_val_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_val_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v_constName_734_);
v_a_774_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_764_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_764_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
else
{
lean_dec(v_val_752_);
goto v___jp_740_;
}
}
else
{
lean_dec(v___x_751_);
goto v___jp_740_;
}
v___jp_740_:
{
lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_741_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__1);
v___x_742_ = 0;
v___x_743_ = l_Lean_MessageData_ofConstName(v_constName_734_, v___x_742_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_741_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__3);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_746_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
return v___x_747_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_734_ = stack[0].m_obj;
lean_object* v___y_735_ = stack[1].m_obj;
lean_object* v___y_736_ = stack[2].m_obj;
lean_object* v___y_737_ = stack[3].m_obj;
lean_object* v___y_738_ = stack[4].m_obj;
lean_object* v_res_782_;
v_res_782_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(v_constName_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___boxed(lean_object* v_constName_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(v_constName_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_789_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2(lean_object* v_declNameNonRec_792_, lean_object* v___f_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; lean_object* v_env_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_env_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_799_ = lean_st_ref_get(v___y_797_);
v_env_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc_ref(v_env_800_);
lean_dec(v___x_799_);
v___x_801_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__0));
lean_inc_n(v_declNameNonRec_792_, 3);
v___x_802_ = l_Lean_Meta_mkEqLikeNameFor(v_env_800_, v_declNameNonRec_792_, v___x_801_);
v___x_803_ = lean_st_ref_get(v___y_797_);
v_env_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc_ref(v_env_804_);
lean_dec(v___x_803_);
v___x_805_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___closed__1));
v___x_806_ = l_Lean_Meta_mkEqLikeNameFor(v_env_804_, v_declNameNonRec_792_, v___x_805_);
v___x_807_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1(v_declNameNonRec_792_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v_toConstantVal_809_; lean_object* v_value_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_939_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v_toConstantVal_809_ = lean_ctor_get(v_a_808_, 0);
v_value_810_ = lean_ctor_get(v_a_808_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; lean_object* v_unused_941_; 
v_unused_940_ = lean_ctor_get(v_a_808_, 3);
lean_dec(v_unused_940_);
v_unused_941_ = lean_ctor_get(v_a_808_, 2);
lean_dec(v_unused_941_);
v___x_812_ = v_a_808_;
v_isShared_813_ = v_isSharedCheck_939_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_value_810_);
lean_inc(v_toConstantVal_809_);
lean_dec(v_a_808_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_939_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_levelParams_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_936_; 
v_levelParams_814_ = lean_ctor_get(v_toConstantVal_809_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_toConstantVal_809_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; lean_object* v_unused_938_; 
v_unused_937_ = lean_ctor_get(v_toConstantVal_809_, 2);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_toConstantVal_809_, 0);
lean_dec(v_unused_938_);
v___x_816_ = v_toConstantVal_809_;
v_isShared_817_ = v_isSharedCheck_936_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_levelParams_814_);
lean_dec(v_toConstantVal_809_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_936_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___x_823_; 
v___x_818_ = lean_box(0);
lean_inc(v_levelParams_814_);
v___x_819_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(v_levelParams_814_, v___x_818_);
v___x_820_ = 0;
v___x_821_ = lean_box(v___x_820_);
lean_inc(v___x_806_);
v___f_822_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___boxed), 11, 4);
lean_closure_set(v___f_822_, 0, v_declNameNonRec_792_);
lean_closure_set(v___f_822_, 1, v___x_819_);
lean_closure_set(v___f_822_, 2, v___x_806_);
lean_closure_set(v___f_822_, 3, v___x_821_);
lean_inc_ref(v_value_810_);
v___x_823_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_810_, v___f_793_, v___x_820_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v_fst_825_; lean_object* v_snd_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_927_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v_fst_825_ = lean_ctor_get(v_a_824_, 0);
v_snd_826_ = lean_ctor_get(v_a_824_, 1);
v_isSharedCheck_927_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_927_ == 0)
{
v___x_828_ = v_a_824_;
v_isShared_829_ = v_isSharedCheck_927_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_snd_826_);
lean_inc(v_fst_825_);
lean_dec(v_a_824_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_927_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
lean_inc(v_levelParams_814_);
lean_inc(v___x_806_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 2, v_fst_825_);
lean_ctor_set(v___x_816_, 0, v___x_806_);
v___x_831_ = v___x_816_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_levelParams_814_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_fst_825_);
v___x_831_ = v_reuseFailAlloc_926_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_835_; 
v___x_832_ = lean_box(1);
v___x_833_ = 1;
lean_inc(v___x_806_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 1);
lean_ctor_set(v___x_828_, 1, v___x_818_);
lean_ctor_set(v___x_828_, 0, v___x_806_);
v___x_835_ = v___x_828_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_818_);
v___x_835_ = v_reuseFailAlloc_925_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_837_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 3, v___x_835_);
lean_ctor_set(v___x_812_, 2, v___x_832_);
lean_ctor_set(v___x_812_, 1, v_snd_826_);
lean_ctor_set(v___x_812_, 0, v___x_831_);
v___x_837_ = v___x_812_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_snd_826_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v___x_835_);
v___x_837_ = v_reuseFailAlloc_924_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*4, v___x_833_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
v___x_839_ = l_Lean_addDecl(v___x_838_, v___x_820_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_840_; lean_object* v_env_841_; lean_object* v_nextMacroScope_842_; lean_object* v_ngen_843_; lean_object* v_auxDeclNGen_844_; lean_object* v_traceState_845_; lean_object* v_recordedDeps_846_; lean_object* v_messages_847_; lean_object* v_infoState_848_; lean_object* v_snapshotTasks_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_914_; 
lean_dec_ref_known(v___x_839_, 1);
v___x_840_ = lean_st_ref_take(v___y_797_);
v_env_841_ = lean_ctor_get(v___x_840_, 0);
v_nextMacroScope_842_ = lean_ctor_get(v___x_840_, 1);
v_ngen_843_ = lean_ctor_get(v___x_840_, 2);
v_auxDeclNGen_844_ = lean_ctor_get(v___x_840_, 3);
v_traceState_845_ = lean_ctor_get(v___x_840_, 4);
v_recordedDeps_846_ = lean_ctor_get(v___x_840_, 6);
v_messages_847_ = lean_ctor_get(v___x_840_, 7);
v_infoState_848_ = lean_ctor_get(v___x_840_, 8);
v_snapshotTasks_849_ = lean_ctor_get(v___x_840_, 9);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v___x_840_, 5);
lean_dec(v_unused_915_);
v___x_851_ = v___x_840_;
v_isShared_852_ = v_isSharedCheck_914_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snapshotTasks_849_);
lean_inc(v_infoState_848_);
lean_inc(v_messages_847_);
lean_inc(v_recordedDeps_846_);
lean_inc(v_traceState_845_);
lean_inc(v_auxDeclNGen_844_);
lean_inc(v_ngen_843_);
lean_inc(v_nextMacroScope_842_);
lean_inc(v_env_841_);
lean_dec(v___x_840_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_914_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_853_ = l_Lean_addNoncomputable(v_env_841_, v___x_806_);
v___x_854_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 5, v___x_854_);
lean_ctor_set(v___x_851_, 0, v___x_853_);
v___x_856_ = v___x_851_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_nextMacroScope_842_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_ngen_843_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_auxDeclNGen_844_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_traceState_845_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_913_, 6, v_recordedDeps_846_);
lean_ctor_set(v_reuseFailAlloc_913_, 7, v_messages_847_);
lean_ctor_set(v_reuseFailAlloc_913_, 8, v_infoState_848_);
lean_ctor_set(v_reuseFailAlloc_913_, 9, v_snapshotTasks_849_);
v___x_856_ = v_reuseFailAlloc_913_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_mctx_859_; lean_object* v_zetaDeltaFVarIds_860_; lean_object* v_postponed_861_; lean_object* v_diag_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_911_; 
v___x_857_ = lean_st_ref_put(v___y_797_, v___x_856_);
v___x_858_ = lean_st_ref_take(v___y_795_);
v_mctx_859_ = lean_ctor_get(v___x_858_, 0);
v_zetaDeltaFVarIds_860_ = lean_ctor_get(v___x_858_, 2);
v_postponed_861_ = lean_ctor_get(v___x_858_, 3);
v_diag_862_ = lean_ctor_get(v___x_858_, 4);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v___x_858_, 1);
lean_dec(v_unused_912_);
v___x_864_ = v___x_858_;
v_isShared_865_ = v_isSharedCheck_911_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_diag_862_);
lean_inc(v_postponed_861_);
lean_inc(v_zetaDeltaFVarIds_860_);
lean_inc(v_mctx_859_);
lean_dec(v___x_858_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_911_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_866_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_866_);
v___x_868_ = v___x_864_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_mctx_859_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_zetaDeltaFVarIds_860_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_postponed_861_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_diag_862_);
v___x_868_ = v_reuseFailAlloc_910_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_st_ref_put(v___y_795_, v___x_868_);
v___x_870_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_810_, v___f_822_, v___x_820_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v_fst_872_; lean_object* v_snd_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_901_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
v_fst_872_ = lean_ctor_get(v_a_871_, 0);
v_snd_873_ = lean_ctor_get(v_a_871_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v_a_871_);
if (v_isSharedCheck_901_ == 0)
{
v___x_875_ = v_a_871_;
v_isShared_876_ = v_isSharedCheck_901_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_snd_873_);
lean_inc(v_fst_872_);
lean_dec(v_a_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_901_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_inc_n(v___x_802_, 2);
v___x_877_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_877_, 0, v___x_802_);
lean_ctor_set(v___x_877_, 1, v_levelParams_814_);
lean_ctor_set(v___x_877_, 2, v_fst_872_);
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
lean_ctor_set(v___x_875_, 1, v___x_818_);
lean_ctor_set(v___x_875_, 0, v___x_802_);
v___x_879_ = v___x_875_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_818_);
v___x_879_ = v_reuseFailAlloc_900_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_a_882_; lean_object* v___x_883_; 
v___x_880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_880_, 0, v___x_877_);
lean_ctor_set(v___x_880_, 1, v_snd_873_);
lean_ctor_set(v___x_880_, 2, v___x_879_);
v___x_881_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v___x_880_, v___y_797_);
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref(v___x_881_);
v___x_883_ = l_Lean_addDecl(v_a_882_, v___x_820_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_883_, 0);
lean_dec(v_unused_891_);
v___x_885_ = v___x_883_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_dec(v___x_883_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_802_);
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_802_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v___x_802_);
v_a_892_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_883_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_883_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_levelParams_814_);
lean_dec(v___x_802_);
v_a_902_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_870_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_870_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
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
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v___f_822_);
lean_dec(v_levelParams_814_);
lean_dec_ref(v_value_810_);
lean_dec(v___x_806_);
lean_dec(v___x_802_);
v_a_916_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_839_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_839_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
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
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref(v___f_822_);
lean_del_object(v___x_816_);
lean_dec(v_levelParams_814_);
lean_del_object(v___x_812_);
lean_dec_ref(v_value_810_);
lean_dec(v___x_806_);
lean_dec(v___x_802_);
v_a_928_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_823_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_823_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v___x_806_);
lean_dec(v___x_802_);
lean_dec_ref(v___f_793_);
lean_dec(v_declNameNonRec_792_);
v_a_942_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_807_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_807_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNameNonRec_792_ = stack[0].m_obj;
lean_object* v___f_793_ = stack[1].m_obj;
lean_object* v___y_794_ = stack[2].m_obj;
lean_object* v___y_795_ = stack[3].m_obj;
lean_object* v___y_796_ = stack[4].m_obj;
lean_object* v___y_797_ = stack[5].m_obj;
lean_object* v_res_950_;
v_res_950_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2(v_declNameNonRec_792_, v___f_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
stack->m_obj
 = v_res_950_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___boxed(lean_object* v_declNameNonRec_951_, lean_object* v___f_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2(v_declNameNonRec_951_, v___f_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
return v_res_958_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(lean_object* v_declNameNonRec_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___f_965_; lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v_env_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
lean_inc_n(v_declNameNonRec_959_, 2);
v___f_965_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___boxed), 8, 1);
lean_closure_set(v___f_965_, 0, v_declNameNonRec_959_);
v___f_966_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__2___boxed), 7, 2);
lean_closure_set(v___f_966_, 0, v_declNameNonRec_959_);
lean_closure_set(v___f_966_, 1, v___f_965_);
v___x_967_ = lean_st_ref_get(v_a_963_);
v_env_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc_ref(v_env_968_);
lean_dec(v___x_967_);
v___x_969_ = l_Lean_Environment_hasExposedBody(v_env_968_, v_declNameNonRec_959_);
v___x_970_ = l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg(v___f_966_, v___x_969_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
return v___x_970_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNameNonRec_959_ = stack[0].m_obj;
lean_object* v_a_960_ = stack[1].m_obj;
lean_object* v_a_961_ = stack[2].m_obj;
lean_object* v_a_962_ = stack[3].m_obj;
lean_object* v_a_963_ = stack[4].m_obj;
lean_object* v_res_971_;
v_res_971_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(v_declNameNonRec_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
stack->m_obj
 = v_res_971_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___boxed(lean_object* v_declNameNonRec_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(v_declNameNonRec_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_978_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0(lean_object* v_00_u03b1_979_, lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v_msg_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
return v___x_986_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_980_ = stack[1].m_obj;
lean_object* v___y_981_ = stack[2].m_obj;
lean_object* v___y_982_ = stack[3].m_obj;
lean_object* v___y_983_ = stack[4].m_obj;
lean_object* v___y_984_ = stack[5].m_obj;
lean_object* v_res_987_;
v_res_987_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0(lean_box(0), v_msg_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
stack->m_obj
 = v_res_987_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___boxed(lean_object* v_00_u03b1_988_, lean_object* v_msg_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0(v_00_u03b1_988_, v_msg_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_995_;
}
}
lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t v___x_996_, uint8_t v___x_997_, uint8_t v_____do__lift_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
if (v_____do__lift_998_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_box(v___x_996_);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_box(v___x_997_);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_996_ = stack[0].m_num;
uint8_t v___x_997_ = stack[1].m_num;
uint8_t v_____do__lift_998_ = stack[2].m_num;
lean_object* v___y_999_ = stack[3].m_obj;
lean_object* v___y_1000_ = stack[4].m_obj;
lean_object* v___y_1001_ = stack[5].m_obj;
lean_object* v___y_1002_ = stack[6].m_obj;
lean_object* v_res_1008_;
v_res_1008_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_996_, v___x_997_, v_____do__lift_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
stack->m_obj
 = v_res_1008_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v_____do__lift_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v___x_4165__boxed_1017_; uint8_t v___x_4166__boxed_1018_; uint8_t v_____do__lift_4167__boxed_1019_; lean_object* v_res_1020_; 
v___x_4165__boxed_1017_ = lean_unbox(v___x_1009_);
v___x_4166__boxed_1018_ = lean_unbox(v___x_1010_);
v_____do__lift_4167__boxed_1019_ = lean_unbox(v_____do__lift_1011_);
v_res_1020_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_4165__boxed_1017_, v___x_4166__boxed_1018_, v_____do__lift_4167__boxed_1019_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1020_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object* v_as_1021_, size_t v_i_1022_, size_t v_stop_1023_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1021_ = stack[0].m_obj;
size_t v_i_1022_ = stack[1].m_num;
size_t v_stop_1023_ = stack[2].m_num;
uint8_t v_res_1033_;
v_res_1033_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_as_1021_, v_i_1022_, v_stop_1023_);
stack->m_num = v_res_1033_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object* v_as_1034_, lean_object* v_i_1035_, lean_object* v_stop_1036_){
_start:
{
size_t v_i_boxed_1037_; size_t v_stop_boxed_1038_; uint8_t v_res_1039_; lean_object* v_r_1040_; 
v_i_boxed_1037_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_stop_boxed_1038_ = lean_unbox_usize(v_stop_1036_);
lean_dec(v_stop_1036_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_as_1034_, v_i_boxed_1037_, v_stop_boxed_1038_);
lean_dec_ref(v_as_1034_);
v_r_1040_ = lean_box(v_res_1039_);
return v_r_1040_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t v_sz_1041_, size_t v_i_1042_, lean_object* v_bs_1043_){
_start:
{
uint8_t v___x_1044_; 
v___x_1044_ = lean_usize_dec_lt(v_i_1042_, v_sz_1041_);
if (v___x_1044_ == 0)
{
return v_bs_1043_;
}
else
{
lean_object* v_v_1045_; lean_object* v_declName_1046_; lean_object* v___x_1047_; lean_object* v_bs_x27_1048_; size_t v___x_1049_; size_t v___x_1050_; lean_object* v___x_1051_; 
v_v_1045_ = lean_array_uget_borrowed(v_bs_1043_, v_i_1042_);
v_declName_1046_ = lean_ctor_get(v_v_1045_, 3);
lean_inc(v_declName_1046_);
v___x_1047_ = lean_unsigned_to_nat(0u);
v_bs_x27_1048_ = lean_array_uset(v_bs_1043_, v_i_1042_, v___x_1047_);
v___x_1049_ = ((size_t)1ULL);
v___x_1050_ = lean_usize_add(v_i_1042_, v___x_1049_);
v___x_1051_ = lean_array_uset(v_bs_x27_1048_, v_i_1042_, v_declName_1046_);
v_i_1042_ = v___x_1050_;
v_bs_1043_ = v___x_1051_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1041_ = stack[0].m_num;
size_t v_i_1042_ = stack[1].m_num;
lean_object* v_bs_1043_ = stack[2].m_obj;
lean_object* v_res_1053_;
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_1041_, v_i_1042_, v_bs_1043_);
stack->m_obj
 = v_res_1053_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object* v_sz_1054_, lean_object* v_i_1055_, lean_object* v_bs_1056_){
_start:
{
size_t v_sz_boxed_1057_; size_t v_i_boxed_1058_; lean_object* v_res_1059_; 
v_sz_boxed_1057_ = lean_unbox_usize(v_sz_1054_);
lean_dec(v_sz_1054_);
v_i_boxed_1058_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_res_1059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_boxed_1057_, v_i_boxed_1058_, v_bs_1056_);
return v_res_1059_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object* v___x_1060_, lean_object* v_declNameNonRec_1061_, lean_object* v_fixedParamPerms_1062_, lean_object* v_fixpointType_1063_, lean_object* v_fixEq_x3f_1064_, uint8_t v_a_1065_, lean_object* v_as_1066_, size_t v_i_1067_, size_t v_stop_1068_, lean_object* v_b_1069_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_usize_dec_eq(v_i_1067_, v_stop_1068_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v_levelParams_1072_; lean_object* v_declName_1073_; lean_object* v_type_1074_; lean_object* v_value_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; size_t v___x_1079_; size_t v___x_1080_; 
v___x_1071_ = lean_array_uget_borrowed(v_as_1066_, v_i_1067_);
v_levelParams_1072_ = lean_ctor_get(v___x_1071_, 1);
v_declName_1073_ = lean_ctor_get(v___x_1071_, 3);
v_type_1074_ = lean_ctor_get(v___x_1071_, 6);
v_value_1075_ = lean_ctor_get(v___x_1071_, 7);
v___x_1076_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
lean_inc(v_fixEq_x3f_1064_);
lean_inc_ref(v_fixpointType_1063_);
lean_inc_ref(v_fixedParamPerms_1062_);
lean_inc(v_declNameNonRec_1061_);
lean_inc_ref(v___x_1060_);
lean_inc_ref(v_value_1075_);
lean_inc_ref(v_type_1074_);
lean_inc(v_levelParams_1072_);
lean_inc_n(v_declName_1073_, 2);
v___x_1077_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1077_, 0, v_declName_1073_);
lean_ctor_set(v___x_1077_, 1, v_levelParams_1072_);
lean_ctor_set(v___x_1077_, 2, v_type_1074_);
lean_ctor_set(v___x_1077_, 3, v_value_1075_);
lean_ctor_set(v___x_1077_, 4, v___x_1060_);
lean_ctor_set(v___x_1077_, 5, v_declNameNonRec_1061_);
lean_ctor_set(v___x_1077_, 6, v_fixedParamPerms_1062_);
lean_ctor_set(v___x_1077_, 7, v_fixpointType_1063_);
lean_ctor_set(v___x_1077_, 8, v_fixEq_x3f_1064_);
v___x_1078_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1076_, v_b_1069_, v_declName_1073_, v___x_1077_, v_a_1065_);
v___x_1079_ = ((size_t)1ULL);
v___x_1080_ = lean_usize_add(v_i_1067_, v___x_1079_);
v_i_1067_ = v___x_1080_;
v_b_1069_ = v___x_1078_;
goto _start;
}
else
{
lean_dec(v_fixEq_x3f_1064_);
lean_dec_ref(v_fixpointType_1063_);
lean_dec_ref(v_fixedParamPerms_1062_);
lean_dec(v_declNameNonRec_1061_);
lean_dec_ref(v___x_1060_);
return v_b_1069_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1060_ = stack[0].m_obj;
lean_object* v_declNameNonRec_1061_ = stack[1].m_obj;
lean_object* v_fixedParamPerms_1062_ = stack[2].m_obj;
lean_object* v_fixpointType_1063_ = stack[3].m_obj;
lean_object* v_fixEq_x3f_1064_ = stack[4].m_obj;
uint8_t v_a_1065_ = stack[5].m_num;
lean_object* v_as_1066_ = stack[6].m_obj;
size_t v_i_1067_ = stack[7].m_num;
size_t v_stop_1068_ = stack[8].m_num;
lean_object* v_b_1069_ = stack[9].m_obj;
lean_object* v_res_1082_;
v_res_1082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_1060_, v_declNameNonRec_1061_, v_fixedParamPerms_1062_, v_fixpointType_1063_, v_fixEq_x3f_1064_, v_a_1065_, v_as_1066_, v_i_1067_, v_stop_1068_, v_b_1069_);
stack->m_obj
 = v_res_1082_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object* v___x_1083_, lean_object* v_declNameNonRec_1084_, lean_object* v_fixedParamPerms_1085_, lean_object* v_fixpointType_1086_, lean_object* v_fixEq_x3f_1087_, lean_object* v_a_1088_, lean_object* v_as_1089_, lean_object* v_i_1090_, lean_object* v_stop_1091_, lean_object* v_b_1092_){
_start:
{
uint8_t v_a_4260__boxed_1093_; size_t v_i_boxed_1094_; size_t v_stop_boxed_1095_; lean_object* v_res_1096_; 
v_a_4260__boxed_1093_ = lean_unbox(v_a_1088_);
v_i_boxed_1094_ = lean_unbox_usize(v_i_1090_);
lean_dec(v_i_1090_);
v_stop_boxed_1095_ = lean_unbox_usize(v_stop_1091_);
lean_dec(v_stop_1091_);
v_res_1096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_1083_, v_declNameNonRec_1084_, v_fixedParamPerms_1085_, v_fixpointType_1086_, v_fixEq_x3f_1087_, v_a_4260__boxed_1093_, v_as_1089_, v_i_boxed_1094_, v_stop_boxed_1095_, v_b_1092_);
lean_dec_ref(v_as_1089_);
return v_res_1096_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object* v_as_1097_, size_t v_i_1098_, size_t v_stop_1099_, lean_object* v_b_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_usize_dec_eq(v_i_1098_, v_stop_1099_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v_declName_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_array_uget_borrowed(v_as_1097_, v_i_1098_);
v_declName_1106_ = lean_ctor_get(v___x_1105_, 3);
lean_inc(v_declName_1106_);
v___x_1107_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_1106_, v___y_1101_, v___y_1102_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; size_t v___x_1109_; size_t v___x_1110_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1107_, 1);
v___x_1109_ = ((size_t)1ULL);
v___x_1110_ = lean_usize_add(v_i_1098_, v___x_1109_);
v_i_1098_ = v___x_1110_;
v_b_1100_ = v_a_1108_;
goto _start;
}
else
{
return v___x_1107_;
}
}
else
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_b_1100_);
return v___x_1112_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1097_ = stack[0].m_obj;
size_t v_i_1098_ = stack[1].m_num;
size_t v_stop_1099_ = stack[2].m_num;
lean_object* v_b_1100_ = stack[3].m_obj;
lean_object* v___y_1101_ = stack[4].m_obj;
lean_object* v___y_1102_ = stack[5].m_obj;
lean_object* v_res_1113_;
v_res_1113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_1097_, v_i_1098_, v_stop_1099_, v_b_1100_, v___y_1101_, v___y_1102_);
stack->m_obj
 = v_res_1113_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object* v_as_1114_, lean_object* v_i_1115_, lean_object* v_stop_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
size_t v_i_boxed_1121_; size_t v_stop_boxed_1122_; lean_object* v_res_1123_; 
v_i_boxed_1121_ = lean_unbox_usize(v_i_1115_);
lean_dec(v_i_1115_);
v_stop_boxed_1122_ = lean_unbox_usize(v_stop_1116_);
lean_dec(v_stop_1116_);
v_res_1123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_1114_, v_i_boxed_1121_, v_stop_boxed_1122_, v_b_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec_ref(v_as_1114_);
return v_res_1123_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t v___x_1124_, lean_object* v_as_1125_, size_t v_i_1126_, size_t v_stop_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_usize_dec_eq(v_i_1126_, v_stop_1127_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v_type_1139_; uint8_t v___x_1140_; uint8_t v_a_1142_; lean_object* v___x_1145_; 
v___x_1138_ = lean_array_uget_borrowed(v_as_1125_, v_i_1126_);
v_type_1139_ = lean_ctor_get(v___x_1138_, 6);
v___x_1140_ = 1;
lean_inc_ref(v_type_1139_);
v___x_1145_ = l_Lean_Meta_isProp(v_type_1139_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; uint8_t v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = lean_unbox(v_a_1146_);
lean_dec(v_a_1146_);
if (v___x_1147_ == 0)
{
v_a_1142_ = v___x_1124_;
goto v___jp_1141_;
}
else
{
goto v___jp_1133_;
}
}
else
{
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1148_; uint8_t v___x_1149_; 
v_a_1148_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1149_ = lean_unbox(v_a_1148_);
lean_dec(v_a_1148_);
v_a_1142_ = v___x_1149_;
goto v___jp_1141_;
}
else
{
return v___x_1145_;
}
}
v___jp_1141_:
{
if (v_a_1142_ == 0)
{
goto v___jp_1133_;
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_box(v___x_1140_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
}
else
{
uint8_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = 0;
v___x_1151_ = lean_box(v___x_1150_);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
v___jp_1133_:
{
size_t v___x_1134_; size_t v___x_1135_; 
v___x_1134_ = ((size_t)1ULL);
v___x_1135_ = lean_usize_add(v_i_1126_, v___x_1134_);
v_i_1126_ = v___x_1135_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1124_ = stack[0].m_num;
lean_object* v_as_1125_ = stack[1].m_obj;
size_t v_i_1126_ = stack[2].m_num;
size_t v_stop_1127_ = stack[3].m_num;
lean_object* v___y_1128_ = stack[4].m_obj;
lean_object* v___y_1129_ = stack[5].m_obj;
lean_object* v___y_1130_ = stack[6].m_obj;
lean_object* v___y_1131_ = stack[7].m_obj;
lean_object* v_res_1153_;
v_res_1153_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_1124_, v_as_1125_, v_i_1126_, v_stop_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
stack->m_obj
 = v_res_1153_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object* v___x_1154_, lean_object* v_as_1155_, lean_object* v_i_1156_, lean_object* v_stop_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
uint8_t v___x_4333__boxed_1163_; size_t v_i_boxed_1164_; size_t v_stop_boxed_1165_; lean_object* v_res_1166_; 
v___x_4333__boxed_1163_ = lean_unbox(v___x_1154_);
v_i_boxed_1164_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_stop_boxed_1165_ = lean_unbox_usize(v_stop_1157_);
lean_dec(v_stop_1157_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_4333__boxed_1163_, v_as_1155_, v_i_boxed_1164_, v_stop_boxed_1165_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v_as_1155_);
return v_res_1166_;
}
}
lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object* v_preDefs_1167_, lean_object* v_declNameNonRec_1168_, lean_object* v_fixedParamPerms_1169_, lean_object* v_fixpointType_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___y_1180_; lean_object* v_nextMacroScope_1181_; lean_object* v_ngen_1182_; lean_object* v_auxDeclNGen_1183_; lean_object* v_traceState_1184_; lean_object* v_recordedDeps_1185_; lean_object* v_messages_1186_; lean_object* v_infoState_1187_; lean_object* v_snapshotTasks_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; size_t v___y_1218_; lean_object* v___y_1219_; uint8_t v___y_1220_; lean_object* v_fixEq_x3f_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1241_; lean_object* v___y_1284_; uint8_t v___x_1285_; 
v___x_1214_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_array_get_size(v_preDefs_1167_);
v___x_1285_ = lean_nat_dec_lt(v___x_1215_, v___x_1216_);
if (v___x_1285_ == 0)
{
goto v___jp_1272_;
}
else
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = lean_box(0);
v___x_1287_ = lean_nat_dec_le(v___x_1216_, v___x_1216_);
if (v___x_1287_ == 0)
{
if (v___x_1285_ == 0)
{
goto v___jp_1272_;
}
else
{
size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = lean_usize_of_nat(v___x_1216_);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_1167_, v___x_1288_, v___x_1289_, v___x_1286_, v_a_1173_, v_a_1174_);
v___y_1284_ = v___x_1290_;
goto v___jp_1283_;
}
}
else
{
size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = ((size_t)0ULL);
v___x_1292_ = lean_usize_of_nat(v___x_1216_);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_1167_, v___x_1291_, v___x_1292_, v___x_1286_, v_a_1173_, v_a_1174_);
v___y_1284_ = v___x_1293_;
goto v___jp_1283_;
}
}
v___jp_1176_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
v___jp_1179_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v_mctx_1195_; lean_object* v_zetaDeltaFVarIds_1196_; lean_object* v_postponed_1197_; lean_object* v_diag_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1209_; 
v___x_1191_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
v___x_1192_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1192_, 0, v___y_1190_);
lean_ctor_set(v___x_1192_, 1, v_nextMacroScope_1181_);
lean_ctor_set(v___x_1192_, 2, v_ngen_1182_);
lean_ctor_set(v___x_1192_, 3, v_auxDeclNGen_1183_);
lean_ctor_set(v___x_1192_, 4, v_traceState_1184_);
lean_ctor_set(v___x_1192_, 5, v___x_1191_);
lean_ctor_set(v___x_1192_, 6, v_recordedDeps_1185_);
lean_ctor_set(v___x_1192_, 7, v_messages_1186_);
lean_ctor_set(v___x_1192_, 8, v_infoState_1187_);
lean_ctor_set(v___x_1192_, 9, v_snapshotTasks_1188_);
v___x_1193_ = lean_st_ref_put(v___y_1189_, v___x_1192_);
v___x_1194_ = lean_st_ref_take(v___y_1180_);
v_mctx_1195_ = lean_ctor_get(v___x_1194_, 0);
v_zetaDeltaFVarIds_1196_ = lean_ctor_get(v___x_1194_, 2);
v_postponed_1197_ = lean_ctor_get(v___x_1194_, 3);
v_diag_1198_ = lean_ctor_get(v___x_1194_, 4);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v___x_1194_, 1);
lean_dec(v_unused_1210_);
v___x_1200_ = v___x_1194_;
v_isShared_1201_ = v_isSharedCheck_1209_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_diag_1198_);
lean_inc(v_postponed_1197_);
lean_inc(v_zetaDeltaFVarIds_1196_);
lean_inc(v_mctx_1195_);
lean_dec(v___x_1194_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1209_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__3);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v___x_1203_);
v___x_1205_ = v___x_1200_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_mctx_1195_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_zetaDeltaFVarIds_1196_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_postponed_1197_);
lean_ctor_set(v_reuseFailAlloc_1208_, 4, v_diag_1198_);
v___x_1205_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_st_ref_put(v___y_1180_, v___x_1205_);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1202_);
return v___x_1207_;
}
}
}
v___jp_1211_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
v___jp_1217_:
{
lean_object* v___x_1224_; lean_object* v_env_1225_; lean_object* v_nextMacroScope_1226_; lean_object* v_ngen_1227_; lean_object* v_auxDeclNGen_1228_; lean_object* v_traceState_1229_; lean_object* v_recordedDeps_1230_; lean_object* v_messages_1231_; lean_object* v_infoState_1232_; lean_object* v_snapshotTasks_1233_; uint8_t v___x_1234_; 
v___x_1224_ = lean_st_ref_take(v___y_1223_);
v_env_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc_ref(v_env_1225_);
v_nextMacroScope_1226_ = lean_ctor_get(v___x_1224_, 1);
lean_inc(v_nextMacroScope_1226_);
v_ngen_1227_ = lean_ctor_get(v___x_1224_, 2);
lean_inc_ref(v_ngen_1227_);
v_auxDeclNGen_1228_ = lean_ctor_get(v___x_1224_, 3);
lean_inc_ref(v_auxDeclNGen_1228_);
v_traceState_1229_ = lean_ctor_get(v___x_1224_, 4);
lean_inc_ref(v_traceState_1229_);
v_recordedDeps_1230_ = lean_ctor_get(v___x_1224_, 6);
lean_inc_ref(v_recordedDeps_1230_);
v_messages_1231_ = lean_ctor_get(v___x_1224_, 7);
lean_inc_ref(v_messages_1231_);
v_infoState_1232_ = lean_ctor_get(v___x_1224_, 8);
lean_inc_ref(v_infoState_1232_);
v_snapshotTasks_1233_ = lean_ctor_get(v___x_1224_, 9);
lean_inc_ref(v_snapshotTasks_1233_);
lean_dec(v___x_1224_);
v___x_1234_ = lean_nat_dec_lt(v___x_1215_, v___x_1216_);
if (v___x_1234_ == 0)
{
lean_dec(v_fixEq_x3f_1221_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_fixpointType_1170_);
lean_dec_ref(v_fixedParamPerms_1169_);
lean_dec(v_declNameNonRec_1168_);
lean_dec_ref(v_preDefs_1167_);
v___y_1180_ = v___y_1222_;
v_nextMacroScope_1181_ = v_nextMacroScope_1226_;
v_ngen_1182_ = v_ngen_1227_;
v_auxDeclNGen_1183_ = v_auxDeclNGen_1228_;
v_traceState_1184_ = v_traceState_1229_;
v_recordedDeps_1185_ = v_recordedDeps_1230_;
v_messages_1186_ = v_messages_1231_;
v_infoState_1187_ = v_infoState_1232_;
v_snapshotTasks_1188_ = v_snapshotTasks_1233_;
v___y_1189_ = v___y_1223_;
v___y_1190_ = v_env_1225_;
goto v___jp_1179_;
}
else
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_nat_dec_le(v___x_1216_, v___x_1216_);
if (v___x_1235_ == 0)
{
if (v___x_1234_ == 0)
{
lean_dec(v_fixEq_x3f_1221_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_fixpointType_1170_);
lean_dec_ref(v_fixedParamPerms_1169_);
lean_dec(v_declNameNonRec_1168_);
lean_dec_ref(v_preDefs_1167_);
v___y_1180_ = v___y_1222_;
v_nextMacroScope_1181_ = v_nextMacroScope_1226_;
v_ngen_1182_ = v_ngen_1227_;
v_auxDeclNGen_1183_ = v_auxDeclNGen_1228_;
v_traceState_1184_ = v_traceState_1229_;
v_recordedDeps_1185_ = v_recordedDeps_1230_;
v_messages_1186_ = v_messages_1231_;
v_infoState_1187_ = v_infoState_1232_;
v_snapshotTasks_1188_ = v_snapshotTasks_1233_;
v___y_1189_ = v___y_1223_;
v___y_1190_ = v_env_1225_;
goto v___jp_1179_;
}
else
{
size_t v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_usize_of_nat(v___x_1216_);
v___x_1237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___y_1219_, v_declNameNonRec_1168_, v_fixedParamPerms_1169_, v_fixpointType_1170_, v_fixEq_x3f_1221_, v___y_1220_, v_preDefs_1167_, v___y_1218_, v___x_1236_, v_env_1225_);
lean_dec_ref(v_preDefs_1167_);
v___y_1180_ = v___y_1222_;
v_nextMacroScope_1181_ = v_nextMacroScope_1226_;
v_ngen_1182_ = v_ngen_1227_;
v_auxDeclNGen_1183_ = v_auxDeclNGen_1228_;
v_traceState_1184_ = v_traceState_1229_;
v_recordedDeps_1185_ = v_recordedDeps_1230_;
v_messages_1186_ = v_messages_1231_;
v_infoState_1187_ = v_infoState_1232_;
v_snapshotTasks_1188_ = v_snapshotTasks_1233_;
v___y_1189_ = v___y_1223_;
v___y_1190_ = v___x_1237_;
goto v___jp_1179_;
}
}
else
{
size_t v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_usize_of_nat(v___x_1216_);
v___x_1239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___y_1219_, v_declNameNonRec_1168_, v_fixedParamPerms_1169_, v_fixpointType_1170_, v_fixEq_x3f_1221_, v___y_1220_, v_preDefs_1167_, v___y_1218_, v___x_1238_, v_env_1225_);
lean_dec_ref(v_preDefs_1167_);
v___y_1180_ = v___y_1222_;
v_nextMacroScope_1181_ = v_nextMacroScope_1226_;
v_ngen_1182_ = v_ngen_1227_;
v_auxDeclNGen_1183_ = v_auxDeclNGen_1228_;
v_traceState_1184_ = v_traceState_1229_;
v_recordedDeps_1185_ = v_recordedDeps_1230_;
v_messages_1186_ = v_messages_1231_;
v_infoState_1187_ = v_infoState_1232_;
v_snapshotTasks_1188_ = v_snapshotTasks_1233_;
v___y_1189_ = v___y_1223_;
v___y_1190_ = v___x_1239_;
goto v___jp_1179_;
}
}
}
v___jp_1240_:
{
if (lean_obj_tag(v___y_1241_) == 0)
{
lean_object* v_a_1242_; uint8_t v___x_1243_; 
v_a_1242_ = lean_ctor_get(v___y_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___y_1241_, 1);
v___x_1243_ = lean_unbox(v_a_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v_declName_1245_; size_t v_sz_1246_; size_t v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1244_ = lean_array_get_borrowed(v___x_1214_, v_preDefs_1167_, v___x_1215_);
v_declName_1245_ = lean_ctor_get(v___x_1244_, 3);
v_sz_1246_ = lean_array_size(v_preDefs_1167_);
v___x_1247_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_1167_);
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_1246_, v___x_1247_, v_preDefs_1167_);
v___x_1249_ = lean_name_eq(v_declNameNonRec_1168_, v_declName_1245_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; 
lean_inc(v_declNameNonRec_1168_);
v___x_1250_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq(v_declNameNonRec_1168_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v___x_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_a_1251_);
v___x_1253_ = lean_unbox(v_a_1242_);
lean_dec(v_a_1242_);
v___y_1218_ = v___x_1247_;
v___y_1219_ = v___x_1248_;
v___y_1220_ = v___x_1253_;
v_fixEq_x3f_1221_ = v___x_1252_;
v___y_1222_ = v_a_1172_;
v___y_1223_ = v_a_1174_;
goto v___jp_1217_;
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v___x_1248_);
lean_dec(v_a_1242_);
lean_dec_ref(v_fixpointType_1170_);
lean_dec_ref(v_fixedParamPerms_1169_);
lean_dec(v_declNameNonRec_1168_);
lean_dec_ref(v_preDefs_1167_);
v_a_1254_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1250_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1250_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = lean_box(0);
v___x_1263_ = lean_unbox(v_a_1242_);
lean_dec(v_a_1242_);
v___y_1218_ = v___x_1247_;
v___y_1219_ = v___x_1248_;
v___y_1220_ = v___x_1263_;
v_fixEq_x3f_1221_ = v___x_1262_;
v___y_1222_ = v_a_1172_;
v___y_1223_ = v_a_1174_;
goto v___jp_1217_;
}
}
else
{
lean_dec(v_a_1242_);
lean_dec_ref(v_fixpointType_1170_);
lean_dec_ref(v_fixedParamPerms_1169_);
lean_dec(v_declNameNonRec_1168_);
lean_dec_ref(v_preDefs_1167_);
goto v___jp_1176_;
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_fixpointType_1170_);
lean_dec_ref(v_fixedParamPerms_1169_);
lean_dec(v_declNameNonRec_1168_);
lean_dec_ref(v_preDefs_1167_);
v_a_1264_ = lean_ctor_get(v___y_1241_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___y_1241_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___y_1241_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___y_1241_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
v___jp_1272_:
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_nat_dec_lt(v___x_1215_, v___x_1216_);
if (v___x_1273_ == 0)
{
lean_dec_ref(v_fixpointType_1170_);
lean_dec_ref(v_fixedParamPerms_1169_);
lean_dec(v_declNameNonRec_1168_);
lean_dec_ref(v_preDefs_1167_);
goto v___jp_1211_;
}
else
{
if (v___x_1273_ == 0)
{
lean_dec_ref(v_fixpointType_1170_);
lean_dec_ref(v_fixedParamPerms_1169_);
lean_dec(v_declNameNonRec_1168_);
lean_dec_ref(v_preDefs_1167_);
goto v___jp_1211_;
}
else
{
size_t v___x_1274_; size_t v___x_1275_; uint8_t v___x_1276_; 
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = lean_usize_of_nat(v___x_1216_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_preDefs_1167_, v___x_1274_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_dec_ref(v_fixpointType_1170_);
lean_dec_ref(v_fixedParamPerms_1169_);
lean_dec(v_declNameNonRec_1168_);
lean_dec_ref(v_preDefs_1167_);
goto v___jp_1211_;
}
else
{
uint8_t v___x_1277_; 
v___x_1277_ = 0;
if (v___x_1273_ == 0)
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_1276_, v___x_1277_, v___x_1273_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
v___y_1241_ = v___x_1278_;
goto v___jp_1240_;
}
else
{
if (v___x_1273_ == 0)
{
lean_dec_ref(v_fixpointType_1170_);
lean_dec_ref(v_fixedParamPerms_1169_);
lean_dec(v_declNameNonRec_1168_);
lean_dec_ref(v_preDefs_1167_);
goto v___jp_1176_;
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_1276_, v_preDefs_1167_, v___x_1274_, v___x_1275_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = lean_unbox(v_a_1280_);
lean_dec(v_a_1280_);
v___x_1282_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(v___x_1276_, v___x_1277_, v___x_1281_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
v___y_1241_ = v___x_1282_;
goto v___jp_1240_;
}
else
{
v___y_1241_ = v___x_1279_;
goto v___jp_1240_;
}
}
}
}
}
}
}
v___jp_1283_:
{
if (lean_obj_tag(v___y_1284_) == 0)
{
lean_dec_ref_known(v___y_1284_, 1);
goto v___jp_1272_;
}
else
{
lean_dec_ref(v_fixpointType_1170_);
lean_dec_ref(v_fixedParamPerms_1169_);
lean_dec(v_declNameNonRec_1168_);
lean_dec_ref(v_preDefs_1167_);
return v___y_1284_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_PartialFixpoint_registerEqnsInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_1167_ = stack[0].m_obj;
lean_object* v_declNameNonRec_1168_ = stack[1].m_obj;
lean_object* v_fixedParamPerms_1169_ = stack[2].m_obj;
lean_object* v_fixpointType_1170_ = stack[3].m_obj;
lean_object* v_a_1171_ = stack[4].m_obj;
lean_object* v_a_1172_ = stack[5].m_obj;
lean_object* v_a_1173_ = stack[6].m_obj;
lean_object* v_a_1174_ = stack[7].m_obj;
lean_object* v_res_1294_;
v_res_1294_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_preDefs_1167_, v_declNameNonRec_1168_, v_fixedParamPerms_1169_, v_fixpointType_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
stack->m_obj
 = v_res_1294_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(lean_object* v_preDefs_1295_, lean_object* v_declNameNonRec_1296_, lean_object* v_fixedParamPerms_1297_, lean_object* v_fixpointType_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_preDefs_1295_, v_declNameNonRec_1296_, v_fixedParamPerms_1297_, v_fixpointType_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
return v_res_1304_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object* v_as_1305_, size_t v_i_1306_, size_t v_stop_1307_, lean_object* v_b_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_1305_, v_i_1306_, v_stop_1307_, v_b_1308_, v___y_1311_, v___y_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1305_ = stack[0].m_obj;
size_t v_i_1306_ = stack[1].m_num;
size_t v_stop_1307_ = stack[2].m_num;
lean_object* v_b_1308_ = stack[3].m_obj;
lean_object* v___y_1309_ = stack[4].m_obj;
lean_object* v___y_1310_ = stack[5].m_obj;
lean_object* v___y_1311_ = stack[6].m_obj;
lean_object* v___y_1312_ = stack[7].m_obj;
lean_object* v_res_1315_;
v_res_1315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(v_as_1305_, v_i_1306_, v_stop_1307_, v_b_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
stack->m_obj
 = v_res_1315_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object* v_as_1316_, lean_object* v_i_1317_, lean_object* v_stop_1318_, lean_object* v_b_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
size_t v_i_boxed_1325_; size_t v_stop_boxed_1326_; lean_object* v_res_1327_; 
v_i_boxed_1325_ = lean_unbox_usize(v_i_1317_);
lean_dec(v_i_1317_);
v_stop_boxed_1326_ = lean_unbox_usize(v_stop_1318_);
lean_dec(v_stop_1318_);
v_res_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(v_as_1316_, v_i_boxed_1325_, v_stop_boxed_1326_, v_b_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v_as_1316_);
return v_res_1327_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(lean_object* v_mvarId_1328_, lean_object* v_x_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1328_, v_x_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
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
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
v_a_1344_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1335_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1335_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1328_ = stack[0].m_obj;
lean_object* v_x_1329_ = stack[1].m_obj;
lean_object* v___y_1330_ = stack[2].m_obj;
lean_object* v___y_1331_ = stack[3].m_obj;
lean_object* v___y_1332_ = stack[4].m_obj;
lean_object* v___y_1333_ = stack[5].m_obj;
lean_object* v_res_1352_;
v_res_1352_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1328_, v_x_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
stack->m_obj
 = v_res_1352_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg___boxed(lean_object* v_mvarId_1353_, lean_object* v_x_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1353_, v_x_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1360_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(lean_object* v_00_u03b1_1361_, lean_object* v_mvarId_1362_, lean_object* v_x_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1362_, v_x_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1362_ = stack[1].m_obj;
lean_object* v_x_1363_ = stack[2].m_obj;
lean_object* v___y_1364_ = stack[3].m_obj;
lean_object* v___y_1365_ = stack[4].m_obj;
lean_object* v___y_1366_ = stack[5].m_obj;
lean_object* v___y_1367_ = stack[6].m_obj;
lean_object* v_res_1370_;
v_res_1370_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(lean_box(0), v_mvarId_1362_, v_x_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
stack->m_obj
 = v_res_1370_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(lean_object* v_00_u03b1_1371_, lean_object* v_mvarId_1372_, lean_object* v_x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(v_00_u03b1_1371_, v_mvarId_1372_, v_x_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1379_;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object* v_declName_1380_, lean_object* v_declNameNonRec_1381_, lean_object* v_n_1382_){
_start:
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_name_eq(v_n_1382_, v_declName_1380_);
if (v___x_1383_ == 0)
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_name_eq(v_n_1382_, v_declNameNonRec_1381_);
return v___x_1384_;
}
else
{
return v___x_1383_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1380_ = stack[0].m_obj;
lean_object* v_declNameNonRec_1381_ = stack[1].m_obj;
lean_object* v_n_1382_ = stack[2].m_obj;
uint8_t v_res_1385_;
v_res_1385_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(v_declName_1380_, v_declNameNonRec_1381_, v_n_1382_);
stack->m_num = v_res_1385_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object* v_declName_1386_, lean_object* v_declNameNonRec_1387_, lean_object* v_n_1388_){
_start:
{
uint8_t v_res_1389_; lean_object* v_r_1390_; 
v_res_1389_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(v_declName_1386_, v_declNameNonRec_1387_, v_n_1388_);
lean_dec(v_n_1388_);
lean_dec(v_declNameNonRec_1387_);
lean_dec(v_declName_1386_);
v_r_1390_ = lean_box(v_res_1389_);
return v_r_1390_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5));
v___x_1401_ = l_Lean_MessageData_ofFormat(v___x_1400_);
return v___x_1401_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6);
v___x_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
return v___x_1403_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object* v_mvarId_1404_, lean_object* v___f_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
lean_inc(v_mvarId_1404_);
v___x_1411_ = l_Lean_MVarId_getType_x27(v_mvarId_1404_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1413_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_1414_ = lean_unsigned_to_nat(3u);
v___x_1415_ = l_Lean_Expr_isAppOfArity(v_a_1412_, v___x_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec(v_a_1412_);
lean_dec_ref(v___f_1405_);
v___x_1416_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3));
v___x_1417_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7);
v___x_1418_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1416_, v_mvarId_1404_, v___x_1417_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; 
v___x_1419_ = l_Lean_Expr_appFn_x21(v_a_1412_);
v___x_1420_ = l_Lean_Expr_appArg_x21(v___x_1419_);
lean_dec_ref(v___x_1419_);
v___x_1421_ = l_Lean_Expr_appArg_x21(v_a_1412_);
lean_dec(v_a_1412_);
v___x_1422_ = 0;
v___x_1423_ = l_Lean_Meta_deltaExpand(v___x_1420_, v___f_1405_, v___x_1422_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = l_Lean_Meta_mkEq(v_a_1424_, v___x_1421_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1404_, v_a_1426_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1427_;
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_mvarId_1404_);
v_a_1428_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1425_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1425_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
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
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v___x_1421_);
lean_dec(v_mvarId_1404_);
v_a_1436_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1423_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1423_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec_ref(v___f_1405_);
lean_dec(v_mvarId_1404_);
v_a_1444_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1411_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1411_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1404_ = stack[0].m_obj;
lean_object* v___f_1405_ = stack[1].m_obj;
lean_object* v___y_1406_ = stack[2].m_obj;
lean_object* v___y_1407_ = stack[3].m_obj;
lean_object* v___y_1408_ = stack[4].m_obj;
lean_object* v___y_1409_ = stack[5].m_obj;
lean_object* v_res_1452_;
v_res_1452_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(v_mvarId_1404_, v___f_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
stack->m_obj
 = v_res_1452_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed(lean_object* v_mvarId_1453_, lean_object* v___f_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(v_mvarId_1453_, v___f_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v_res_1460_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object* v_declName_1461_, lean_object* v_declNameNonRec_1462_, lean_object* v_mvarId_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v___f_1469_; lean_object* v___f_1470_; lean_object* v___x_1471_; 
v___f_1469_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1469_, 0, v_declName_1461_);
lean_closure_set(v___f_1469_, 1, v_declNameNonRec_1462_);
lean_inc(v_mvarId_1463_);
v___f_1470_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1470_, 0, v_mvarId_1463_);
lean_closure_set(v___f_1470_, 1, v___f_1469_);
v___x_1471_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1463_, v___f_1470_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
return v___x_1471_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1461_ = stack[0].m_obj;
lean_object* v_declNameNonRec_1462_ = stack[1].m_obj;
lean_object* v_mvarId_1463_ = stack[2].m_obj;
lean_object* v_a_1464_ = stack[3].m_obj;
lean_object* v_a_1465_ = stack[4].m_obj;
lean_object* v_a_1466_ = stack[5].m_obj;
lean_object* v_a_1467_ = stack[6].m_obj;
lean_object* v_res_1472_;
v_res_1472_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_1461_, v_declNameNonRec_1462_, v_mvarId_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
stack->m_obj
 = v_res_1472_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(lean_object* v_declName_1473_, lean_object* v_declNameNonRec_1474_, lean_object* v_mvarId_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_1473_, v_declNameNonRec_1474_, v_mvarId_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(lean_object* v_msg_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = l_Lean_instInhabitedExpr;
v___x_1484_ = lean_panic_fn_borrowed(v___x_1483_, v_msg_1482_);
return v___x_1484_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0));
v___x_1487_ = l_Lean_stringToMessageData(v___x_1486_);
return v___x_1487_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = l_Lean_Expr_bvar___override(v___x_1494_);
return v___x_1495_;
}
}
static size_t _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7(void){
_start:
{
lean_object* v___x_1496_; size_t v___x_1497_; 
v___x_1496_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
v___x_1497_ = lean_ptr_addr(v___x_1496_);
return v___x_1497_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10));
v___x_1502_ = lean_unsigned_to_nat(18u);
v___x_1503_ = lean_unsigned_to_nat(1913u);
v___x_1504_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9));
v___x_1505_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8));
v___x_1506_ = l_mkPanicMessageWithDecl(v___x_1505_, v___x_1504_, v___x_1503_, v___x_1502_, v___x_1501_);
return v___x_1506_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(lean_object* v_lhs_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__6));
v___x_1517_ = lean_unsigned_to_nat(4u);
v___x_1518_ = l_Lean_Expr_isAppOfArity(v_lhs_1510_, v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__0___closed__8));
v___x_1520_ = l_Lean_Expr_isAppOfArity(v_lhs_1510_, v___x_1519_, v___x_1517_);
if (v___x_1520_ == 0)
{
uint8_t v___x_1521_; 
v___x_1521_ = l_Lean_Expr_isApp(v_lhs_1510_);
if (v___x_1521_ == 0)
{
uint8_t v___x_1522_; 
v___x_1522_ = l_Lean_Expr_isProj(v_lhs_1510_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1);
v___x_1524_ = l_Lean_MessageData_ofExpr(v_lhs_1510_);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_1525_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1526_;
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = l_Lean_Expr_projExpr_x21(v_lhs_1510_);
lean_inc(v_a_1514_);
lean_inc_ref(v_a_1513_);
lean_inc(v_a_1512_);
lean_inc_ref(v_a_1511_);
lean_inc_ref(v___x_1527_);
v___x_1528_ = lean_infer_type(v___x_1527_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; lean_object* v___y_1533_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3));
v___x_1531_ = 0;
if (lean_obj_tag(v_lhs_1510_) == 11)
{
lean_object* v_typeName_1543_; lean_object* v_idx_1544_; lean_object* v_struct_1545_; lean_object* v___x_1546_; size_t v___x_1547_; size_t v___x_1548_; uint8_t v___x_1549_; 
v_typeName_1543_ = lean_ctor_get(v_lhs_1510_, 0);
v_idx_1544_ = lean_ctor_get(v_lhs_1510_, 1);
v_struct_1545_ = lean_ctor_get(v_lhs_1510_, 2);
v___x_1546_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
v___x_1547_ = lean_ptr_addr(v_struct_1545_);
v___x_1548_ = lean_usize_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7);
v___x_1549_ = lean_usize_dec_eq(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
lean_inc(v_idx_1544_);
lean_inc(v_typeName_1543_);
lean_dec_ref_known(v_lhs_1510_, 3);
v___x_1550_ = l_Lean_Expr_proj___override(v_typeName_1543_, v_idx_1544_, v___x_1546_);
v___y_1533_ = v___x_1550_;
goto v___jp_1532_;
}
else
{
v___y_1533_ = v_lhs_1510_;
goto v___jp_1532_;
}
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec_ref(v_lhs_1510_);
v___x_1551_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
v___x_1552_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(v___x_1551_);
v___y_1533_ = v___x_1552_;
goto v___jp_1532_;
}
v___jp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = l_Lean_mkLambda(v___x_1530_, v___x_1531_, v_a_1529_, v___y_1533_);
v___x_1535_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1527_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v___x_1537_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5));
v___x_1538_ = lean_unsigned_to_nat(2u);
v___x_1539_ = lean_mk_empty_array_with_capacity(v___x_1538_);
v___x_1540_ = lean_array_push(v___x_1539_, v___x_1534_);
v___x_1541_ = lean_array_push(v___x_1540_, v_a_1536_);
v___x_1542_ = l_Lean_Meta_mkAppM(v___x_1537_, v___x_1541_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1542_;
}
else
{
lean_dec_ref(v___x_1534_);
return v___x_1535_;
}
}
}
else
{
lean_dec_ref(v___x_1527_);
lean_dec_ref(v_lhs_1510_);
return v___x_1528_;
}
}
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = l_Lean_Expr_appFn_x21(v_lhs_1510_);
v___x_1554_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1553_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13));
v___x_1557_ = l_Lean_Expr_appArg_x21(v_lhs_1510_);
lean_dec_ref(v_lhs_1510_);
v___x_1558_ = lean_unsigned_to_nat(2u);
v___x_1559_ = lean_mk_empty_array_with_capacity(v___x_1558_);
v___x_1560_ = lean_array_push(v___x_1559_, v_a_1555_);
v___x_1561_ = lean_array_push(v___x_1560_, v___x_1557_);
v___x_1562_ = l_Lean_Meta_mkAppM(v___x_1556_, v___x_1561_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1562_;
}
else
{
lean_dec_ref(v_lhs_1510_);
return v___x_1554_;
}
}
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v_dummy_1567_; lean_object* v_nargs_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1563_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__2));
v___x_1564_ = l_Lean_Expr_getAppFn(v_lhs_1510_);
v___x_1565_ = l_Lean_Expr_constLevels_x21(v___x_1564_);
lean_dec_ref(v___x_1564_);
v___x_1566_ = l_Lean_mkConst(v___x_1563_, v___x_1565_);
v_dummy_1567_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_1568_ = l_Lean_Expr_getAppNumArgs(v_lhs_1510_);
lean_inc(v_nargs_1568_);
v___x_1569_ = lean_mk_array(v_nargs_1568_, v_dummy_1567_);
v___x_1570_ = lean_unsigned_to_nat(1u);
v___x_1571_ = lean_nat_sub(v_nargs_1568_, v___x_1570_);
lean_dec(v_nargs_1568_);
v___x_1572_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_1510_, v___x_1569_, v___x_1571_);
v___x_1573_ = l_Lean_mkAppN(v___x_1566_, v___x_1572_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v_dummy_1579_; lean_object* v_nargs_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1575_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__4));
v___x_1576_ = l_Lean_Expr_getAppFn(v_lhs_1510_);
v___x_1577_ = l_Lean_Expr_constLevels_x21(v___x_1576_);
lean_dec_ref(v___x_1576_);
v___x_1578_ = l_Lean_mkConst(v___x_1575_, v___x_1577_);
v_dummy_1579_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_1580_ = l_Lean_Expr_getAppNumArgs(v_lhs_1510_);
lean_inc(v_nargs_1580_);
v___x_1581_ = lean_mk_array(v_nargs_1580_, v_dummy_1579_);
v___x_1582_ = lean_unsigned_to_nat(1u);
v___x_1583_ = lean_nat_sub(v_nargs_1580_, v___x_1582_);
lean_dec(v_nargs_1580_);
v___x_1584_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_lhs_1510_, v___x_1581_, v___x_1583_);
v___x_1585_ = l_Lean_mkAppN(v___x_1578_, v___x_1584_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1510_ = stack[0].m_obj;
lean_object* v_a_1511_ = stack[1].m_obj;
lean_object* v_a_1512_ = stack[2].m_obj;
lean_object* v_a_1513_ = stack[3].m_obj;
lean_object* v_a_1514_ = stack[4].m_obj;
lean_object* v_res_1587_;
v_res_1587_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v_lhs_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
stack->m_obj
 = v_res_1587_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(lean_object* v_lhs_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v_lhs_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
return v_res_1594_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(lean_object* v_msg_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___f_1602_; lean_object* v___x_1515__overap_1603_; lean_object* v___x_1604_; 
v___f_1602_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0));
v___x_1515__overap_1603_ = lean_panic_fn_borrowed(v___f_1602_, v_msg_1596_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v___y_1598_);
lean_inc_ref(v___y_1597_);
v___x_1604_ = lean_apply_5(v___x_1515__overap_1603_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, lean_box(0));
return v___x_1604_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1596_ = stack[0].m_obj;
lean_object* v___y_1597_ = stack[1].m_obj;
lean_object* v___y_1598_ = stack[2].m_obj;
lean_object* v___y_1599_ = stack[3].m_obj;
lean_object* v___y_1600_ = stack[4].m_obj;
lean_object* v_res_1605_;
v_res_1605_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v_msg_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
stack->m_obj
 = v_res_1605_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(lean_object* v_msg_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v_msg_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
lean_object* v_ks_1617_; lean_object* v_vs_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1642_; 
v_ks_1617_ = lean_ctor_get(v_x_1613_, 0);
v_vs_1618_ = lean_ctor_get(v_x_1613_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_x_1613_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1620_ = v_x_1613_;
v_isShared_1621_ = v_isSharedCheck_1642_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_vs_1618_);
lean_inc(v_ks_1617_);
lean_dec(v_x_1613_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1642_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = lean_array_get_size(v_ks_1617_);
v___x_1623_ = lean_nat_dec_lt(v_x_1614_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
lean_dec(v_x_1614_);
v___x_1624_ = lean_array_push(v_ks_1617_, v_x_1615_);
v___x_1625_ = lean_array_push(v_vs_1618_, v_x_1616_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 1, v___x_1625_);
lean_ctor_set(v___x_1620_, 0, v___x_1624_);
v___x_1627_ = v___x_1620_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
else
{
lean_object* v_k_x27_1629_; uint8_t v___x_1630_; 
v_k_x27_1629_ = lean_array_fget_borrowed(v_ks_1617_, v_x_1614_);
v___x_1630_ = l_Lean_instBEqMVarId_beq(v_x_1615_, v_k_x27_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1632_; 
if (v_isShared_1621_ == 0)
{
v___x_1632_ = v___x_1620_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_ks_1617_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_vs_1618_);
v___x_1632_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = lean_nat_add(v_x_1614_, v___x_1633_);
lean_dec(v_x_1614_);
v_x_1613_ = v___x_1632_;
v_x_1614_ = v___x_1634_;
goto _start;
}
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1637_ = lean_array_fset(v_ks_1617_, v_x_1614_, v_x_1615_);
v___x_1638_ = lean_array_fset(v_vs_1618_, v_x_1614_, v_x_1616_);
lean_dec(v_x_1614_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 1, v___x_1638_);
lean_ctor_set(v___x_1620_, 0, v___x_1637_);
v___x_1640_ = v___x_1620_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_1643_, lean_object* v_k_1644_, lean_object* v_v_1645_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_1643_, v___x_1646_, v_k_1644_, v_v_1645_);
return v___x_1647_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1648_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1649_, size_t v_x_1650_, size_t v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
if (lean_obj_tag(v_x_1649_) == 0)
{
lean_object* v_es_1654_; size_t v___x_1655_; size_t v___x_1656_; lean_object* v_j_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v_es_1654_ = lean_ctor_get(v_x_1649_, 0);
v___x_1655_ = ((size_t)31ULL);
v___x_1656_ = lean_usize_land(v_x_1650_, v___x_1655_);
v_j_1657_ = lean_usize_to_nat(v___x_1656_);
v___x_1658_ = lean_array_get_size(v_es_1654_);
v___x_1659_ = lean_nat_dec_lt(v_j_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_dec(v_j_1657_);
lean_dec(v_x_1653_);
lean_dec(v_x_1652_);
return v_x_1649_;
}
else
{
lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1698_; 
lean_inc_ref(v_es_1654_);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_x_1649_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; 
v_unused_1699_ = lean_ctor_get(v_x_1649_, 0);
lean_dec(v_unused_1699_);
v___x_1661_ = v_x_1649_;
v_isShared_1662_ = v_isSharedCheck_1698_;
goto v_resetjp_1660_;
}
else
{
lean_dec(v_x_1649_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1698_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v_v_1663_; lean_object* v___x_1664_; lean_object* v_xs_x27_1665_; lean_object* v___y_1667_; 
v_v_1663_ = lean_array_fget(v_es_1654_, v_j_1657_);
v___x_1664_ = lean_box(0);
v_xs_x27_1665_ = lean_array_fset(v_es_1654_, v_j_1657_, v___x_1664_);
switch(lean_obj_tag(v_v_1663_))
{
case 0:
{
lean_object* v_key_1672_; lean_object* v_val_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1683_; 
v_key_1672_ = lean_ctor_get(v_v_1663_, 0);
v_val_1673_ = lean_ctor_get(v_v_1663_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_v_1663_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1675_ = v_v_1663_;
v_isShared_1676_ = v_isSharedCheck_1683_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_val_1673_);
lean_inc(v_key_1672_);
lean_dec(v_v_1663_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1683_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
uint8_t v___x_1677_; 
v___x_1677_ = l_Lean_instBEqMVarId_beq(v_x_1652_, v_key_1672_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_del_object(v___x_1675_);
v___x_1678_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1672_, v_val_1673_, v_x_1652_, v_x_1653_);
v___x_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
v___y_1667_ = v___x_1679_;
goto v___jp_1666_;
}
else
{
lean_object* v___x_1681_; 
lean_dec(v_val_1673_);
lean_dec(v_key_1672_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 1, v_x_1653_);
lean_ctor_set(v___x_1675_, 0, v_x_1652_);
v___x_1681_ = v___x_1675_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_x_1652_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_x_1653_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
v___y_1667_ = v___x_1681_;
goto v___jp_1666_;
}
}
}
}
case 1:
{
lean_object* v_node_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1696_; 
v_node_1684_ = lean_ctor_get(v_v_1663_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_v_1663_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1686_ = v_v_1663_;
v_isShared_1687_ = v_isSharedCheck_1696_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_node_1684_);
lean_dec(v_v_1663_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1696_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
size_t v___x_1688_; size_t v___x_1689_; size_t v___x_1690_; size_t v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1688_ = ((size_t)5ULL);
v___x_1689_ = lean_usize_shift_right(v_x_1650_, v___x_1688_);
v___x_1690_ = ((size_t)1ULL);
v___x_1691_ = lean_usize_add(v_x_1651_, v___x_1690_);
v___x_1692_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_node_1684_, v___x_1689_, v___x_1691_, v_x_1652_, v_x_1653_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1692_);
v___x_1694_ = v___x_1686_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
v___y_1667_ = v___x_1694_;
goto v___jp_1666_;
}
}
}
default: 
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v_x_1652_);
lean_ctor_set(v___x_1697_, 1, v_x_1653_);
v___y_1667_ = v___x_1697_;
goto v___jp_1666_;
}
}
v___jp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = lean_array_fset(v_xs_x27_1665_, v_j_1657_, v___y_1667_);
lean_dec(v_j_1657_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1668_);
v___x_1670_ = v___x_1661_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
else
{
lean_object* v_ks_1700_; lean_object* v_vs_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1719_; 
v_ks_1700_ = lean_ctor_get(v_x_1649_, 0);
v_vs_1701_ = lean_ctor_get(v_x_1649_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_x_1649_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1703_ = v_x_1649_;
v_isShared_1704_ = v_isSharedCheck_1719_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_vs_1701_);
lean_inc(v_ks_1700_);
lean_dec(v_x_1649_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1719_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_ks_1700_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_vs_1701_);
v___x_1706_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v_newNode_1707_; size_t v___x_1708_; uint8_t v___x_1709_; 
v_newNode_1707_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v___x_1706_, v_x_1652_, v_x_1653_);
v___x_1708_ = ((size_t)7ULL);
v___x_1709_ = lean_usize_dec_le(v___x_1708_, v_x_1651_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1710_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1707_);
v___x_1711_ = lean_unsigned_to_nat(4u);
v___x_1712_ = lean_nat_dec_lt(v___x_1710_, v___x_1711_);
lean_dec(v___x_1710_);
if (v___x_1712_ == 0)
{
lean_object* v_ks_1713_; lean_object* v_vs_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_ks_1713_ = lean_ctor_get(v_newNode_1707_, 0);
lean_inc_ref(v_ks_1713_);
v_vs_1714_ = lean_ctor_get(v_newNode_1707_, 1);
lean_inc_ref(v_vs_1714_);
lean_dec_ref(v_newNode_1707_);
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_1717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_1651_, v_ks_1713_, v_vs_1714_, v___x_1715_, v___x_1716_);
lean_dec_ref(v_vs_1714_);
lean_dec_ref(v_ks_1713_);
return v___x_1717_;
}
else
{
return v_newNode_1707_;
}
}
else
{
return v_newNode_1707_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1649_ = stack[0].m_obj;
size_t v_x_1650_ = stack[1].m_num;
size_t v_x_1651_ = stack[2].m_num;
lean_object* v_x_1652_ = stack[3].m_obj;
lean_object* v_x_1653_ = stack[4].m_obj;
lean_object* v_res_1720_;
v_res_1720_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1649_, v_x_1650_, v_x_1651_, v_x_1652_, v_x_1653_);
stack->m_obj
 = v_res_1720_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_1721_, lean_object* v_keys_1722_, lean_object* v_vals_1723_, lean_object* v_i_1724_, lean_object* v_entries_1725_){
_start:
{
lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = lean_array_get_size(v_keys_1722_);
v___x_1727_ = lean_nat_dec_lt(v_i_1724_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_dec(v_i_1724_);
return v_entries_1725_;
}
else
{
lean_object* v_k_1728_; lean_object* v_v_1729_; uint64_t v___x_1730_; size_t v_h_1731_; size_t v___x_1732_; lean_object* v___x_1733_; size_t v___x_1734_; size_t v___x_1735_; size_t v___x_1736_; size_t v_h_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_k_1728_ = lean_array_fget_borrowed(v_keys_1722_, v_i_1724_);
v_v_1729_ = lean_array_fget_borrowed(v_vals_1723_, v_i_1724_);
v___x_1730_ = l_Lean_instHashableMVarId_hash(v_k_1728_);
v_h_1731_ = lean_uint64_to_usize(v___x_1730_);
v___x_1732_ = ((size_t)5ULL);
v___x_1733_ = lean_unsigned_to_nat(1u);
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_sub(v_depth_1721_, v___x_1734_);
v___x_1736_ = lean_usize_mul(v___x_1732_, v___x_1735_);
v_h_1737_ = lean_usize_shift_right(v_h_1731_, v___x_1736_);
v___x_1738_ = lean_nat_add(v_i_1724_, v___x_1733_);
lean_dec(v_i_1724_);
lean_inc(v_v_1729_);
lean_inc(v_k_1728_);
v___x_1739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_entries_1725_, v_h_1737_, v_depth_1721_, v_k_1728_, v_v_1729_);
v_i_1724_ = v___x_1738_;
v_entries_1725_ = v___x_1739_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1721_ = stack[0].m_num;
lean_object* v_keys_1722_ = stack[1].m_obj;
lean_object* v_vals_1723_ = stack[2].m_obj;
lean_object* v_i_1724_ = stack[3].m_obj;
lean_object* v_entries_1725_ = stack[4].m_obj;
lean_object* v_res_1741_;
v_res_1741_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1721_, v_keys_1722_, v_vals_1723_, v_i_1724_, v_entries_1725_);
stack->m_obj
 = v_res_1741_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_1742_, lean_object* v_keys_1743_, lean_object* v_vals_1744_, lean_object* v_i_1745_, lean_object* v_entries_1746_){
_start:
{
size_t v_depth_boxed_1747_; lean_object* v_res_1748_; 
v_depth_boxed_1747_ = lean_unbox_usize(v_depth_1742_);
lean_dec(v_depth_1742_);
v_res_1748_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_1747_, v_keys_1743_, v_vals_1744_, v_i_1745_, v_entries_1746_);
lean_dec_ref(v_vals_1744_);
lean_dec_ref(v_keys_1743_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
size_t v_x_2150__boxed_1754_; size_t v_x_2151__boxed_1755_; lean_object* v_res_1756_; 
v_x_2150__boxed_1754_ = lean_unbox_usize(v_x_1750_);
lean_dec(v_x_1750_);
v_x_2151__boxed_1755_ = lean_unbox_usize(v_x_1751_);
lean_dec(v_x_1751_);
v_res_1756_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1749_, v_x_2150__boxed_1754_, v_x_2151__boxed_1755_, v_x_1752_, v_x_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(lean_object* v_x_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
uint64_t v___x_1760_; size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = l_Lean_instHashableMVarId_hash(v_x_1758_);
v___x_1761_ = lean_uint64_to_usize(v___x_1760_);
v___x_1762_ = ((size_t)1ULL);
v___x_1763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1757_, v___x_1761_, v___x_1762_, v_x_1758_, v_x_1759_);
return v___x_1763_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(lean_object* v_mvarId_1764_, lean_object* v_val_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; lean_object* v_mctx_1769_; lean_object* v_cache_1770_; lean_object* v_zetaDeltaFVarIds_1771_; lean_object* v_postponed_1772_; lean_object* v_diag_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1803_; 
v___x_1768_ = lean_st_ref_take(v___y_1766_);
v_mctx_1769_ = lean_ctor_get(v___x_1768_, 0);
v_cache_1770_ = lean_ctor_get(v___x_1768_, 1);
v_zetaDeltaFVarIds_1771_ = lean_ctor_get(v___x_1768_, 2);
v_postponed_1772_ = lean_ctor_get(v___x_1768_, 3);
v_diag_1773_ = lean_ctor_get(v___x_1768_, 4);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1775_ = v___x_1768_;
v_isShared_1776_ = v_isSharedCheck_1803_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_diag_1773_);
lean_inc(v_postponed_1772_);
lean_inc(v_zetaDeltaFVarIds_1771_);
lean_inc(v_cache_1770_);
lean_inc(v_mctx_1769_);
lean_dec(v___x_1768_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1803_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v_depth_1777_; lean_object* v_levelAssignDepth_1778_; lean_object* v_lmvarCounter_1779_; lean_object* v_mvarCounter_1780_; lean_object* v_lDecls_1781_; lean_object* v_decls_1782_; lean_object* v_userNames_1783_; lean_object* v_lAssignment_1784_; lean_object* v_eAssignment_1785_; lean_object* v_dAssignment_1786_; lean_object* v_instanceTypedMVars_1787_; lean_object* v_synthNormMemo_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1802_; 
v_depth_1777_ = lean_ctor_get(v_mctx_1769_, 0);
v_levelAssignDepth_1778_ = lean_ctor_get(v_mctx_1769_, 1);
v_lmvarCounter_1779_ = lean_ctor_get(v_mctx_1769_, 2);
v_mvarCounter_1780_ = lean_ctor_get(v_mctx_1769_, 3);
v_lDecls_1781_ = lean_ctor_get(v_mctx_1769_, 4);
v_decls_1782_ = lean_ctor_get(v_mctx_1769_, 5);
v_userNames_1783_ = lean_ctor_get(v_mctx_1769_, 6);
v_lAssignment_1784_ = lean_ctor_get(v_mctx_1769_, 7);
v_eAssignment_1785_ = lean_ctor_get(v_mctx_1769_, 8);
v_dAssignment_1786_ = lean_ctor_get(v_mctx_1769_, 9);
v_instanceTypedMVars_1787_ = lean_ctor_get(v_mctx_1769_, 10);
v_synthNormMemo_1788_ = lean_ctor_get(v_mctx_1769_, 11);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_mctx_1769_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1790_ = v_mctx_1769_;
v_isShared_1791_ = v_isSharedCheck_1802_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_synthNormMemo_1788_);
lean_inc(v_instanceTypedMVars_1787_);
lean_inc(v_dAssignment_1786_);
lean_inc(v_eAssignment_1785_);
lean_inc(v_lAssignment_1784_);
lean_inc(v_userNames_1783_);
lean_inc(v_decls_1782_);
lean_inc(v_lDecls_1781_);
lean_inc(v_mvarCounter_1780_);
lean_inc(v_lmvarCounter_1779_);
lean_inc(v_levelAssignDepth_1778_);
lean_inc(v_depth_1777_);
lean_dec(v_mctx_1769_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1802_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1792_ = lean_box(0);
v___x_1793_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_1785_, v_mvarId_1764_, v_val_1765_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 8, v___x_1793_);
v___x_1795_ = v___x_1790_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_depth_1777_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_levelAssignDepth_1778_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_lmvarCounter_1779_);
lean_ctor_set(v_reuseFailAlloc_1801_, 3, v_mvarCounter_1780_);
lean_ctor_set(v_reuseFailAlloc_1801_, 4, v_lDecls_1781_);
lean_ctor_set(v_reuseFailAlloc_1801_, 5, v_decls_1782_);
lean_ctor_set(v_reuseFailAlloc_1801_, 6, v_userNames_1783_);
lean_ctor_set(v_reuseFailAlloc_1801_, 7, v_lAssignment_1784_);
lean_ctor_set(v_reuseFailAlloc_1801_, 8, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1801_, 9, v_dAssignment_1786_);
lean_ctor_set(v_reuseFailAlloc_1801_, 10, v_instanceTypedMVars_1787_);
lean_ctor_set(v_reuseFailAlloc_1801_, 11, v_synthNormMemo_1788_);
v___x_1795_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1797_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1795_);
v___x_1797_ = v___x_1775_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_cache_1770_);
lean_ctor_set(v_reuseFailAlloc_1800_, 2, v_zetaDeltaFVarIds_1771_);
lean_ctor_set(v_reuseFailAlloc_1800_, 3, v_postponed_1772_);
lean_ctor_set(v_reuseFailAlloc_1800_, 4, v_diag_1773_);
v___x_1797_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_st_ref_put(v___y_1766_, v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1792_);
return v___x_1799_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1764_ = stack[0].m_obj;
lean_object* v_val_1765_ = stack[1].m_obj;
lean_object* v___y_1766_ = stack[2].m_obj;
lean_object* v_res_1804_;
v_res_1804_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1764_, v_val_1765_, v___y_1766_);
stack->m_obj
 = v_res_1804_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(lean_object* v_mvarId_1805_, lean_object* v_val_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1805_, v_val_1806_, v___y_1807_);
lean_dec(v___y_1807_);
return v_res_1809_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1812_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1813_ = lean_unsigned_to_nat(41u);
v___x_1814_ = lean_unsigned_to_nat(113u);
v___x_1815_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_1816_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1817_ = l_mkPanicMessageWithDecl(v___x_1816_, v___x_1815_, v___x_1814_, v___x_1813_, v___x_1812_);
return v___x_1817_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1818_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_1819_ = lean_unsigned_to_nat(51u);
v___x_1820_ = lean_unsigned_to_nat(115u);
v___x_1821_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1));
v___x_1822_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_1823_ = l_mkPanicMessageWithDecl(v___x_1822_, v___x_1821_, v___x_1820_, v___x_1819_, v___x_1818_);
return v___x_1823_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object* v_mvarId_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; 
lean_inc(v_mvarId_1824_);
v___x_1830_ = l_Lean_MVarId_getType_x27(v_mvarId_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_1833_ = lean_unsigned_to_nat(3u);
v___x_1834_ = l_Lean_Expr_isAppOfArity(v_a_1831_, v___x_1832_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec(v_a_1831_);
lean_dec(v_mvarId_1824_);
v___x_1835_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2);
v___x_1836_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_1835_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1837_ = l_Lean_Expr_appFn_x21(v_a_1831_);
v___x_1838_ = l_Lean_Expr_appArg_x21(v___x_1837_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = l_Lean_Expr_appArg_x21(v_a_1831_);
lean_dec(v_a_1831_);
v___x_1840_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_1838_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1842_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc_n(v_a_1841_, 2);
lean_dec_ref_known(v___x_1840_, 1);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
v___x_1842_ = lean_infer_type(v_a_1841_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; uint8_t v___x_1844_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
v___x_1844_ = l_Lean_Expr_isAppOfArity(v_a_1843_, v___x_1832_, v___x_1833_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec(v_a_1843_);
lean_dec(v_a_1841_);
lean_dec_ref(v___x_1839_);
lean_dec(v_mvarId_1824_);
v___x_1845_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
v___x_1846_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_1845_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = l_Lean_Expr_appArg_x21(v_a_1843_);
lean_dec(v_a_1843_);
v___x_1848_ = l_Lean_Meta_mkEq(v___x_1847_, v___x_1839_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = lean_box(0);
v___x_1851_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1849_, v___x_1850_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1853_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc_n(v_a_1852_, 2);
lean_dec_ref_known(v___x_1851_, 1);
v___x_1853_ = l_Lean_Meta_mkEqTrans(v_a_1841_, v_a_1852_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v___y_1825_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1863_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1824_, v_a_1854_, v___y_1826_);
lean_dec(v___y_1826_);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v___x_1855_, 0);
lean_dec(v_unused_1864_);
v___x_1857_ = v___x_1855_;
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
else
{
lean_dec(v___x_1855_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = l_Lean_Expr_mvarId_x21(v_a_1852_);
lean_dec(v_a_1852_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1859_);
v___x_1861_ = v___x_1857_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_a_1852_);
lean_dec(v___y_1826_);
lean_dec(v_mvarId_1824_);
v_a_1865_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1853_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1853_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_a_1841_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v_mvarId_1824_);
v_a_1873_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1851_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1851_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_a_1841_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v_mvarId_1824_);
v_a_1881_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1848_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1848_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec(v_a_1841_);
lean_dec_ref(v___x_1839_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v_mvarId_1824_);
v_a_1889_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1842_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1842_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec_ref(v___x_1839_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v_mvarId_1824_);
v_a_1897_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1840_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1840_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v_mvarId_1824_);
v_a_1905_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1830_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1830_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1824_ = stack[0].m_obj;
lean_object* v___y_1825_ = stack[1].m_obj;
lean_object* v___y_1826_ = stack[2].m_obj;
lean_object* v___y_1827_ = stack[3].m_obj;
lean_object* v___y_1828_ = stack[4].m_obj;
lean_object* v_res_1913_;
v_res_1913_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
stack->m_obj
 = v_res_1913_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(lean_object* v_mvarId_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
return v_res_1920_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object* v_mvarId_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v___f_1927_; lean_object* v___x_1928_; 
lean_inc(v_mvarId_1921_);
v___f_1927_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1927_, 0, v_mvarId_1921_);
v___x_1928_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_1921_, v___f_1927_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
return v___x_1928_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1921_ = stack[0].m_obj;
lean_object* v_a_1922_ = stack[1].m_obj;
lean_object* v_a_1923_ = stack[2].m_obj;
lean_object* v_a_1924_ = stack[3].m_obj;
lean_object* v_a_1925_ = stack[4].m_obj;
lean_object* v_res_1929_;
v_res_1929_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
stack->m_obj
 = v_res_1929_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(lean_object* v_mvarId_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
return v_res_1936_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(lean_object* v_mvarId_1937_, lean_object* v_val_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_1937_, v_val_1938_, v___y_1940_);
return v___x_1944_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1937_ = stack[0].m_obj;
lean_object* v_val_1938_ = stack[1].m_obj;
lean_object* v___y_1939_ = stack[2].m_obj;
lean_object* v___y_1940_ = stack[3].m_obj;
lean_object* v___y_1941_ = stack[4].m_obj;
lean_object* v___y_1942_ = stack[5].m_obj;
lean_object* v_res_1945_;
v_res_1945_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_1937_, v_val_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
stack->m_obj
 = v_res_1945_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(lean_object* v_mvarId_1946_, lean_object* v_val_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_1946_, v_val_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(lean_object* v_00_u03b2_1954_, lean_object* v_x_1955_, lean_object* v_x_1956_, lean_object* v_x_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_1955_, v_x_1956_, v_x_1957_);
return v___x_1958_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1959_, lean_object* v_x_1960_, size_t v_x_1961_, size_t v_x_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_1960_, v_x_1961_, v_x_1962_, v_x_1963_, v_x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1960_ = stack[1].m_obj;
size_t v_x_1961_ = stack[2].m_num;
size_t v_x_1962_ = stack[3].m_num;
lean_object* v_x_1963_ = stack[4].m_obj;
lean_object* v_x_1964_ = stack[5].m_obj;
lean_object* v_res_1966_;
v_res_1966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(lean_box(0), v_x_1960_, v_x_1961_, v_x_1962_, v_x_1963_, v_x_1964_);
stack->m_obj
 = v_res_1966_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1967_, lean_object* v_x_1968_, lean_object* v_x_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_){
_start:
{
size_t v_x_2864__boxed_1973_; size_t v_x_2865__boxed_1974_; lean_object* v_res_1975_; 
v_x_2864__boxed_1973_ = lean_unbox_usize(v_x_1969_);
lean_dec(v_x_1969_);
v_x_2865__boxed_1974_ = lean_unbox_usize(v_x_1970_);
lean_dec(v_x_1970_);
v_res_1975_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_1967_, v_x_1968_, v_x_2864__boxed_1973_, v_x_2865__boxed_1974_, v_x_1971_, v_x_1972_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1976_, lean_object* v_n_1977_, lean_object* v_k_1978_, lean_object* v_v_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1977_, v_k_1978_, v_v_1979_);
return v___x_1980_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1981_, size_t v_depth_1982_, lean_object* v_keys_1983_, lean_object* v_vals_1984_, lean_object* v_heq_1985_, lean_object* v_i_1986_, lean_object* v_entries_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1982_, v_keys_1983_, v_vals_1984_, v_i_1986_, v_entries_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1982_ = stack[1].m_num;
lean_object* v_keys_1983_ = stack[2].m_obj;
lean_object* v_vals_1984_ = stack[3].m_obj;
lean_object* v_i_1986_ = stack[5].m_obj;
lean_object* v_entries_1987_ = stack[6].m_obj;
lean_object* v_res_1989_;
v_res_1989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(lean_box(0), v_depth_1982_, v_keys_1983_, v_vals_1984_, lean_box(0), v_i_1986_, v_entries_1987_);
stack->m_obj
 = v_res_1989_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1990_, lean_object* v_depth_1991_, lean_object* v_keys_1992_, lean_object* v_vals_1993_, lean_object* v_heq_1994_, lean_object* v_i_1995_, lean_object* v_entries_1996_){
_start:
{
size_t v_depth_boxed_1997_; lean_object* v_res_1998_; 
v_depth_boxed_1997_ = lean_unbox_usize(v_depth_1991_);
lean_dec(v_depth_1991_);
v_res_1998_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1990_, v_depth_boxed_1997_, v_keys_1992_, v_vals_1993_, v_heq_1994_, v_i_1995_, v_entries_1996_);
lean_dec_ref(v_vals_1993_);
lean_dec_ref(v_keys_1992_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2000_, v_x_2001_, v_x_2002_, v_x_2003_);
return v___x_2004_;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0(lean_object* v_declNameNonRec_2005_, lean_object* v_numFixed_2006_, lean_object* v_x_2007_){
_start:
{
uint8_t v___x_2008_; 
v___x_2008_ = l_Lean_Expr_isAppOfArity(v_x_2007_, v_declNameNonRec_2005_, v_numFixed_2006_);
return v___x_2008_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNameNonRec_2005_ = stack[0].m_obj;
lean_object* v_numFixed_2006_ = stack[1].m_obj;
lean_object* v_x_2007_ = stack[2].m_obj;
uint8_t v_res_2009_;
v_res_2009_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0(v_declNameNonRec_2005_, v_numFixed_2006_, v_x_2007_);
stack->m_num = v_res_2009_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0___boxed(lean_object* v_declNameNonRec_2010_, lean_object* v_numFixed_2011_, lean_object* v_x_2012_){
_start:
{
uint8_t v_res_2013_; lean_object* v_r_2014_; 
v_res_2013_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0(v_declNameNonRec_2010_, v_numFixed_2011_, v_x_2012_);
lean_dec_ref(v_x_2012_);
lean_dec(v_declNameNonRec_2010_);
v_r_2014_ = lean_box(v_res_2013_);
return v_r_2014_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2016_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_2017_ = lean_unsigned_to_nat(41u);
v___x_2018_ = lean_unsigned_to_nat(128u);
v___x_2019_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__0));
v___x_2020_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_2021_ = l_mkPanicMessageWithDecl(v___x_2020_, v___x_2019_, v___x_2018_, v___x_2017_, v___x_2016_);
return v___x_2021_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2022_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__1___closed__6));
v___x_2023_ = lean_unsigned_to_nat(51u);
v___x_2024_ = lean_unsigned_to_nat(134u);
v___x_2025_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__0));
v___x_2026_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0));
v___x_2027_ = l_mkPanicMessageWithDecl(v___x_2026_, v___x_2025_, v___x_2024_, v___x_2023_, v___x_2022_);
return v___x_2027_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__5));
v___x_2033_ = l_Lean_stringToMessageData(v___x_2032_);
return v___x_2033_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__7));
v___x_2036_ = l_Lean_stringToMessageData(v___x_2035_);
return v___x_2036_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1(lean_object* v_mvarId_2037_, lean_object* v___f_2038_, lean_object* v_fixEq_2039_, lean_object* v_declNameNonRec_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; 
lean_inc(v_mvarId_2037_);
v___x_2046_ = l_Lean_MVarId_getType_x27(v_mvarId_2037_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1));
v___x_2049_ = lean_unsigned_to_nat(3u);
v___x_2050_ = l_Lean_Expr_isAppOfArity(v_a_2047_, v___x_2048_, v___x_2049_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_dec(v_a_2047_);
lean_dec(v_declNameNonRec_2040_);
lean_dec(v_fixEq_2039_);
lean_dec(v_mvarId_2037_);
v___x_2051_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__1);
v___x_2052_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_2051_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v___x_2052_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = l_Lean_Expr_appFn_x21(v_a_2047_);
v___x_2054_ = l_Lean_Expr_appArg_x21(v___x_2053_);
lean_dec_ref(v___x_2053_);
v___x_2055_ = lean_find_expr(v___f_2038_, v___x_2054_);
if (lean_obj_tag(v___x_2055_) == 1)
{
lean_object* v_val_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec(v_declNameNonRec_2040_);
v_val_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc_n(v_val_2056_, 2);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2057_ = l_Lean_Expr_appArg_x21(v_a_2047_);
lean_dec(v_a_2047_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
v___x_2058_ = lean_infer_type(v_val_2056_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = lean_box(0);
lean_inc(v_val_2056_);
v___x_2061_ = l_Lean_Meta_kabstract(v___x_2054_, v_val_2056_, v___x_2060_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_dummy_2069_; lean_object* v_nargs_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3));
v___x_2064_ = 0;
v___x_2065_ = l_Lean_mkLambda(v___x_2063_, v___x_2064_, v_a_2059_, v_a_2062_);
v___x_2066_ = l_Lean_Expr_getAppFn(v_val_2056_);
v___x_2067_ = l_Lean_Expr_constLevels_x21(v___x_2066_);
lean_dec_ref(v___x_2066_);
v___x_2068_ = l_Lean_mkConst(v_fixEq_2039_, v___x_2067_);
v_dummy_2069_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq___lam__1___closed__0);
v_nargs_2070_ = l_Lean_Expr_getAppNumArgs(v_val_2056_);
lean_inc(v_nargs_2070_);
v___x_2071_ = lean_mk_array(v_nargs_2070_, v_dummy_2069_);
v___x_2072_ = lean_unsigned_to_nat(1u);
v___x_2073_ = lean_nat_sub(v_nargs_2070_, v___x_2072_);
lean_dec(v_nargs_2070_);
v___x_2074_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_2056_, v___x_2071_, v___x_2073_);
v___x_2075_ = l_Lean_mkAppN(v___x_2068_, v___x_2074_);
lean_dec_ref(v___x_2074_);
v___x_2076_ = l_Lean_Meta_mkCongrArg(v___x_2065_, v___x_2075_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2078_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc_n(v_a_2077_, 2);
lean_dec_ref_known(v___x_2076_, 1);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
v___x_2078_ = lean_infer_type(v_a_2077_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; uint8_t v___x_2080_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v___x_2080_ = l_Lean_Expr_isAppOfArity(v_a_2079_, v___x_2048_, v___x_2049_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec(v_a_2079_);
lean_dec(v_a_2077_);
lean_dec_ref(v___x_2057_);
lean_dec(v_mvarId_2037_);
v___x_2081_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__2);
v___x_2082_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_2081_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v___x_2082_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = l_Lean_Expr_appArg_x21(v_a_2079_);
lean_dec(v_a_2079_);
v___x_2084_ = l_Lean_Expr_headBeta(v___x_2083_);
v___x_2085_ = l_Lean_Meta_mkEq(v___x_2084_, v___x_2057_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2087_ = lean_box(0);
v___x_2088_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2086_, v___x_2087_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc_n(v_a_2089_, 2);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2090_ = l_Lean_Meta_mkEqTrans(v_a_2077_, v_a_2089_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec_ref(v___y_2041_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2100_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_2037_, v_a_2091_, v___y_2042_);
lean_dec(v___y_2042_);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2100_ == 0)
{
lean_object* v_unused_2101_; 
v_unused_2101_ = lean_ctor_get(v___x_2092_, 0);
lean_dec(v_unused_2101_);
v___x_2094_ = v___x_2092_;
v_isShared_2095_ = v_isSharedCheck_2100_;
goto v_resetjp_2093_;
}
else
{
lean_dec(v___x_2092_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2100_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = l_Lean_Expr_mvarId_x21(v_a_2089_);
lean_dec(v_a_2089_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2096_);
v___x_2098_ = v___x_2094_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_a_2089_);
lean_dec(v___y_2042_);
lean_dec(v_mvarId_2037_);
v_a_2102_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2090_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2090_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec(v_a_2077_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v_mvarId_2037_);
v_a_2110_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2088_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2088_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec(v_a_2077_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v_mvarId_2037_);
v_a_2118_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2085_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2085_);
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
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec(v_a_2077_);
lean_dec_ref(v___x_2057_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v_mvarId_2037_);
v_a_2126_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2078_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2078_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v___x_2057_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v_mvarId_2037_);
v_a_2134_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2076_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2076_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v_a_2059_);
lean_dec_ref(v___x_2057_);
lean_dec(v_val_2056_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v_fixEq_2039_);
lean_dec(v_mvarId_2037_);
v_a_2142_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2061_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2061_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec_ref(v___x_2057_);
lean_dec(v_val_2056_);
lean_dec_ref(v___x_2054_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v_fixEq_2039_);
lean_dec(v_mvarId_2037_);
v_a_2150_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2058_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2058_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v___x_2055_);
lean_dec_ref(v___x_2054_);
lean_dec(v_a_2047_);
lean_dec(v_fixEq_2039_);
v___x_2158_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__4));
v___x_2159_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__6);
v___x_2160_ = 0;
v___x_2161_ = l_Lean_MessageData_ofConstName(v_declNameNonRec_2040_, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2159_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___closed__8);
v___x_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
v___x_2166_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2158_, v_mvarId_2037_, v___x_2165_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v___x_2166_;
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v_declNameNonRec_2040_);
lean_dec(v_fixEq_2039_);
lean_dec(v_mvarId_2037_);
v_a_2167_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2046_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2046_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2037_ = stack[0].m_obj;
lean_object* v___f_2038_ = stack[1].m_obj;
lean_object* v_fixEq_2039_ = stack[2].m_obj;
lean_object* v_declNameNonRec_2040_ = stack[3].m_obj;
lean_object* v___y_2041_ = stack[4].m_obj;
lean_object* v___y_2042_ = stack[5].m_obj;
lean_object* v___y_2043_ = stack[6].m_obj;
lean_object* v___y_2044_ = stack[7].m_obj;
lean_object* v_res_2175_;
v_res_2175_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1(v_mvarId_2037_, v___f_2038_, v_fixEq_2039_, v_declNameNonRec_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
stack->m_obj
 = v_res_2175_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___boxed(lean_object* v_mvarId_2176_, lean_object* v___f_2177_, lean_object* v_fixEq_2178_, lean_object* v_declNameNonRec_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1(v_mvarId_2176_, v___f_2177_, v_fixEq_2178_, v_declNameNonRec_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec_ref(v___f_2177_);
return v_res_2185_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(lean_object* v_declNameNonRec_2186_, lean_object* v_fixEq_2187_, lean_object* v_numFixed_2188_, lean_object* v_mvarId_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v___f_2195_; lean_object* v___f_2196_; lean_object* v___x_2197_; 
lean_inc(v_declNameNonRec_2186_);
v___f_2195_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2195_, 0, v_declNameNonRec_2186_);
lean_closure_set(v___f_2195_, 1, v_numFixed_2188_);
lean_inc(v_mvarId_2189_);
v___f_2196_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___lam__1___boxed), 9, 4);
lean_closure_set(v___f_2196_, 0, v_mvarId_2189_);
lean_closure_set(v___f_2196_, 1, v___f_2195_);
lean_closure_set(v___f_2196_, 2, v_fixEq_2187_);
lean_closure_set(v___f_2196_, 3, v_declNameNonRec_2186_);
v___x_2197_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_2189_, v___f_2196_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
return v___x_2197_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNameNonRec_2186_ = stack[0].m_obj;
lean_object* v_fixEq_2187_ = stack[1].m_obj;
lean_object* v_numFixed_2188_ = stack[2].m_obj;
lean_object* v_mvarId_2189_ = stack[3].m_obj;
lean_object* v_a_2190_ = stack[4].m_obj;
lean_object* v_a_2191_ = stack[5].m_obj;
lean_object* v_a_2192_ = stack[6].m_obj;
lean_object* v_a_2193_ = stack[7].m_obj;
lean_object* v_res_2198_;
v_res_2198_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(v_declNameNonRec_2186_, v_fixEq_2187_, v_numFixed_2188_, v_mvarId_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
stack->m_obj
 = v_res_2198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith___boxed(lean_object* v_declNameNonRec_2199_, lean_object* v_fixEq_2200_, lean_object* v_numFixed_2201_, lean_object* v_mvarId_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(v_declNameNonRec_2199_, v_fixEq_2200_, v_numFixed_2201_, v_mvarId_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
return v_res_2208_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(lean_object* v_e_2209_, lean_object* v___y_2210_){
_start:
{
uint8_t v___x_2212_; 
v___x_2212_ = l_Lean_Expr_hasMVar(v_e_2209_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; 
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_e_2209_);
return v___x_2213_;
}
else
{
lean_object* v___x_2214_; lean_object* v_mctx_2215_; lean_object* v___x_2216_; lean_object* v_fst_2217_; lean_object* v_snd_2218_; lean_object* v___x_2219_; lean_object* v_cache_2220_; lean_object* v_zetaDeltaFVarIds_2221_; lean_object* v_postponed_2222_; lean_object* v_diag_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2232_; 
v___x_2214_ = lean_st_ref_get(v___y_2210_);
v_mctx_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc_ref(v_mctx_2215_);
lean_dec(v___x_2214_);
v___x_2216_ = l_Lean_instantiateMVarsCore(v_mctx_2215_, v_e_2209_);
v_fst_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_fst_2217_);
v_snd_2218_ = lean_ctor_get(v___x_2216_, 1);
lean_inc(v_snd_2218_);
lean_dec_ref(v___x_2216_);
v___x_2219_ = lean_st_ref_take(v___y_2210_);
v_cache_2220_ = lean_ctor_get(v___x_2219_, 1);
v_zetaDeltaFVarIds_2221_ = lean_ctor_get(v___x_2219_, 2);
v_postponed_2222_ = lean_ctor_get(v___x_2219_, 3);
v_diag_2223_ = lean_ctor_get(v___x_2219_, 4);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; 
v_unused_2233_ = lean_ctor_get(v___x_2219_, 0);
lean_dec(v_unused_2233_);
v___x_2225_ = v___x_2219_;
v_isShared_2226_ = v_isSharedCheck_2232_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_diag_2223_);
lean_inc(v_postponed_2222_);
lean_inc(v_zetaDeltaFVarIds_2221_);
lean_inc(v_cache_2220_);
lean_dec(v___x_2219_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2232_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v_snd_2218_);
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_snd_2218_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_cache_2220_);
lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_zetaDeltaFVarIds_2221_);
lean_ctor_set(v_reuseFailAlloc_2231_, 3, v_postponed_2222_);
lean_ctor_set(v_reuseFailAlloc_2231_, 4, v_diag_2223_);
v___x_2228_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_st_ref_put(v___y_2210_, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v_fst_2217_);
return v___x_2230_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2209_ = stack[0].m_obj;
lean_object* v___y_2210_ = stack[1].m_obj;
lean_object* v_res_2234_;
v_res_2234_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_e_2209_, v___y_2210_);
stack->m_obj
 = v_res_2234_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg___boxed(lean_object* v_e_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_e_2235_, v___y_2236_);
lean_dec(v___y_2236_);
return v_res_2238_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(lean_object* v_e_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_e_2239_, v___y_2241_);
return v___x_2245_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2239_ = stack[0].m_obj;
lean_object* v___y_2240_ = stack[1].m_obj;
lean_object* v___y_2241_ = stack[2].m_obj;
lean_object* v___y_2242_ = stack[3].m_obj;
lean_object* v___y_2243_ = stack[4].m_obj;
lean_object* v_res_2246_;
v_res_2246_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_e_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
stack->m_obj
 = v_res_2246_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___boxed(lean_object* v_e_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_e_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_2254_, lean_object* v_opt_2255_){
_start:
{
lean_object* v_name_2256_; lean_object* v_defValue_2257_; lean_object* v_map_2258_; lean_object* v___x_2259_; 
v_name_2256_ = lean_ctor_get(v_opt_2255_, 0);
v_defValue_2257_ = lean_ctor_get(v_opt_2255_, 1);
v_map_2258_ = lean_ctor_get(v_opts_2254_, 0);
v___x_2259_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2258_, v_name_2256_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_inc(v_defValue_2257_);
return v_defValue_2257_;
}
else
{
lean_object* v_val_2260_; 
v_val_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_val_2260_);
lean_dec_ref_known(v___x_2259_, 1);
if (lean_obj_tag(v_val_2260_) == 3)
{
lean_object* v_v_2261_; 
v_v_2261_ = lean_ctor_get(v_val_2260_, 0);
lean_inc(v_v_2261_);
lean_dec_ref_known(v_val_2260_, 1);
return v_v_2261_;
}
else
{
lean_dec(v_val_2260_);
lean_inc(v_defValue_2257_);
return v_defValue_2257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_2262_, lean_object* v_opt_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_2262_, v_opt_2263_);
lean_dec_ref(v_opt_2263_);
lean_dec_ref(v_opts_2262_);
return v_res_2264_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(lean_object* v_k_2265_, uint8_t v_allowLevelAssignments_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2266_, v_k_2265_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_a_2281_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2272_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2272_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2265_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_2266_ = stack[1].m_num;
lean_object* v___y_2267_ = stack[2].m_obj;
lean_object* v___y_2268_ = stack[3].m_obj;
lean_object* v___y_2269_ = stack[4].m_obj;
lean_object* v___y_2270_ = stack[5].m_obj;
lean_object* v_res_2289_;
v_res_2289_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_k_2265_, v_allowLevelAssignments_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
stack->m_obj
 = v_res_2289_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg___boxed(lean_object* v_k_2290_, lean_object* v_allowLevelAssignments_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2297_; lean_object* v_res_2298_; 
v_allowLevelAssignments_boxed_2297_ = lean_unbox(v_allowLevelAssignments_2291_);
v_res_2298_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_k_2290_, v_allowLevelAssignments_boxed_2297_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
return v_res_2298_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_object* v_00_u03b1_2299_, lean_object* v_k_2300_, uint8_t v_allowLevelAssignments_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_k_2300_, v_allowLevelAssignments_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2300_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_2301_ = stack[2].m_num;
lean_object* v___y_2302_ = stack[3].m_obj;
lean_object* v___y_2303_ = stack[4].m_obj;
lean_object* v___y_2304_ = stack[5].m_obj;
lean_object* v___y_2305_ = stack[6].m_obj;
lean_object* v_res_2308_;
v_res_2308_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(lean_box(0), v_k_2300_, v_allowLevelAssignments_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
stack->m_obj
 = v_res_2308_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(lean_object* v_00_u03b1_2309_, lean_object* v_k_2310_, lean_object* v_allowLevelAssignments_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2317_; lean_object* v_res_2318_; 
v_allowLevelAssignments_boxed_2317_ = lean_unbox(v_allowLevelAssignments_2311_);
v_res_2318_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v_00_u03b1_2309_, v_k_2310_, v_allowLevelAssignments_boxed_2317_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
return v_res_2318_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object* v___x_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_toCold_2328_; lean_object* v_options_2329_; uint8_t v_hasTrace_2330_; 
v_toCold_2328_ = lean_ctor_get(v___y_2325_, 0);
v_options_2329_ = lean_ctor_get(v_toCold_2328_, 2);
v_hasTrace_2330_ = lean_ctor_get_uint8(v_options_2329_, sizeof(void*)*1);
if (v_hasTrace_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_dec(v___x_2322_);
v___x_2331_ = lean_box(v_hasTrace_2330_);
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
return v___x_2332_;
}
else
{
lean_object* v_inheritedTraceOptions_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v_inheritedTraceOptions_2333_ = lean_ctor_get(v_toCold_2328_, 11);
v___x_2334_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_2335_ = l_Lean_Name_append(v___x_2334_, v___x_2322_);
v___x_2336_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2333_, v_options_2329_, v___x_2335_);
lean_dec(v___x_2335_);
v___x_2337_ = lean_box(v___x_2336_);
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
return v___x_2338_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2322_ = stack[0].m_obj;
lean_object* v___y_2323_ = stack[1].m_obj;
lean_object* v___y_2324_ = stack[2].m_obj;
lean_object* v___y_2325_ = stack[3].m_obj;
lean_object* v___y_2326_ = stack[4].m_obj;
lean_object* v_res_2339_;
v_res_2339_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
stack->m_obj
 = v_res_2339_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v___x_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2346_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(lean_object* v_o_2347_, lean_object* v_k_2348_, uint8_t v_v_2349_){
_start:
{
lean_object* v_map_2350_; uint8_t v_hasTrace_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2365_; 
v_map_2350_ = lean_ctor_get(v_o_2347_, 0);
v_hasTrace_2351_ = lean_ctor_get_uint8(v_o_2347_, sizeof(void*)*1);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_o_2347_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2353_ = v_o_2347_;
v_isShared_2354_ = v_isSharedCheck_2365_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_map_2350_);
lean_dec(v_o_2347_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2365_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2355_, 0, v_v_2349_);
lean_inc(v_k_2348_);
v___x_2356_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2348_, v___x_2355_, v_map_2350_);
if (v_hasTrace_2351_ == 0)
{
lean_object* v___x_2357_; uint8_t v___x_2358_; lean_object* v___x_2360_; 
v___x_2357_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
v___x_2358_ = l_Lean_Name_isPrefixOf(v___x_2357_, v_k_2348_);
lean_dec(v_k_2348_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2356_);
v___x_2360_ = v___x_2353_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2356_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_ctor_set_uint8(v___x_2360_, sizeof(void*)*1, v___x_2358_);
return v___x_2360_;
}
}
else
{
lean_object* v___x_2363_; 
lean_dec(v_k_2348_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2356_);
v___x_2363_ = v___x_2353_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*1, v_hasTrace_2351_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_2347_ = stack[0].m_obj;
lean_object* v_k_2348_ = stack[1].m_obj;
uint8_t v_v_2349_ = stack[2].m_num;
lean_object* v_res_2366_;
v_res_2366_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(v_o_2347_, v_k_2348_, v_v_2349_);
stack->m_obj
 = v_res_2366_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3___boxed(lean_object* v_o_2367_, lean_object* v_k_2368_, lean_object* v_v_2369_){
_start:
{
uint8_t v_v_boxed_2370_; lean_object* v_res_2371_; 
v_v_boxed_2370_ = lean_unbox(v_v_2369_);
v_res_2371_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(v_o_2367_, v_k_2368_, v_v_boxed_2370_);
return v_res_2371_;
}
}
lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_2372_, lean_object* v_opt_2373_, uint8_t v_val_2374_){
_start:
{
lean_object* v_name_2375_; lean_object* v___x_2376_; 
v_name_2375_ = lean_ctor_get(v_opt_2373_, 0);
lean_inc(v_name_2375_);
lean_dec_ref(v_opt_2373_);
v___x_2376_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_spec__3(v_opts_2372_, v_name_2375_, v_val_2374_);
return v___x_2376_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2372_ = stack[0].m_obj;
lean_object* v_opt_2373_ = stack[1].m_obj;
uint8_t v_val_2374_ = stack[2].m_num;
lean_object* v_res_2377_;
v_res_2377_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_2372_, v_opt_2373_, v_val_2374_);
stack->m_obj
 = v_res_2377_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_2378_, lean_object* v_opt_2379_, lean_object* v_val_2380_){
_start:
{
uint8_t v_val_boxed_2381_; lean_object* v_res_2382_; 
v_val_boxed_2381_ = lean_unbox(v_val_2380_);
v_res_2382_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_2378_, v_opt_2379_, v_val_boxed_2381_);
return v_res_2382_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object* v_mvarId_2383_, uint8_t v___x_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___y_2391_; uint16_t v___y_2392_; lean_object* v_fileName_2393_; lean_object* v_fileMap_2394_; lean_object* v_currNamespace_2395_; lean_object* v_openDecls_2396_; lean_object* v_initHeartbeats_2397_; lean_object* v_maxHeartbeats_2398_; lean_object* v_quotContext_2399_; lean_object* v_currMacroScope_2400_; lean_object* v_cancelTk_x3f_2401_; lean_object* v_inheritedTraceOptions_2402_; lean_object* v_currRecDepth_2403_; lean_object* v_ref_2404_; uint8_t v_suppressElabErrors_2405_; uint8_t v_isRecordingDeps_2406_; lean_object* v___y_2407_; lean_object* v_toCold_2413_; lean_object* v_currRecDepth_2414_; lean_object* v_ref_2415_; uint8_t v_suppressElabErrors_2416_; uint8_t v_isRecordingDeps_2417_; lean_object* v_fileName_2418_; lean_object* v_fileMap_2419_; lean_object* v_options_2420_; lean_object* v_currNamespace_2421_; lean_object* v_openDecls_2422_; lean_object* v_initHeartbeats_2423_; lean_object* v_maxHeartbeats_2424_; lean_object* v_quotContext_2425_; lean_object* v_currMacroScope_2426_; lean_object* v_cancelTk_x3f_2427_; lean_object* v_inheritedTraceOptions_2428_; uint8_t v___y_2430_; lean_object* v___y_2431_; uint16_t v___y_2432_; lean_object* v___y_2455_; 
v_toCold_2413_ = lean_ctor_get(v___y_2387_, 0);
v_currRecDepth_2414_ = lean_ctor_get(v___y_2387_, 1);
v_ref_2415_ = lean_ctor_get(v___y_2387_, 2);
v_suppressElabErrors_2416_ = lean_ctor_get_uint8(v___y_2387_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2417_ = lean_ctor_get_uint8(v___y_2387_, sizeof(void*)*3 + 3);
v_fileName_2418_ = lean_ctor_get(v_toCold_2413_, 0);
v_fileMap_2419_ = lean_ctor_get(v_toCold_2413_, 1);
v_options_2420_ = lean_ctor_get(v_toCold_2413_, 2);
v_currNamespace_2421_ = lean_ctor_get(v_toCold_2413_, 4);
v_openDecls_2422_ = lean_ctor_get(v_toCold_2413_, 5);
v_initHeartbeats_2423_ = lean_ctor_get(v_toCold_2413_, 6);
v_maxHeartbeats_2424_ = lean_ctor_get(v_toCold_2413_, 7);
v_quotContext_2425_ = lean_ctor_get(v_toCold_2413_, 8);
v_currMacroScope_2426_ = lean_ctor_get(v_toCold_2413_, 9);
v_cancelTk_x3f_2427_ = lean_ctor_get(v_toCold_2413_, 10);
v_inheritedTraceOptions_2428_ = lean_ctor_get(v_toCold_2413_, 11);
if (v_isRecordingDeps_2417_ == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = l_Lean_Meta_smartUnfolding;
lean_inc_ref(v_options_2420_);
v___x_2466_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_options_2420_, v___x_2465_, v_isRecordingDeps_2417_);
v___y_2455_ = v___x_2466_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2467_; 
lean_inc_ref(v_options_2420_);
v___x_2467_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2420_);
v___y_2455_ = v___x_2467_;
goto v___jp_2454_;
}
v___jp_2390_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2408_ = l_Lean_maxRecDepth;
v___x_2409_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___y_2391_, v___x_2408_);
v___x_2410_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2410_, 0, v_fileName_2393_);
lean_ctor_set(v___x_2410_, 1, v_fileMap_2394_);
lean_ctor_set(v___x_2410_, 2, v___y_2391_);
lean_ctor_set(v___x_2410_, 3, v___x_2409_);
lean_ctor_set(v___x_2410_, 4, v_currNamespace_2395_);
lean_ctor_set(v___x_2410_, 5, v_openDecls_2396_);
lean_ctor_set(v___x_2410_, 6, v_initHeartbeats_2397_);
lean_ctor_set(v___x_2410_, 7, v_maxHeartbeats_2398_);
lean_ctor_set(v___x_2410_, 8, v_quotContext_2399_);
lean_ctor_set(v___x_2410_, 9, v_currMacroScope_2400_);
lean_ctor_set(v___x_2410_, 10, v_cancelTk_x3f_2401_);
lean_ctor_set(v___x_2410_, 11, v_inheritedTraceOptions_2402_);
lean_inc(v_ref_2404_);
lean_inc(v_currRecDepth_2403_);
v___x_2411_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v_currRecDepth_2403_);
lean_ctor_set(v___x_2411_, 2, v_ref_2404_);
lean_ctor_set_uint16(v___x_2411_, sizeof(void*)*3, v___y_2392_);
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*3 + 2, v_suppressElabErrors_2405_);
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*3 + 3, v_isRecordingDeps_2406_);
v___x_2412_ = l_Lean_MVarId_refl(v_mvarId_2383_, v___x_2384_, v___y_2385_, v___y_2386_, v___x_2411_, v___y_2407_);
lean_dec_ref_known(v___x_2411_, 3);
return v___x_2412_;
}
v___jp_2429_:
{
lean_object* v___x_2433_; lean_object* v_env_2434_; lean_object* v_nextMacroScope_2435_; lean_object* v_ngen_2436_; lean_object* v_auxDeclNGen_2437_; lean_object* v_traceState_2438_; lean_object* v_recordedDeps_2439_; lean_object* v_messages_2440_; lean_object* v_infoState_2441_; lean_object* v_snapshotTasks_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2452_; 
v___x_2433_ = lean_st_ref_take(v___y_2388_);
v_env_2434_ = lean_ctor_get(v___x_2433_, 0);
v_nextMacroScope_2435_ = lean_ctor_get(v___x_2433_, 1);
v_ngen_2436_ = lean_ctor_get(v___x_2433_, 2);
v_auxDeclNGen_2437_ = lean_ctor_get(v___x_2433_, 3);
v_traceState_2438_ = lean_ctor_get(v___x_2433_, 4);
v_recordedDeps_2439_ = lean_ctor_get(v___x_2433_, 6);
v_messages_2440_ = lean_ctor_get(v___x_2433_, 7);
v_infoState_2441_ = lean_ctor_get(v___x_2433_, 8);
v_snapshotTasks_2442_ = lean_ctor_get(v___x_2433_, 9);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2452_ == 0)
{
lean_object* v_unused_2453_; 
v_unused_2453_ = lean_ctor_get(v___x_2433_, 5);
lean_dec(v_unused_2453_);
v___x_2444_ = v___x_2433_;
v_isShared_2445_ = v_isSharedCheck_2452_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_snapshotTasks_2442_);
lean_inc(v_infoState_2441_);
lean_inc(v_messages_2440_);
lean_inc(v_recordedDeps_2439_);
lean_inc(v_traceState_2438_);
lean_inc(v_auxDeclNGen_2437_);
lean_inc(v_ngen_2436_);
lean_inc(v_nextMacroScope_2435_);
lean_inc(v_env_2434_);
lean_dec(v___x_2433_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2452_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2446_ = l_Lean_Kernel_enableDiag(v_env_2434_, v___y_2430_);
v___x_2447_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 5, v___x_2447_);
lean_ctor_set(v___x_2444_, 0, v___x_2446_);
v___x_2449_ = v___x_2444_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_nextMacroScope_2435_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_ngen_2436_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v_auxDeclNGen_2437_);
lean_ctor_set(v_reuseFailAlloc_2451_, 4, v_traceState_2438_);
lean_ctor_set(v_reuseFailAlloc_2451_, 5, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2451_, 6, v_recordedDeps_2439_);
lean_ctor_set(v_reuseFailAlloc_2451_, 7, v_messages_2440_);
lean_ctor_set(v_reuseFailAlloc_2451_, 8, v_infoState_2441_);
lean_ctor_set(v_reuseFailAlloc_2451_, 9, v_snapshotTasks_2442_);
v___x_2449_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_st_ref_put(v___y_2388_, v___x_2449_);
lean_inc_ref(v_inheritedTraceOptions_2428_);
lean_inc(v_cancelTk_x3f_2427_);
lean_inc(v_currMacroScope_2426_);
lean_inc(v_quotContext_2425_);
lean_inc(v_maxHeartbeats_2424_);
lean_inc(v_initHeartbeats_2423_);
lean_inc(v_openDecls_2422_);
lean_inc(v_currNamespace_2421_);
lean_inc_ref(v_fileMap_2419_);
lean_inc_ref(v_fileName_2418_);
v___y_2391_ = v___y_2431_;
v___y_2392_ = v___y_2432_;
v_fileName_2393_ = v_fileName_2418_;
v_fileMap_2394_ = v_fileMap_2419_;
v_currNamespace_2395_ = v_currNamespace_2421_;
v_openDecls_2396_ = v_openDecls_2422_;
v_initHeartbeats_2397_ = v_initHeartbeats_2423_;
v_maxHeartbeats_2398_ = v_maxHeartbeats_2424_;
v_quotContext_2399_ = v_quotContext_2425_;
v_currMacroScope_2400_ = v_currMacroScope_2426_;
v_cancelTk_x3f_2401_ = v_cancelTk_x3f_2427_;
v_inheritedTraceOptions_2402_ = v_inheritedTraceOptions_2428_;
v_currRecDepth_2403_ = v_currRecDepth_2414_;
v_ref_2404_ = v_ref_2415_;
v_suppressElabErrors_2405_ = v_suppressElabErrors_2416_;
v_isRecordingDeps_2406_ = v_isRecordingDeps_2417_;
v___y_2407_ = v___y_2388_;
goto v___jp_2390_;
}
}
}
v___jp_2454_:
{
uint16_t v___x_2456_; lean_object* v___x_2457_; lean_object* v_env_2458_; uint8_t v___x_2459_; uint16_t v___x_2460_; uint16_t v___x_2461_; uint16_t v___x_2462_; uint8_t v___x_2463_; 
v___x_2456_ = l_Lean_OptionFlags_ofOptions(v___y_2455_);
v___x_2457_ = lean_st_ref_get(v___y_2388_);
v_env_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc_ref(v_env_2458_);
lean_dec(v___x_2457_);
v___x_2459_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2458_);
lean_dec_ref(v_env_2458_);
v___x_2460_ = 512;
v___x_2461_ = lean_uint16_land(v___x_2456_, v___x_2460_);
v___x_2462_ = 0;
v___x_2463_ = lean_uint16_dec_eq(v___x_2461_, v___x_2462_);
if (v___x_2463_ == 0)
{
if (v___x_2459_ == 0)
{
v___y_2430_ = v___x_2384_;
v___y_2431_ = v___y_2455_;
v___y_2432_ = v___x_2456_;
goto v___jp_2429_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2428_);
lean_inc(v_cancelTk_x3f_2427_);
lean_inc(v_currMacroScope_2426_);
lean_inc(v_quotContext_2425_);
lean_inc(v_maxHeartbeats_2424_);
lean_inc(v_initHeartbeats_2423_);
lean_inc(v_openDecls_2422_);
lean_inc(v_currNamespace_2421_);
lean_inc_ref(v_fileMap_2419_);
lean_inc_ref(v_fileName_2418_);
v___y_2391_ = v___y_2455_;
v___y_2392_ = v___x_2456_;
v_fileName_2393_ = v_fileName_2418_;
v_fileMap_2394_ = v_fileMap_2419_;
v_currNamespace_2395_ = v_currNamespace_2421_;
v_openDecls_2396_ = v_openDecls_2422_;
v_initHeartbeats_2397_ = v_initHeartbeats_2423_;
v_maxHeartbeats_2398_ = v_maxHeartbeats_2424_;
v_quotContext_2399_ = v_quotContext_2425_;
v_currMacroScope_2400_ = v_currMacroScope_2426_;
v_cancelTk_x3f_2401_ = v_cancelTk_x3f_2427_;
v_inheritedTraceOptions_2402_ = v_inheritedTraceOptions_2428_;
v_currRecDepth_2403_ = v_currRecDepth_2414_;
v_ref_2404_ = v_ref_2415_;
v_suppressElabErrors_2405_ = v_suppressElabErrors_2416_;
v_isRecordingDeps_2406_ = v_isRecordingDeps_2417_;
v___y_2407_ = v___y_2388_;
goto v___jp_2390_;
}
}
else
{
if (v___x_2459_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2428_);
lean_inc(v_cancelTk_x3f_2427_);
lean_inc(v_currMacroScope_2426_);
lean_inc(v_quotContext_2425_);
lean_inc(v_maxHeartbeats_2424_);
lean_inc(v_initHeartbeats_2423_);
lean_inc(v_openDecls_2422_);
lean_inc(v_currNamespace_2421_);
lean_inc_ref(v_fileMap_2419_);
lean_inc_ref(v_fileName_2418_);
v___y_2391_ = v___y_2455_;
v___y_2392_ = v___x_2456_;
v_fileName_2393_ = v_fileName_2418_;
v_fileMap_2394_ = v_fileMap_2419_;
v_currNamespace_2395_ = v_currNamespace_2421_;
v_openDecls_2396_ = v_openDecls_2422_;
v_initHeartbeats_2397_ = v_initHeartbeats_2423_;
v_maxHeartbeats_2398_ = v_maxHeartbeats_2424_;
v_quotContext_2399_ = v_quotContext_2425_;
v_currMacroScope_2400_ = v_currMacroScope_2426_;
v_cancelTk_x3f_2401_ = v_cancelTk_x3f_2427_;
v_inheritedTraceOptions_2402_ = v_inheritedTraceOptions_2428_;
v_currRecDepth_2403_ = v_currRecDepth_2414_;
v_ref_2404_ = v_ref_2415_;
v_suppressElabErrors_2405_ = v_suppressElabErrors_2416_;
v_isRecordingDeps_2406_ = v_isRecordingDeps_2417_;
v___y_2407_ = v___y_2388_;
goto v___jp_2390_;
}
else
{
uint8_t v___x_2464_; 
v___x_2464_ = 0;
v___y_2430_ = v___x_2464_;
v___y_2431_ = v___y_2455_;
v___y_2432_ = v___x_2456_;
goto v___jp_2429_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2383_ = stack[0].m_obj;
uint8_t v___x_2384_ = stack[1].m_num;
lean_object* v___y_2385_ = stack[2].m_obj;
lean_object* v___y_2386_ = stack[3].m_obj;
lean_object* v___y_2387_ = stack[4].m_obj;
lean_object* v___y_2388_ = stack[5].m_obj;
lean_object* v_res_2468_;
v_res_2468_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_mvarId_2383_, v___x_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
stack->m_obj
 = v_res_2468_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(lean_object* v_mvarId_2469_, lean_object* v___x_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
uint8_t v___x_10356__boxed_2476_; lean_object* v_res_2477_; 
v___x_10356__boxed_2476_ = lean_unbox(v___x_2470_);
v_res_2477_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_mvarId_2469_, v___x_10356__boxed_2476_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2477_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2478_; double v___x_2479_; 
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = lean_float_of_nat(v___x_2478_);
return v___x_2479_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(lean_object* v_cls_2483_, lean_object* v_msg_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_ref_2490_; lean_object* v___x_2491_; lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2537_; 
v_ref_2490_ = lean_ctor_get(v___y_2487_, 2);
v___x_2491_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0_spec__0(v_msg_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2537_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2537_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v_traceState_2497_; lean_object* v_env_2498_; lean_object* v_nextMacroScope_2499_; lean_object* v_ngen_2500_; lean_object* v_auxDeclNGen_2501_; lean_object* v_cache_2502_; lean_object* v_recordedDeps_2503_; lean_object* v_messages_2504_; lean_object* v_infoState_2505_; lean_object* v_snapshotTasks_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2536_; 
v___x_2496_ = lean_st_ref_take(v___y_2488_);
v_traceState_2497_ = lean_ctor_get(v___x_2496_, 4);
v_env_2498_ = lean_ctor_get(v___x_2496_, 0);
v_nextMacroScope_2499_ = lean_ctor_get(v___x_2496_, 1);
v_ngen_2500_ = lean_ctor_get(v___x_2496_, 2);
v_auxDeclNGen_2501_ = lean_ctor_get(v___x_2496_, 3);
v_cache_2502_ = lean_ctor_get(v___x_2496_, 5);
v_recordedDeps_2503_ = lean_ctor_get(v___x_2496_, 6);
v_messages_2504_ = lean_ctor_get(v___x_2496_, 7);
v_infoState_2505_ = lean_ctor_get(v___x_2496_, 8);
v_snapshotTasks_2506_ = lean_ctor_get(v___x_2496_, 9);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2508_ = v___x_2496_;
v_isShared_2509_ = v_isSharedCheck_2536_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_snapshotTasks_2506_);
lean_inc(v_infoState_2505_);
lean_inc(v_messages_2504_);
lean_inc(v_recordedDeps_2503_);
lean_inc(v_cache_2502_);
lean_inc(v_traceState_2497_);
lean_inc(v_auxDeclNGen_2501_);
lean_inc(v_ngen_2500_);
lean_inc(v_nextMacroScope_2499_);
lean_inc(v_env_2498_);
lean_dec(v___x_2496_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2536_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
uint64_t v_tid_2510_; lean_object* v_traces_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2535_; 
v_tid_2510_ = lean_ctor_get_uint64(v_traceState_2497_, sizeof(void*)*1);
v_traces_2511_ = lean_ctor_get(v_traceState_2497_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_traceState_2497_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2513_ = v_traceState_2497_;
v_isShared_2514_ = v_isSharedCheck_2535_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_traces_2511_);
lean_dec(v_traceState_2497_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2535_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; double v___x_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2515_ = lean_box(0);
v___x_2516_ = lean_box(0);
v___x_2517_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__0);
v___x_2518_ = 0;
v___x_2519_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__1));
v___x_2520_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2520_, 0, v_cls_2483_);
lean_ctor_set(v___x_2520_, 1, v___x_2516_);
lean_ctor_set(v___x_2520_, 2, v___x_2519_);
lean_ctor_set_float(v___x_2520_, sizeof(void*)*3, v___x_2517_);
lean_ctor_set_float(v___x_2520_, sizeof(void*)*3 + 8, v___x_2517_);
lean_ctor_set_uint8(v___x_2520_, sizeof(void*)*3 + 16, v___x_2518_);
v___x_2521_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___closed__2));
v___x_2522_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v_a_2492_);
lean_ctor_set(v___x_2522_, 2, v___x_2521_);
lean_inc(v_ref_2490_);
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v_ref_2490_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = l_Lean_PersistentArray_push___redArg(v_traces_2511_, v___x_2523_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2524_);
v___x_2526_ = v___x_2513_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2524_);
lean_ctor_set_uint64(v_reuseFailAlloc_2534_, sizeof(void*)*1, v_tid_2510_);
v___x_2526_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2528_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 4, v___x_2526_);
v___x_2528_ = v___x_2508_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_env_2498_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_nextMacroScope_2499_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v_ngen_2500_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v_auxDeclNGen_2501_);
lean_ctor_set(v_reuseFailAlloc_2533_, 4, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2533_, 5, v_cache_2502_);
lean_ctor_set(v_reuseFailAlloc_2533_, 6, v_recordedDeps_2503_);
lean_ctor_set(v_reuseFailAlloc_2533_, 7, v_messages_2504_);
lean_ctor_set(v_reuseFailAlloc_2533_, 8, v_infoState_2505_);
lean_ctor_set(v_reuseFailAlloc_2533_, 9, v_snapshotTasks_2506_);
v___x_2528_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_st_ref_put(v___y_2488_, v___x_2528_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2515_);
v___x_2531_ = v___x_2494_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2515_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2483_ = stack[0].m_obj;
lean_object* v_msg_2484_ = stack[1].m_obj;
lean_object* v___y_2485_ = stack[2].m_obj;
lean_object* v___y_2486_ = stack[3].m_obj;
lean_object* v___y_2487_ = stack[4].m_obj;
lean_object* v___y_2488_ = stack[5].m_obj;
lean_object* v_res_2538_;
v_res_2538_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_cls_2483_, v_msg_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
stack->m_obj
 = v_res_2538_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_cls_2539_, lean_object* v_msg_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_cls_2539_, v_msg_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
return v_res_2546_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object* v_a_2556_, lean_object* v___x_2557_, lean_object* v___f_2558_, lean_object* v_fixEq_x3f_2559_, lean_object* v_declName_2560_, lean_object* v___x_2561_, lean_object* v___x_2562_, lean_object* v_fixedParamPerms_2563_, lean_object* v_declNameNonRec_2564_, lean_object* v_____r_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v_mvarId_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; 
if (lean_obj_tag(v_fixEq_x3f_2559_) == 1)
{
lean_object* v_val_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2715_; 
v_val_2660_ = lean_ctor_get(v_fixEq_x3f_2559_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_fixEq_x3f_2559_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2662_ = v_fixEq_x3f_2559_;
v_isShared_2663_ = v_isSharedCheck_2715_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_val_2660_);
lean_dec(v_fixEq_x3f_2559_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2715_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; 
v___x_2664_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_2560_, v___x_2561_, v___x_2562_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___x_2682_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
lean_inc_ref(v___f_2558_);
lean_inc(v___y_2569_);
lean_inc_ref(v___y_2568_);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
v___x_2682_ = lean_apply_5(v___f_2558_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, lean_box(0));
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; uint8_t v___x_2684_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = lean_unbox(v_a_2683_);
lean_dec(v_a_2683_);
if (v___x_2684_ == 0)
{
lean_del_object(v___x_2662_);
v___y_2667_ = v___y_2566_;
v___y_2668_ = v___y_2567_;
v___y_2669_ = v___y_2568_;
v___y_2670_ = v___y_2569_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2685_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5);
lean_inc(v_a_2665_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v_a_2665_);
v___x_2687_ = v___x_2662_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2665_);
v___x_2687_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2685_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
lean_inc(v___x_2557_);
v___x_2689_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2557_, v___x_2688_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_dec_ref_known(v___x_2689_, 1);
v___y_2667_ = v___y_2566_;
v___y_2668_ = v___y_2567_;
v___y_2669_ = v___y_2568_;
v___y_2670_ = v___y_2569_;
goto v___jp_2666_;
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v_a_2665_);
lean_dec(v_val_2660_);
lean_dec(v_declNameNonRec_2564_);
lean_dec_ref(v_fixedParamPerms_2563_);
lean_dec_ref(v___f_2558_);
lean_dec(v___x_2557_);
lean_dec_ref(v_a_2556_);
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
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
}
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v_a_2665_);
lean_del_object(v___x_2662_);
lean_dec(v_val_2660_);
lean_dec(v_declNameNonRec_2564_);
lean_dec_ref(v_fixedParamPerms_2563_);
lean_dec_ref(v___f_2558_);
lean_dec(v___x_2557_);
lean_dec_ref(v_a_2556_);
v_a_2699_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2682_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2682_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
v___jp_2666_:
{
lean_object* v_numFixed_2671_; lean_object* v___x_2672_; 
v_numFixed_2671_ = lean_ctor_get(v_fixedParamPerms_2563_, 0);
lean_inc(v_numFixed_2671_);
lean_dec_ref(v_fixedParamPerms_2563_);
v___x_2672_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEqWith(v_declNameNonRec_2564_, v_val_2660_, v_numFixed_2671_, v_a_2665_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v_mvarId_2632_ = v_a_2673_;
v___y_2633_ = v___y_2667_;
v___y_2634_ = v___y_2668_;
v___y_2635_ = v___y_2669_;
v___y_2636_ = v___y_2670_;
goto v___jp_2631_;
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec_ref(v___f_2558_);
lean_dec(v___x_2557_);
lean_dec_ref(v_a_2556_);
v_a_2674_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2672_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2672_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_del_object(v___x_2662_);
lean_dec(v_val_2660_);
lean_dec(v_declNameNonRec_2564_);
lean_dec_ref(v_fixedParamPerms_2563_);
lean_dec_ref(v___f_2558_);
lean_dec(v___x_2557_);
lean_dec_ref(v_a_2556_);
v_a_2707_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2664_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2664_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
else
{
lean_object* v___x_2716_; 
lean_dec_ref(v_fixedParamPerms_2563_);
lean_dec(v___x_2561_);
lean_dec(v_fixEq_x3f_2559_);
v___x_2716_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_2560_, v_declNameNonRec_2564_, v___x_2562_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___x_2733_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
lean_inc_ref(v___f_2558_);
lean_inc(v___y_2569_);
lean_inc_ref(v___y_2568_);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
v___x_2733_ = lean_apply_5(v___f_2558_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, lean_box(0));
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; uint8_t v___x_2735_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2735_ = lean_unbox(v_a_2734_);
lean_dec(v_a_2734_);
if (v___x_2735_ == 0)
{
v___y_2719_ = v___y_2566_;
v___y_2720_ = v___y_2567_;
v___y_2721_ = v___y_2568_;
v___y_2722_ = v___y_2569_;
goto v___jp_2718_;
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2736_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5);
lean_inc(v_a_2717_);
v___x_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2737_, 0, v_a_2717_);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
lean_inc(v___x_2557_);
v___x_2739_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2557_, v___x_2738_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_dec_ref_known(v___x_2739_, 1);
v___y_2719_ = v___y_2566_;
v___y_2720_ = v___y_2567_;
v___y_2721_ = v___y_2568_;
v___y_2722_ = v___y_2569_;
goto v___jp_2718_;
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v_a_2717_);
lean_dec_ref(v___f_2558_);
lean_dec(v___x_2557_);
lean_dec_ref(v_a_2556_);
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v_a_2717_);
lean_dec_ref(v___f_2558_);
lean_dec(v___x_2557_);
lean_dec_ref(v_a_2556_);
v_a_2748_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2733_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2733_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
v___jp_2718_:
{
lean_object* v___x_2723_; 
v___x_2723_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_a_2717_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref_known(v___x_2723_, 1);
v_mvarId_2632_ = v_a_2724_;
v___y_2633_ = v___y_2719_;
v___y_2634_ = v___y_2720_;
v___y_2635_ = v___y_2721_;
v___y_2636_ = v___y_2722_;
goto v___jp_2631_;
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref(v___f_2558_);
lean_dec(v___x_2557_);
lean_dec_ref(v_a_2556_);
v_a_2725_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2723_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2723_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec_ref(v___f_2558_);
lean_dec(v___x_2557_);
lean_dec_ref(v_a_2556_);
v_a_2756_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2716_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2716_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
v___jp_2571_:
{
if (lean_obj_tag(v___y_2576_) == 0)
{
lean_object* v_toCold_2577_; lean_object* v_options_2578_; uint8_t v_hasTrace_2579_; 
lean_dec_ref_known(v___y_2576_, 1);
v_toCold_2577_ = lean_ctor_get(v___y_2575_, 0);
v_options_2578_ = lean_ctor_get(v_toCold_2577_, 2);
v_hasTrace_2579_ = lean_ctor_get_uint8(v_options_2578_, sizeof(void*)*1);
if (v_hasTrace_2579_ == 0)
{
lean_object* v___x_2580_; 
lean_dec(v___x_2557_);
v___x_2580_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2556_, v___y_2573_);
return v___x_2580_;
}
else
{
lean_object* v_inheritedTraceOptions_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_inheritedTraceOptions_2581_ = lean_ctor_get(v_toCold_2577_, 11);
v___x_2582_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1));
lean_inc(v___x_2557_);
v___x_2583_ = l_Lean_Name_append(v___x_2582_, v___x_2557_);
v___x_2584_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2581_, v_options_2578_, v___x_2583_);
lean_dec(v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; 
lean_dec(v___x_2557_);
v___x_2585_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2556_, v___y_2573_);
return v___x_2585_;
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1);
v___x_2587_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2557_, v___x_2586_, v___y_2572_, v___y_2573_, v___y_2575_, v___y_2574_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v___x_2588_; 
lean_dec_ref_known(v___x_2587_, 1);
v___x_2588_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0___redArg(v_a_2556_, v___y_2573_);
return v___x_2588_;
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v_a_2556_);
v_a_2589_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2587_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2587_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v___x_2557_);
lean_dec_ref(v_a_2556_);
v_a_2597_ = lean_ctor_get(v___y_2576_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___y_2576_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___y_2576_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___y_2576_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
v___jp_2605_:
{
lean_object* v___x_2611_; uint8_t v_transparency_2612_; uint8_t v___x_2613_; uint8_t v___x_2614_; uint8_t v___x_2615_; 
v___x_2611_ = l_Lean_Meta_Context_config(v___y_2609_);
v_transparency_2612_ = lean_ctor_get_uint8(v___x_2611_, 9);
lean_dec_ref(v___x_2611_);
v___x_2613_ = 0;
v___x_2614_ = 1;
v___x_2615_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2612_, v___x_2613_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; 
v___x_2616_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v___y_2606_, v___x_2614_, v___y_2609_, v___y_2610_, v___y_2608_, v___y_2607_);
v___y_2572_ = v___y_2609_;
v___y_2573_ = v___y_2610_;
v___y_2574_ = v___y_2607_;
v___y_2575_ = v___y_2608_;
v___y_2576_ = v___x_2616_;
goto v___jp_2571_;
}
else
{
lean_object* v_keyedConfig_2617_; uint8_t v_trackZetaDelta_2618_; lean_object* v_zetaDeltaSet_2619_; lean_object* v_lctx_2620_; lean_object* v_localInstances_2621_; lean_object* v_defEqCtx_x3f_2622_; lean_object* v_synthPendingDepth_2623_; lean_object* v_customCanUnfoldPredicate_x3f_2624_; uint8_t v_univApprox_2625_; uint8_t v_inTypeClassResolution_2626_; uint8_t v_cacheInferType_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_keyedConfig_2617_ = lean_ctor_get(v___y_2609_, 0);
v_trackZetaDelta_2618_ = lean_ctor_get_uint8(v___y_2609_, sizeof(void*)*7);
v_zetaDeltaSet_2619_ = lean_ctor_get(v___y_2609_, 1);
v_lctx_2620_ = lean_ctor_get(v___y_2609_, 2);
v_localInstances_2621_ = lean_ctor_get(v___y_2609_, 3);
v_defEqCtx_x3f_2622_ = lean_ctor_get(v___y_2609_, 4);
v_synthPendingDepth_2623_ = lean_ctor_get(v___y_2609_, 5);
v_customCanUnfoldPredicate_x3f_2624_ = lean_ctor_get(v___y_2609_, 6);
v_univApprox_2625_ = lean_ctor_get_uint8(v___y_2609_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2626_ = lean_ctor_get_uint8(v___y_2609_, sizeof(void*)*7 + 2);
v_cacheInferType_2627_ = lean_ctor_get_uint8(v___y_2609_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2617_);
v___x_2628_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2613_, v_keyedConfig_2617_);
lean_inc(v_customCanUnfoldPredicate_x3f_2624_);
lean_inc(v_synthPendingDepth_2623_);
lean_inc(v_defEqCtx_x3f_2622_);
lean_inc_ref(v_localInstances_2621_);
lean_inc_ref(v_lctx_2620_);
lean_inc(v_zetaDeltaSet_2619_);
v___x_2629_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
lean_ctor_set(v___x_2629_, 1, v_zetaDeltaSet_2619_);
lean_ctor_set(v___x_2629_, 2, v_lctx_2620_);
lean_ctor_set(v___x_2629_, 3, v_localInstances_2621_);
lean_ctor_set(v___x_2629_, 4, v_defEqCtx_x3f_2622_);
lean_ctor_set(v___x_2629_, 5, v_synthPendingDepth_2623_);
lean_ctor_set(v___x_2629_, 6, v_customCanUnfoldPredicate_x3f_2624_);
lean_ctor_set_uint8(v___x_2629_, sizeof(void*)*7, v_trackZetaDelta_2618_);
lean_ctor_set_uint8(v___x_2629_, sizeof(void*)*7 + 1, v_univApprox_2625_);
lean_ctor_set_uint8(v___x_2629_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2626_);
lean_ctor_set_uint8(v___x_2629_, sizeof(void*)*7 + 3, v_cacheInferType_2627_);
v___x_2630_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v___y_2606_, v___x_2614_, v___x_2629_, v___y_2610_, v___y_2608_, v___y_2607_);
lean_dec_ref_known(v___x_2629_, 7);
v___y_2572_ = v___y_2609_;
v___y_2573_ = v___y_2610_;
v___y_2574_ = v___y_2607_;
v___y_2575_ = v___y_2608_;
v___y_2576_ = v___x_2630_;
goto v___jp_2571_;
}
}
v___jp_2631_:
{
lean_object* v___x_2637_; 
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2635_);
lean_inc(v___y_2634_);
lean_inc_ref(v___y_2633_);
v___x_2637_ = lean_apply_5(v___f_2558_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, lean_box(0));
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; uint8_t v___x_2639_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
v___x_2639_ = lean_unbox(v_a_2638_);
lean_dec(v_a_2638_);
if (v___x_2639_ == 0)
{
v___y_2606_ = v_mvarId_2632_;
v___y_2607_ = v___y_2636_;
v___y_2608_ = v___y_2635_;
v___y_2609_ = v___y_2633_;
v___y_2610_ = v___y_2634_;
goto v___jp_2605_;
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2640_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3);
lean_inc(v_mvarId_2632_);
v___x_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_mvarId_2632_);
v___x_2642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
lean_inc(v___x_2557_);
v___x_2643_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2557_, v___x_2642_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_dec_ref_known(v___x_2643_, 1);
v___y_2606_ = v_mvarId_2632_;
v___y_2607_ = v___y_2636_;
v___y_2608_ = v___y_2635_;
v___y_2609_ = v___y_2633_;
v___y_2610_ = v___y_2634_;
goto v___jp_2605_;
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_mvarId_2632_);
lean_dec(v___x_2557_);
lean_dec_ref(v_a_2556_);
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v_mvarId_2632_);
lean_dec(v___x_2557_);
lean_dec_ref(v_a_2556_);
v_a_2652_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2637_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2637_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2556_ = stack[0].m_obj;
lean_object* v___x_2557_ = stack[1].m_obj;
lean_object* v___f_2558_ = stack[2].m_obj;
lean_object* v_fixEq_x3f_2559_ = stack[3].m_obj;
lean_object* v_declName_2560_ = stack[4].m_obj;
lean_object* v___x_2561_ = stack[5].m_obj;
lean_object* v___x_2562_ = stack[6].m_obj;
lean_object* v_fixedParamPerms_2563_ = stack[7].m_obj;
lean_object* v_declNameNonRec_2564_ = stack[8].m_obj;
lean_object* v_____r_2565_ = stack[9].m_obj;
lean_object* v___y_2566_ = stack[10].m_obj;
lean_object* v___y_2567_ = stack[11].m_obj;
lean_object* v___y_2568_ = stack[12].m_obj;
lean_object* v___y_2569_ = stack[13].m_obj;
lean_object* v_res_2764_;
v_res_2764_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2556_, v___x_2557_, v___f_2558_, v_fixEq_x3f_2559_, v_declName_2560_, v___x_2561_, v___x_2562_, v_fixedParamPerms_2563_, v_declNameNonRec_2564_, v_____r_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
stack->m_obj
 = v_res_2764_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(lean_object* v_a_2765_, lean_object* v___x_2766_, lean_object* v___f_2767_, lean_object* v_fixEq_x3f_2768_, lean_object* v_declName_2769_, lean_object* v___x_2770_, lean_object* v___x_2771_, lean_object* v_fixedParamPerms_2772_, lean_object* v_declNameNonRec_2773_, lean_object* v_____r_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2765_, v___x_2766_, v___f_2767_, v_fixEq_x3f_2768_, v_declName_2769_, v___x_2770_, v___x_2771_, v_fixedParamPerms_2772_, v_declNameNonRec_2773_, v_____r_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
return v_res_2780_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__0));
v___x_2783_ = l_Lean_stringToMessageData(v___x_2782_);
return v___x_2783_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__2));
v___x_2786_ = l_Lean_stringToMessageData(v___x_2785_);
return v___x_2786_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9(void){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__8));
v___x_2797_ = l_Lean_stringToMessageData(v___x_2796_);
return v___x_2797_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(lean_object* v_declName_2798_, lean_object* v_a_2799_, lean_object* v___x_2800_, lean_object* v_fixEq_x3f_2801_, lean_object* v_fixedParamPerms_2802_, lean_object* v_declNameNonRec_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___y_2810_; lean_object* v___y_2811_; uint8_t v___y_2812_; lean_object* v___y_2822_; lean_object* v_a_2823_; lean_object* v___y_2827_; lean_object* v___x_2829_; 
lean_inc(v___x_2800_);
v___x_2829_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2799_, v___x_2800_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___f_2833_; lean_object* v___x_2834_; lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2858_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2831_ = l_Lean_Expr_mvarId_x21(v_a_2830_);
v___x_2832_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__6));
v___f_2833_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__7));
v___x_2834_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_2832_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2837_ = v___x_2834_;
v_isShared_2838_ = v_isSharedCheck_2858_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2834_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2858_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
uint8_t v___x_2839_; 
v___x_2839_ = lean_unbox(v_a_2835_);
lean_dec(v_a_2835_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_del_object(v___x_2837_);
v___x_2840_ = lean_box(0);
lean_inc(v_declName_2798_);
v___x_2841_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2830_, v___x_2832_, v___f_2833_, v_fixEq_x3f_2801_, v_declName_2798_, v___x_2800_, v___x_2831_, v_fixedParamPerms_2802_, v_declNameNonRec_2803_, v___x_2840_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
v___y_2827_ = v___x_2841_;
goto v___jp_2826_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2842_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__9);
lean_inc(v___x_2831_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set_tag(v___x_2837_, 1);
lean_ctor_set(v___x_2837_, 0, v___x_2831_);
v___x_2844_ = v___x_2837_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2831_);
v___x_2844_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2842_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v___x_2832_, v___x_2845_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
lean_inc(v_declName_2798_);
v___x_2848_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_a_2830_, v___x_2832_, v___f_2833_, v_fixEq_x3f_2801_, v_declName_2798_, v___x_2800_, v___x_2831_, v_fixedParamPerms_2802_, v_declNameNonRec_2803_, v_a_2847_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
v___y_2827_ = v___x_2848_;
goto v___jp_2826_;
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v___x_2831_);
lean_dec(v_a_2830_);
lean_dec(v_declNameNonRec_2803_);
lean_dec_ref(v_fixedParamPerms_2802_);
lean_dec(v_fixEq_x3f_2801_);
lean_dec(v___x_2800_);
v_a_2849_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2846_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2846_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
lean_inc(v_a_2849_);
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
v___y_2822_ = v___x_2854_;
v_a_2823_ = v_a_2849_;
goto v___jp_2821_;
}
}
}
}
}
}
}
else
{
lean_dec(v_declNameNonRec_2803_);
lean_dec_ref(v_fixedParamPerms_2802_);
lean_dec(v_fixEq_x3f_2801_);
lean_dec(v___x_2800_);
v___y_2827_ = v___x_2829_;
goto v___jp_2826_;
}
v___jp_2809_:
{
if (v___y_2812_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_dec_ref(v___y_2810_);
v___x_2813_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__1);
v___x_2814_ = l_Lean_MessageData_ofConstName(v_declName_2798_, v___y_2812_);
v___x_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___closed__3);
v___x_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = l_Lean_Exception_toMessageData(v___y_2811_);
v___x_2819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__0___redArg(v___x_2819_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
return v___x_2820_;
}
else
{
lean_dec_ref(v___y_2811_);
lean_dec(v_declName_2798_);
return v___y_2810_;
}
}
v___jp_2821_:
{
uint8_t v___x_2824_; 
v___x_2824_ = l_Lean_Exception_isInterrupt(v_a_2823_);
if (v___x_2824_ == 0)
{
uint8_t v___x_2825_; 
lean_inc_ref(v_a_2823_);
v___x_2825_ = l_Lean_Exception_isRuntime(v_a_2823_);
v___y_2810_ = v___y_2822_;
v___y_2811_ = v_a_2823_;
v___y_2812_ = v___x_2825_;
goto v___jp_2809_;
}
else
{
v___y_2810_ = v___y_2822_;
v___y_2811_ = v_a_2823_;
v___y_2812_ = v___x_2824_;
goto v___jp_2809_;
}
}
v___jp_2826_:
{
if (lean_obj_tag(v___y_2827_) == 0)
{
lean_dec(v_declName_2798_);
return v___y_2827_;
}
else
{
lean_object* v_a_2828_; 
v_a_2828_ = lean_ctor_get(v___y_2827_, 0);
lean_inc(v_a_2828_);
v___y_2822_ = v___y_2827_;
v_a_2823_ = v_a_2828_;
goto v___jp_2821_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2798_ = stack[0].m_obj;
lean_object* v_a_2799_ = stack[1].m_obj;
lean_object* v___x_2800_ = stack[2].m_obj;
lean_object* v_fixEq_x3f_2801_ = stack[3].m_obj;
lean_object* v_fixedParamPerms_2802_ = stack[4].m_obj;
lean_object* v_declNameNonRec_2803_ = stack[5].m_obj;
lean_object* v___y_2804_ = stack[6].m_obj;
lean_object* v___y_2805_ = stack[7].m_obj;
lean_object* v___y_2806_ = stack[8].m_obj;
lean_object* v___y_2807_ = stack[9].m_obj;
lean_object* v_res_2859_;
v_res_2859_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(v_declName_2798_, v_a_2799_, v___x_2800_, v_fixEq_x3f_2801_, v_fixedParamPerms_2802_, v_declNameNonRec_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
stack->m_obj
 = v_res_2859_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed(lean_object* v_declName_2860_, lean_object* v_a_2861_, lean_object* v___x_2862_, lean_object* v_fixEq_x3f_2863_, lean_object* v_fixedParamPerms_2864_, lean_object* v_declNameNonRec_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(v_declName_2860_, v_a_2861_, v___x_2862_, v_fixEq_x3f_2863_, v_fixedParamPerms_2864_, v_declNameNonRec_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
return v_res_2871_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4(lean_object* v_levelParams_2872_, lean_object* v_declName_2873_, lean_object* v_fixEq_x3f_2874_, lean_object* v_fixedParamPerms_2875_, lean_object* v_declNameNonRec_2876_, lean_object* v_name_2877_, lean_object* v_xs_2878_, lean_object* v_body_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___x_2885_; lean_object* v_us_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2885_ = lean_box(0);
lean_inc(v_levelParams_2872_);
v_us_2886_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__2(v_levelParams_2872_, v___x_2885_);
lean_inc(v_declName_2873_);
v___x_2887_ = l_Lean_mkConst(v_declName_2873_, v_us_2886_);
v___x_2888_ = l_Lean_mkAppN(v___x_2887_, v_xs_2878_);
v___x_2889_ = l_Lean_Meta_mkEq(v___x_2888_, v_body_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2891_; lean_object* v___f_2892_; uint8_t v___x_2893_; lean_object* v___x_2894_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc_n(v_a_2890_, 2);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2891_ = lean_box(0);
v___f_2892_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed), 11, 6);
lean_closure_set(v___f_2892_, 0, v_declName_2873_);
lean_closure_set(v___f_2892_, 1, v_a_2890_);
lean_closure_set(v___f_2892_, 2, v___x_2891_);
lean_closure_set(v___f_2892_, 3, v_fixEq_x3f_2874_);
lean_closure_set(v___f_2892_, 4, v_fixedParamPerms_2875_);
lean_closure_set(v___f_2892_, 5, v_declNameNonRec_2876_);
v___x_2893_ = 0;
v___x_2894_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v___f_2892_, v___x_2893_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; uint8_t v___x_2896_; uint8_t v___x_2897_; lean_object* v___x_2898_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2896_ = 1;
v___x_2897_ = 1;
v___x_2898_ = l_Lean_Meta_mkForallFVars(v_xs_2878_, v_a_2890_, v___x_2893_, v___x_2896_, v___x_2896_, v___x_2897_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2900_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2898_, 1);
v___x_2900_ = l_Lean_Meta_letToHave(v_a_2899_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2902_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2902_ = l_Lean_Meta_mkLambdaFVars(v_xs_2878_, v_a_2895_, v___x_2893_, v___x_2896_, v___x_2893_, v___x_2896_, v___x_2897_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v_a_2908_; lean_object* v___x_2909_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2902_, 1);
lean_inc(v_name_2877_);
v___x_2904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2904_, 0, v_name_2877_);
lean_ctor_set(v___x_2904_, 1, v_levelParams_2872_);
lean_ctor_set(v___x_2904_, 2, v_a_2901_);
v___x_2905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2905_, 0, v_name_2877_);
lean_ctor_set(v___x_2905_, 1, v___x_2885_);
v___x_2906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v_a_2903_);
lean_ctor_set(v___x_2906_, 2, v___x_2905_);
v___x_2907_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__4___redArg(v___x_2906_, v___y_2883_);
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref(v___x_2907_);
v___x_2909_ = l_Lean_addDecl(v_a_2908_, v___x_2893_, v___y_2882_, v___y_2883_);
return v___x_2909_;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v_a_2901_);
lean_dec(v_name_2877_);
lean_dec(v_levelParams_2872_);
v_a_2910_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2902_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2902_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_a_2895_);
lean_dec(v_name_2877_);
lean_dec(v_levelParams_2872_);
v_a_2918_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2900_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2900_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_a_2895_);
lean_dec(v_name_2877_);
lean_dec(v_levelParams_2872_);
v_a_2926_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2898_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2898_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v_a_2890_);
lean_dec(v_name_2877_);
lean_dec(v_levelParams_2872_);
v_a_2934_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2894_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2894_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v_name_2877_);
lean_dec(v_declNameNonRec_2876_);
lean_dec_ref(v_fixedParamPerms_2875_);
lean_dec(v_fixEq_x3f_2874_);
lean_dec(v_declName_2873_);
lean_dec(v_levelParams_2872_);
v_a_2942_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2889_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2889_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_levelParams_2872_ = stack[0].m_obj;
lean_object* v_declName_2873_ = stack[1].m_obj;
lean_object* v_fixEq_x3f_2874_ = stack[2].m_obj;
lean_object* v_fixedParamPerms_2875_ = stack[3].m_obj;
lean_object* v_declNameNonRec_2876_ = stack[4].m_obj;
lean_object* v_name_2877_ = stack[5].m_obj;
lean_object* v_xs_2878_ = stack[6].m_obj;
lean_object* v_body_2879_ = stack[7].m_obj;
lean_object* v___y_2880_ = stack[8].m_obj;
lean_object* v___y_2881_ = stack[9].m_obj;
lean_object* v___y_2882_ = stack[10].m_obj;
lean_object* v___y_2883_ = stack[11].m_obj;
lean_object* v_res_2950_;
v_res_2950_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4(v_levelParams_2872_, v_declName_2873_, v_fixEq_x3f_2874_, v_fixedParamPerms_2875_, v_declNameNonRec_2876_, v_name_2877_, v_xs_2878_, v_body_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
stack->m_obj
 = v_res_2950_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4___boxed(lean_object* v_levelParams_2951_, lean_object* v_declName_2952_, lean_object* v_fixEq_x3f_2953_, lean_object* v_fixedParamPerms_2954_, lean_object* v_declNameNonRec_2955_, lean_object* v_name_2956_, lean_object* v_xs_2957_, lean_object* v_body_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4(v_levelParams_2951_, v_declName_2952_, v_fixEq_x3f_2953_, v_fixedParamPerms_2954_, v_declNameNonRec_2955_, v_name_2956_, v_xs_2957_, v_body_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v_xs_2957_);
return v_res_2964_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object* v_declName_2965_, lean_object* v_info_2966_, lean_object* v_name_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v_toCold_2973_; lean_object* v_levelParams_2974_; lean_object* v_value_2975_; lean_object* v_declNameNonRec_2976_; lean_object* v_fixedParamPerms_2977_; lean_object* v_fixEq_x3f_2978_; lean_object* v_currRecDepth_2979_; lean_object* v_ref_2980_; uint8_t v_suppressElabErrors_2981_; uint8_t v_isRecordingDeps_2982_; lean_object* v_fileName_2983_; lean_object* v_fileMap_2984_; lean_object* v_options_2985_; lean_object* v_currNamespace_2986_; lean_object* v_openDecls_2987_; lean_object* v_initHeartbeats_2988_; lean_object* v_maxHeartbeats_2989_; lean_object* v_quotContext_2990_; lean_object* v_currMacroScope_2991_; lean_object* v_cancelTk_x3f_2992_; lean_object* v_inheritedTraceOptions_2993_; lean_object* v___f_2994_; uint8_t v___x_2995_; uint16_t v___y_2997_; lean_object* v___y_2998_; lean_object* v_fileName_2999_; lean_object* v_fileMap_3000_; lean_object* v_currNamespace_3001_; lean_object* v_openDecls_3002_; lean_object* v_initHeartbeats_3003_; lean_object* v_maxHeartbeats_3004_; lean_object* v_quotContext_3005_; lean_object* v_currMacroScope_3006_; lean_object* v_cancelTk_x3f_3007_; lean_object* v_inheritedTraceOptions_3008_; lean_object* v_currRecDepth_3009_; lean_object* v_ref_3010_; uint8_t v_suppressElabErrors_3011_; uint8_t v_isRecordingDeps_3012_; lean_object* v___y_3013_; uint16_t v___y_3020_; uint8_t v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3045_; 
v_toCold_2973_ = lean_ctor_get(v_a_2970_, 0);
v_levelParams_2974_ = lean_ctor_get(v_info_2966_, 1);
lean_inc(v_levelParams_2974_);
v_value_2975_ = lean_ctor_get(v_info_2966_, 3);
lean_inc_ref(v_value_2975_);
v_declNameNonRec_2976_ = lean_ctor_get(v_info_2966_, 5);
lean_inc(v_declNameNonRec_2976_);
v_fixedParamPerms_2977_ = lean_ctor_get(v_info_2966_, 6);
lean_inc_ref(v_fixedParamPerms_2977_);
v_fixEq_x3f_2978_ = lean_ctor_get(v_info_2966_, 8);
lean_inc(v_fixEq_x3f_2978_);
lean_dec_ref(v_info_2966_);
v_currRecDepth_2979_ = lean_ctor_get(v_a_2970_, 1);
v_ref_2980_ = lean_ctor_get(v_a_2970_, 2);
v_suppressElabErrors_2981_ = lean_ctor_get_uint8(v_a_2970_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2982_ = lean_ctor_get_uint8(v_a_2970_, sizeof(void*)*3 + 3);
v_fileName_2983_ = lean_ctor_get(v_toCold_2973_, 0);
v_fileMap_2984_ = lean_ctor_get(v_toCold_2973_, 1);
v_options_2985_ = lean_ctor_get(v_toCold_2973_, 2);
v_currNamespace_2986_ = lean_ctor_get(v_toCold_2973_, 4);
v_openDecls_2987_ = lean_ctor_get(v_toCold_2973_, 5);
v_initHeartbeats_2988_ = lean_ctor_get(v_toCold_2973_, 6);
v_maxHeartbeats_2989_ = lean_ctor_get(v_toCold_2973_, 7);
v_quotContext_2990_ = lean_ctor_get(v_toCold_2973_, 8);
v_currMacroScope_2991_ = lean_ctor_get(v_toCold_2973_, 9);
v_cancelTk_x3f_2992_ = lean_ctor_get(v_toCold_2973_, 10);
v_inheritedTraceOptions_2993_ = lean_ctor_get(v_toCold_2973_, 11);
v___f_2994_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__4___boxed), 13, 6);
lean_closure_set(v___f_2994_, 0, v_levelParams_2974_);
lean_closure_set(v___f_2994_, 1, v_declName_2965_);
lean_closure_set(v___f_2994_, 2, v_fixEq_x3f_2978_);
lean_closure_set(v___f_2994_, 3, v_fixedParamPerms_2977_);
lean_closure_set(v___f_2994_, 4, v_declNameNonRec_2976_);
lean_closure_set(v___f_2994_, 5, v_name_2967_);
v___x_2995_ = 0;
if (v_isRecordingDeps_2982_ == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_2985_);
v___x_3056_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_options_2985_, v___x_3055_, v_isRecordingDeps_2982_);
v___y_3045_ = v___x_3056_;
goto v___jp_3044_;
}
else
{
lean_object* v___x_3057_; 
lean_inc_ref(v_options_2985_);
v___x_3057_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2985_);
v___y_3045_ = v___x_3057_;
goto v___jp_3044_;
}
v___jp_2996_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3014_ = l_Lean_maxRecDepth;
v___x_3015_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___y_2998_, v___x_3014_);
v___x_3016_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3016_, 0, v_fileName_2999_);
lean_ctor_set(v___x_3016_, 1, v_fileMap_3000_);
lean_ctor_set(v___x_3016_, 2, v___y_2998_);
lean_ctor_set(v___x_3016_, 3, v___x_3015_);
lean_ctor_set(v___x_3016_, 4, v_currNamespace_3001_);
lean_ctor_set(v___x_3016_, 5, v_openDecls_3002_);
lean_ctor_set(v___x_3016_, 6, v_initHeartbeats_3003_);
lean_ctor_set(v___x_3016_, 7, v_maxHeartbeats_3004_);
lean_ctor_set(v___x_3016_, 8, v_quotContext_3005_);
lean_ctor_set(v___x_3016_, 9, v_currMacroScope_3006_);
lean_ctor_set(v___x_3016_, 10, v_cancelTk_x3f_3007_);
lean_ctor_set(v___x_3016_, 11, v_inheritedTraceOptions_3008_);
lean_inc(v_ref_3010_);
lean_inc(v_currRecDepth_3009_);
v___x_3017_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v_currRecDepth_3009_);
lean_ctor_set(v___x_3017_, 2, v_ref_3010_);
lean_ctor_set_uint16(v___x_3017_, sizeof(void*)*3, v___y_2997_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*3 + 2, v_suppressElabErrors_3011_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*3 + 3, v_isRecordingDeps_3012_);
v___x_3018_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__3___redArg(v_value_2975_, v___f_2994_, v___x_2995_, v_a_2968_, v_a_2969_, v___x_3017_, v___y_3013_);
lean_dec_ref_known(v___x_3017_, 3);
return v___x_3018_;
}
v___jp_3019_:
{
lean_object* v___x_3023_; lean_object* v_env_3024_; lean_object* v_nextMacroScope_3025_; lean_object* v_ngen_3026_; lean_object* v_auxDeclNGen_3027_; lean_object* v_traceState_3028_; lean_object* v_recordedDeps_3029_; lean_object* v_messages_3030_; lean_object* v_infoState_3031_; lean_object* v_snapshotTasks_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3042_; 
v___x_3023_ = lean_st_ref_take(v_a_2971_);
v_env_3024_ = lean_ctor_get(v___x_3023_, 0);
v_nextMacroScope_3025_ = lean_ctor_get(v___x_3023_, 1);
v_ngen_3026_ = lean_ctor_get(v___x_3023_, 2);
v_auxDeclNGen_3027_ = lean_ctor_get(v___x_3023_, 3);
v_traceState_3028_ = lean_ctor_get(v___x_3023_, 4);
v_recordedDeps_3029_ = lean_ctor_get(v___x_3023_, 6);
v_messages_3030_ = lean_ctor_get(v___x_3023_, 7);
v_infoState_3031_ = lean_ctor_get(v___x_3023_, 8);
v_snapshotTasks_3032_ = lean_ctor_get(v___x_3023_, 9);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3042_ == 0)
{
lean_object* v_unused_3043_; 
v_unused_3043_ = lean_ctor_get(v___x_3023_, 5);
lean_dec(v_unused_3043_);
v___x_3034_ = v___x_3023_;
v_isShared_3035_ = v_isSharedCheck_3042_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_snapshotTasks_3032_);
lean_inc(v_infoState_3031_);
lean_inc(v_messages_3030_);
lean_inc(v_recordedDeps_3029_);
lean_inc(v_traceState_3028_);
lean_inc(v_auxDeclNGen_3027_);
lean_inc(v_ngen_3026_);
lean_inc(v_nextMacroScope_3025_);
lean_inc(v_env_3024_);
lean_dec(v___x_3023_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3042_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3036_ = l_Lean_Kernel_enableDiag(v_env_3024_, v___y_3021_);
v___x_3037_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkFixEq_spec__5___redArg___closed__2);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 5, v___x_3037_);
lean_ctor_set(v___x_3034_, 0, v___x_3036_);
v___x_3039_ = v___x_3034_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_nextMacroScope_3025_);
lean_ctor_set(v_reuseFailAlloc_3041_, 2, v_ngen_3026_);
lean_ctor_set(v_reuseFailAlloc_3041_, 3, v_auxDeclNGen_3027_);
lean_ctor_set(v_reuseFailAlloc_3041_, 4, v_traceState_3028_);
lean_ctor_set(v_reuseFailAlloc_3041_, 5, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3041_, 6, v_recordedDeps_3029_);
lean_ctor_set(v_reuseFailAlloc_3041_, 7, v_messages_3030_);
lean_ctor_set(v_reuseFailAlloc_3041_, 8, v_infoState_3031_);
lean_ctor_set(v_reuseFailAlloc_3041_, 9, v_snapshotTasks_3032_);
v___x_3039_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_st_ref_put(v_a_2971_, v___x_3039_);
lean_inc_ref(v_inheritedTraceOptions_2993_);
lean_inc(v_cancelTk_x3f_2992_);
lean_inc(v_currMacroScope_2991_);
lean_inc(v_quotContext_2990_);
lean_inc(v_maxHeartbeats_2989_);
lean_inc(v_initHeartbeats_2988_);
lean_inc(v_openDecls_2987_);
lean_inc(v_currNamespace_2986_);
lean_inc_ref(v_fileMap_2984_);
lean_inc_ref(v_fileName_2983_);
v___y_2997_ = v___y_3020_;
v___y_2998_ = v___y_3022_;
v_fileName_2999_ = v_fileName_2983_;
v_fileMap_3000_ = v_fileMap_2984_;
v_currNamespace_3001_ = v_currNamespace_2986_;
v_openDecls_3002_ = v_openDecls_2987_;
v_initHeartbeats_3003_ = v_initHeartbeats_2988_;
v_maxHeartbeats_3004_ = v_maxHeartbeats_2989_;
v_quotContext_3005_ = v_quotContext_2990_;
v_currMacroScope_3006_ = v_currMacroScope_2991_;
v_cancelTk_x3f_3007_ = v_cancelTk_x3f_2992_;
v_inheritedTraceOptions_3008_ = v_inheritedTraceOptions_2993_;
v_currRecDepth_3009_ = v_currRecDepth_2979_;
v_ref_3010_ = v_ref_2980_;
v_suppressElabErrors_3011_ = v_suppressElabErrors_2981_;
v_isRecordingDeps_3012_ = v_isRecordingDeps_2982_;
v___y_3013_ = v_a_2971_;
goto v___jp_2996_;
}
}
}
v___jp_3044_:
{
uint16_t v___x_3046_; lean_object* v___x_3047_; lean_object* v_env_3048_; uint8_t v___x_3049_; uint16_t v___x_3050_; uint16_t v___x_3051_; uint16_t v___x_3052_; uint8_t v___x_3053_; 
v___x_3046_ = l_Lean_OptionFlags_ofOptions(v___y_3045_);
v___x_3047_ = lean_st_ref_get(v_a_2971_);
v_env_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc_ref(v_env_3048_);
lean_dec(v___x_3047_);
v___x_3049_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3048_);
lean_dec_ref(v_env_3048_);
v___x_3050_ = 512;
v___x_3051_ = lean_uint16_land(v___x_3046_, v___x_3050_);
v___x_3052_ = 0;
v___x_3053_ = lean_uint16_dec_eq(v___x_3051_, v___x_3052_);
if (v___x_3053_ == 0)
{
if (v___x_3049_ == 0)
{
uint8_t v___x_3054_; 
v___x_3054_ = 1;
v___y_3020_ = v___x_3046_;
v___y_3021_ = v___x_3054_;
v___y_3022_ = v___y_3045_;
goto v___jp_3019_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2993_);
lean_inc(v_cancelTk_x3f_2992_);
lean_inc(v_currMacroScope_2991_);
lean_inc(v_quotContext_2990_);
lean_inc(v_maxHeartbeats_2989_);
lean_inc(v_initHeartbeats_2988_);
lean_inc(v_openDecls_2987_);
lean_inc(v_currNamespace_2986_);
lean_inc_ref(v_fileMap_2984_);
lean_inc_ref(v_fileName_2983_);
v___y_2997_ = v___x_3046_;
v___y_2998_ = v___y_3045_;
v_fileName_2999_ = v_fileName_2983_;
v_fileMap_3000_ = v_fileMap_2984_;
v_currNamespace_3001_ = v_currNamespace_2986_;
v_openDecls_3002_ = v_openDecls_2987_;
v_initHeartbeats_3003_ = v_initHeartbeats_2988_;
v_maxHeartbeats_3004_ = v_maxHeartbeats_2989_;
v_quotContext_3005_ = v_quotContext_2990_;
v_currMacroScope_3006_ = v_currMacroScope_2991_;
v_cancelTk_x3f_3007_ = v_cancelTk_x3f_2992_;
v_inheritedTraceOptions_3008_ = v_inheritedTraceOptions_2993_;
v_currRecDepth_3009_ = v_currRecDepth_2979_;
v_ref_3010_ = v_ref_2980_;
v_suppressElabErrors_3011_ = v_suppressElabErrors_2981_;
v_isRecordingDeps_3012_ = v_isRecordingDeps_2982_;
v___y_3013_ = v_a_2971_;
goto v___jp_2996_;
}
}
else
{
if (v___x_3049_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2993_);
lean_inc(v_cancelTk_x3f_2992_);
lean_inc(v_currMacroScope_2991_);
lean_inc(v_quotContext_2990_);
lean_inc(v_maxHeartbeats_2989_);
lean_inc(v_initHeartbeats_2988_);
lean_inc(v_openDecls_2987_);
lean_inc(v_currNamespace_2986_);
lean_inc_ref(v_fileMap_2984_);
lean_inc_ref(v_fileName_2983_);
v___y_2997_ = v___x_3046_;
v___y_2998_ = v___y_3045_;
v_fileName_2999_ = v_fileName_2983_;
v_fileMap_3000_ = v_fileMap_2984_;
v_currNamespace_3001_ = v_currNamespace_2986_;
v_openDecls_3002_ = v_openDecls_2987_;
v_initHeartbeats_3003_ = v_initHeartbeats_2988_;
v_maxHeartbeats_3004_ = v_maxHeartbeats_2989_;
v_quotContext_3005_ = v_quotContext_2990_;
v_currMacroScope_3006_ = v_currMacroScope_2991_;
v_cancelTk_x3f_3007_ = v_cancelTk_x3f_2992_;
v_inheritedTraceOptions_3008_ = v_inheritedTraceOptions_2993_;
v_currRecDepth_3009_ = v_currRecDepth_2979_;
v_ref_3010_ = v_ref_2980_;
v_suppressElabErrors_3011_ = v_suppressElabErrors_2981_;
v_isRecordingDeps_3012_ = v_isRecordingDeps_2982_;
v___y_3013_ = v_a_2971_;
goto v___jp_2996_;
}
else
{
v___y_3020_ = v___x_3046_;
v___y_3021_ = v___x_2995_;
v___y_3022_ = v___y_3045_;
goto v___jp_3019_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2965_ = stack[0].m_obj;
lean_object* v_info_2966_ = stack[1].m_obj;
lean_object* v_name_2967_ = stack[2].m_obj;
lean_object* v_a_2968_ = stack[3].m_obj;
lean_object* v_a_2969_ = stack[4].m_obj;
lean_object* v_a_2970_ = stack[5].m_obj;
lean_object* v_a_2971_ = stack[6].m_obj;
lean_object* v_res_3058_;
v_res_3058_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_2965_, v_info_2966_, v_name_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
stack->m_obj
 = v_res_3058_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3059_, lean_object* v_info_3060_, lean_object* v_name_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_3059_, v_info_3060_, v_name_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
return v_res_3067_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* v_declName_3068_, lean_object* v_info_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v___x_3075_; lean_object* v_env_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3075_ = lean_st_ref_get(v_a_3073_);
v_env_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc_ref(v_env_3076_);
lean_dec(v___x_3075_);
v___x_3077_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc_n(v_declName_3068_, 2);
v___x_3078_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3076_, v_declName_3068_, v___x_3077_);
lean_inc_n(v___x_3078_, 2);
v___x_3079_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3079_, 0, v_declName_3068_);
lean_closure_set(v___x_3079_, 1, v_info_3069_);
lean_closure_set(v___x_3079_, 2, v___x_3078_);
v___x_3080_ = l_Lean_Meta_realizeConst(v_declName_3068_, v___x_3078_, v___x_3079_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v___x_3080_, 0);
lean_dec(v_unused_3088_);
v___x_3082_ = v___x_3080_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_dec(v___x_3080_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v___x_3078_);
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3078_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v___x_3078_);
v_a_3089_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3080_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3080_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3068_ = stack[0].m_obj;
lean_object* v_info_3069_ = stack[1].m_obj;
lean_object* v_a_3070_ = stack[2].m_obj;
lean_object* v_a_3071_ = stack[3].m_obj;
lean_object* v_a_3072_ = stack[4].m_obj;
lean_object* v_a_3073_ = stack[5].m_obj;
lean_object* v_res_3097_;
v_res_3097_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_3068_, v_info_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
stack->m_obj
 = v_res_3097_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(lean_object* v_declName_3098_, lean_object* v_info_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_3098_, v_info_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
return v_res_3105_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* v_declName_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v_env_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v_env_3118_; uint8_t v___x_3119_; uint8_t v___x_3120_; 
v___x_3112_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
v___x_3113_ = lean_st_ref_get(v_a_3110_);
v_env_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc_ref(v_env_3114_);
lean_dec(v___x_3113_);
v___x_3115_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3106_);
v___x_3116_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3114_, v_declName_3106_, v___x_3115_);
v___x_3117_ = lean_st_ref_get(v_a_3110_);
v_env_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc_ref_n(v_env_3118_, 2);
lean_dec(v___x_3117_);
v___x_3119_ = 1;
lean_inc(v___x_3116_);
v___x_3120_ = l_Lean_Environment_contains(v_env_3118_, v___x_3116_, v___x_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; lean_object* v_toEnvExtension_3122_; lean_object* v_asyncMode_3123_; uint8_t v___x_3124_; lean_object* v___x_3125_; 
lean_dec(v___x_3116_);
v___x_3121_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
v_toEnvExtension_3122_ = lean_ctor_get(v___x_3121_, 0);
v_asyncMode_3123_ = lean_ctor_get(v_toEnvExtension_3122_, 2);
v___x_3124_ = 0;
lean_inc(v_declName_3106_);
v___x_3125_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3112_, v___x_3121_, v_env_3118_, v_declName_3106_, v_asyncMode_3123_, v___x_3124_);
if (lean_obj_tag(v___x_3125_) == 1)
{
lean_object* v_val_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3150_; 
v_val_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3150_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_val_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3150_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; 
v___x_3130_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_3106_, v_val_3126_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3141_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3141_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3141_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v_a_3131_);
v___x_3136_ = v___x_3128_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3136_);
v___x_3138_ = v___x_3133_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_del_object(v___x_3128_);
v_a_3142_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3130_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3130_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_dec(v___x_3125_);
lean_dec(v_declName_3106_);
v___x_3151_ = lean_box(0);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
return v___x_3152_;
}
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec_ref(v_env_3118_);
lean_dec(v_declName_3106_);
v___x_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3116_);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3106_ = stack[0].m_obj;
lean_object* v_a_3107_ = stack[1].m_obj;
lean_object* v_a_3108_ = stack[2].m_obj;
lean_object* v_a_3109_ = stack[3].m_obj;
lean_object* v_a_3110_ = stack[4].m_obj;
lean_object* v_res_3155_;
v_res_3155_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_3106_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_);
stack->m_obj
 = v_res_3155_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(lean_object* v_declName_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
return v_res_3162_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_));
v___x_3166_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3167_;
v_res_3167_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3167_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(lean_object* v_a_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
return v_res_3169_;
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
