// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Unfold
// Imports: public import Lean.Elab.PreDefinition.Basic public import Lean.Meta.Tactic.Simp.Types import Lean.Elab.PreDefinition.EqnsUtils import Lean.Meta.Tactic.Split import Lean.Meta.Tactic.Simp.Main import Lean.Meta.Tactic.Delta import Lean.Meta.Tactic.Refl import Init.Simproc
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MVarId_refl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_instInhabitedSimpM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_altNumParams(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_Split_splitMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Elab.PreDefinition.WF.Unfold"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "_private.Lean.Elab.PreDefinition.WF.Unfold.0.Lean.Elab.WF.rwFixEq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rwFixEq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__7_value),LEAN_SCALAR_PTR_LITERAL(216, 129, 81, 44, 19, 93, 163, 124)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "expected saturated fixed-point application in "};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "WellFounded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__12 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__12_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__13 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(153, 177, 70, 214, 156, 62, 227, 219)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(209, 126, 194, 128, 117, 36, 224, 78)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__13_value),LEAN_SCALAR_PTR_LITERAL(196, 0, 160, 225, 119, 146, 123, 62)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(153, 177, 70, 214, 156, 62, 227, 219)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__13_value),LEAN_SCALAR_PTR_LITERAL(172, 133, 211, 204, 28, 206, 53, 233)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fix_eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(153, 177, 70, 214, 156, 62, 227, 219)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 168, 55, 181, 1, 128, 191)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(153, 177, 70, 214, 156, 62, 227, 219)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(209, 126, 194, 128, 117, 36, 224, 78)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16_value),LEAN_SCALAR_PTR_LITERAL(173, 254, 168, 75, 13, 175, 61, 73)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "rwFixEq: cannot delta-reduce "};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "_private.Lean.Elab.PreDefinition.WF.Unfold.0.Lean.Elab.WF.splitMatchOrCasesOn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "assertion violation: discr.isFVar\n    "};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2;
static const lean_array_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "_private.Lean.Elab.PreDefinition.WF.Unfold.0.Lean.Elab.WF.mkMatchArgPusher"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: altBodyType.isForall\n          "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "unexpected matcher application for "};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = ", motive is not a proposition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 17, 233, 98, 131, 1, 46, 199)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "β"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 67, 89, 131, 111, 186, 232, 248)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 178, 247, 241, 102, 42, 87, 174)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 108, 188, 174, 117, 112, 110, 72)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "α"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__4_value),LEAN_SCALAR_PTR_LITERAL(102, 24, 27, 80, 217, 159, 184, 13)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_arg_pusher"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(67, 93, 110, 193, 138, 112, 221, 105)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Cannot create match arg pusher for "};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instInhabitedSimpM___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Match.MatcherApp.Basic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.matchMatcherApp\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1;
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "matcherPushArg: expected equality:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "_private.Lean.Elab.PreDefinition.WF.Unfold.0.Lean.Elab.WF.matcherPushArg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "assertion violation: fExprType.isForall\n  "};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WF"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(231, 60, 146, 67, 170, 35, 9, 50)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Unfold"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(107, 60, 73, 44, 205, 78, 214, 55)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(214, 186, 22, 181, 135, 89, 255, 35)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(127, 174, 101, 137, 114, 200, 12, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(33, 93, 149, 86, 9, 247, 3, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(177, 93, 103, 123, 232, 207, 165, 166)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "matcherPushArg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(225, 113, 246, 21, 195, 5, 15, 220)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
static const lean_array_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "failed to finish proof for equational theorem for `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0_value;
static const lean_array_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5;
static const lean_string_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "mkUnfoldEq defined "};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mkUnfoldEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Cannot derive unfold equation "};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___closed__0_value;
static lean_once_cell_t l_Lean_Elab_WF_mkUnfoldEq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "mkBinaryUnfoldEq defined "};
static const lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1;
static const lean_ctor_object l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Failed to apply `"};
static const lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4;
static const lean_string_object l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` to `"};
static const lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Cannot derive "};
static const lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0_value;
static lean_once_cell_t l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1;
static const lean_string_object l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " from "};
static const lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__2 = (const lean_object*)&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__2_value;
static lean_once_cell_t l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eqns"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 14, 28, 10, 226, 95, 51, 62)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 26, 119, 163, 229, 120, 15, 205)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(57, 120, 226, 204, 0, 34, 252, 196)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(156, 125, 245, 250, 214, 234, 210, 86)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(150, 57, 156, 205, 162, 224, 99, 74)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(201, 193, 43, 137, 57, 227, 113, 35)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(41, 253, 77, 165, 5, 71, 84, 139)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(133, 113, 198, 34, 182, 132, 253, 5)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)(((size_t)(417821031) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(25, 31, 165, 159, 161, 54, 57, 238)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 149, 109, 35, 113, 129, 96, 22)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 3, 149, 243, 10, 45, 240, 255)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(247, 102, 107, 61, 251, 143, 49, 202)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___f_8_; lean_object* v___x_3528__overap_9_; lean_object* v___x_10_; 
v___f_8_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_3528__overap_9_ = lean_panic_fn_borrowed(v___f_8_, v_msg_2_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_10_ = lean_apply_5(v___x_3528__overap_9_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___boxed(lean_object* v_msg_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(v_msg_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
lean_dec(v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0(lean_object* v_k_18_, lean_object* v_b_19_, lean_object* v_c_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_26_; 
lean_inc(v___y_24_);
lean_inc_ref(v___y_23_);
lean_inc(v___y_22_);
lean_inc_ref(v___y_21_);
v___x_26_ = lean_apply_7(v_k_18_, v_b_19_, v_c_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, lean_box(0));
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed(lean_object* v_k_27_, lean_object* v_b_28_, lean_object* v_c_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0(v_k_27_, v_b_28_, v_c_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(lean_object* v_type_36_, lean_object* v_maxFVars_x3f_37_, lean_object* v_k_38_, uint8_t v_cleanupAnnotations_39_, uint8_t v_whnfType_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v___f_46_; lean_object* v___x_47_; 
v___f_46_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_46_, 0, v_k_38_);
v___x_47_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_36_, v_maxFVars_x3f_37_, v___f_46_, v_cleanupAnnotations_39_, v_whnfType_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_47_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
else
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
v_a_56_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v___x_47_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_47_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___boxed(lean_object* v_type_64_, lean_object* v_maxFVars_x3f_65_, lean_object* v_k_66_, lean_object* v_cleanupAnnotations_67_, lean_object* v_whnfType_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_74_; uint8_t v_whnfType_boxed_75_; lean_object* v_res_76_; 
v_cleanupAnnotations_boxed_74_ = lean_unbox(v_cleanupAnnotations_67_);
v_whnfType_boxed_75_ = lean_unbox(v_whnfType_68_);
v_res_76_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_64_, v_maxFVars_x3f_65_, v_k_66_, v_cleanupAnnotations_boxed_74_, v_whnfType_boxed_75_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1(lean_object* v_00_u03b1_77_, lean_object* v_type_78_, lean_object* v_maxFVars_x3f_79_, lean_object* v_k_80_, uint8_t v_cleanupAnnotations_81_, uint8_t v_whnfType_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_78_, v_maxFVars_x3f_79_, v_k_80_, v_cleanupAnnotations_81_, v_whnfType_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___boxed(lean_object* v_00_u03b1_89_, lean_object* v_type_90_, lean_object* v_maxFVars_x3f_91_, lean_object* v_k_92_, lean_object* v_cleanupAnnotations_93_, lean_object* v_whnfType_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_100_; uint8_t v_whnfType_boxed_101_; lean_object* v_res_102_; 
v_cleanupAnnotations_boxed_100_ = lean_unbox(v_cleanupAnnotations_93_);
v_whnfType_boxed_101_ = lean_unbox(v_whnfType_94_);
v_res_102_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1(v_00_u03b1_89_, v_type_90_, v_maxFVars_x3f_91_, v_k_92_, v_cleanupAnnotations_boxed_100_, v_whnfType_boxed_101_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(lean_object* v_mvarId_103_, lean_object* v_x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_103_, v_x_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
v_a_119_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_110_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_110_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg___boxed(lean_object* v_mvarId_127_, lean_object* v_x_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(v_mvarId_127_, v_x_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4(lean_object* v_00_u03b1_135_, lean_object* v_mvarId_136_, lean_object* v_x_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(v_mvarId_136_, v_x_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___boxed(lean_object* v_00_u03b1_144_, lean_object* v_mvarId_145_, lean_object* v_x_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4(v_00_u03b1_144_, v_mvarId_145_, v_x_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_152_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(uint8_t v___x_153_, lean_object* v_x_154_){
_start:
{
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed(lean_object* v___x_155_, lean_object* v_x_156_){
_start:
{
uint8_t v___x_5940__boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v___x_5940__boxed_157_ = lean_unbox(v___x_155_);
v_res_158_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(v___x_5940__boxed_157_, v_x_156_);
lean_dec(v_x_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(lean_object* v___x_160_, lean_object* v___x_161_, uint8_t v___x_162_, uint8_t v___x_163_, lean_object* v_ys_164_, lean_object* v_x_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; lean_object* v___x_176_; 
v___x_171_ = l_Lean_Expr_appFn_x21(v___x_160_);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_array_get_borrowed(v___x_161_, v_ys_164_, v___x_172_);
lean_inc(v___x_173_);
v___x_174_ = l_Lean_Expr_app___override(v___x_171_, v___x_173_);
v___x_175_ = 1;
v___x_176_ = l_Lean_Meta_mkLambdaFVars(v_ys_164_, v___x_174_, v___x_162_, v___x_163_, v___x_162_, v___x_163_, v___x_175_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed(lean_object* v___x_177_, lean_object* v___x_178_, lean_object* v___x_179_, lean_object* v___x_180_, lean_object* v_ys_181_, lean_object* v_x_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
uint8_t v___x_5948__boxed_188_; uint8_t v___x_5949__boxed_189_; lean_object* v_res_190_; 
v___x_5948__boxed_188_ = lean_unbox(v___x_179_);
v___x_5949__boxed_189_ = lean_unbox(v___x_180_);
v_res_190_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(v___x_177_, v___x_178_, v___x_5948__boxed_188_, v___x_5949__boxed_189_, v_ys_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec_ref(v_x_182_);
lean_dec_ref(v_ys_181_);
lean_dec_ref(v___x_178_);
lean_dec_ref(v___x_177_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(lean_object* v_msgData_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; lean_object* v_env_198_; lean_object* v___x_199_; lean_object* v_toCold_200_; lean_object* v_mctx_201_; lean_object* v_lctx_202_; lean_object* v_options_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_197_ = lean_st_ref_get(v___y_195_);
v_env_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc_ref(v_env_198_);
lean_dec(v___x_197_);
v___x_199_ = lean_st_ref_get(v___y_193_);
v_toCold_200_ = lean_ctor_get(v___y_194_, 0);
v_mctx_201_ = lean_ctor_get(v___x_199_, 0);
lean_inc_ref(v_mctx_201_);
lean_dec(v___x_199_);
v_lctx_202_ = lean_ctor_get(v___y_192_, 2);
v_options_203_ = lean_ctor_get(v_toCold_200_, 2);
lean_inc_ref(v_options_203_);
lean_inc_ref(v_lctx_202_);
v___x_204_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_204_, 0, v_env_198_);
lean_ctor_set(v___x_204_, 1, v_mctx_201_);
lean_ctor_set(v___x_204_, 2, v_lctx_202_);
lean_ctor_set(v___x_204_, 3, v_options_203_);
v___x_205_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v_msgData_191_);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4___boxed(lean_object* v_msgData_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msgData_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(lean_object* v_msg_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_ref_220_; lean_object* v___x_221_; lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_230_; 
v_ref_220_ = lean_ctor_get(v___y_217_, 2);
v___x_221_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
v_a_222_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_230_ == 0)
{
v___x_224_ = v___x_221_;
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
lean_inc(v_ref_220_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_ref_220_);
lean_ctor_set(v___x_226_, 1, v_a_222_);
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 1);
lean_ctor_set(v___x_224_, 0, v___x_226_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg___boxed(lean_object* v_msg_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
lean_object* v_ks_242_; lean_object* v_vs_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_267_; 
v_ks_242_ = lean_ctor_get(v_x_238_, 0);
v_vs_243_ = lean_ctor_get(v_x_238_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_238_);
if (v_isSharedCheck_267_ == 0)
{
v___x_245_ = v_x_238_;
v_isShared_246_ = v_isSharedCheck_267_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_vs_243_);
lean_inc(v_ks_242_);
lean_dec(v_x_238_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_267_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = lean_array_get_size(v_ks_242_);
v___x_248_ = lean_nat_dec_lt(v_x_239_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
lean_dec(v_x_239_);
v___x_249_ = lean_array_push(v_ks_242_, v_x_240_);
v___x_250_ = lean_array_push(v_vs_243_, v_x_241_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v___x_250_);
lean_ctor_set(v___x_245_, 0, v___x_249_);
v___x_252_ = v___x_245_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
else
{
lean_object* v_k_x27_254_; uint8_t v___x_255_; 
v_k_x27_254_ = lean_array_fget_borrowed(v_ks_242_, v_x_239_);
v___x_255_ = l_Lean_instBEqMVarId_beq(v_x_240_, v_k_x27_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_257_; 
if (v_isShared_246_ == 0)
{
v___x_257_ = v___x_245_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_ks_242_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_vs_243_);
v___x_257_ = v_reuseFailAlloc_261_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_add(v_x_239_, v___x_258_);
lean_dec(v_x_239_);
v_x_238_ = v___x_257_;
v_x_239_ = v___x_259_;
goto _start;
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_262_ = lean_array_fset(v_ks_242_, v_x_239_, v_x_240_);
v___x_263_ = lean_array_fset(v_vs_243_, v_x_239_, v_x_241_);
lean_dec(v_x_239_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v___x_263_);
lean_ctor_set(v___x_245_, 0, v___x_262_);
v___x_265_ = v___x_245_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_n_268_, lean_object* v_k_269_, lean_object* v_v_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_268_, v___x_271_, v_k_269_, v_v_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(lean_object* v_x_274_, size_t v_x_275_, size_t v_x_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v_es_279_; size_t v___x_280_; size_t v___x_281_; lean_object* v_j_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_es_279_ = lean_ctor_get(v_x_274_, 0);
v___x_280_ = ((size_t)31ULL);
v___x_281_ = lean_usize_land(v_x_275_, v___x_280_);
v_j_282_ = lean_usize_to_nat(v___x_281_);
v___x_283_ = lean_array_get_size(v_es_279_);
v___x_284_ = lean_nat_dec_lt(v_j_282_, v___x_283_);
if (v___x_284_ == 0)
{
lean_dec(v_j_282_);
lean_dec(v_x_278_);
lean_dec(v_x_277_);
return v_x_274_;
}
else
{
lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_323_; 
lean_inc_ref(v_es_279_);
v_isSharedCheck_323_ = !lean_is_exclusive(v_x_274_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; 
v_unused_324_ = lean_ctor_get(v_x_274_, 0);
lean_dec(v_unused_324_);
v___x_286_ = v_x_274_;
v_isShared_287_ = v_isSharedCheck_323_;
goto v_resetjp_285_;
}
else
{
lean_dec(v_x_274_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_323_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_v_288_; lean_object* v___x_289_; lean_object* v_xs_x27_290_; lean_object* v___y_292_; 
v_v_288_ = lean_array_fget(v_es_279_, v_j_282_);
v___x_289_ = lean_box(0);
v_xs_x27_290_ = lean_array_fset(v_es_279_, v_j_282_, v___x_289_);
switch(lean_obj_tag(v_v_288_))
{
case 0:
{
lean_object* v_key_297_; lean_object* v_val_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_308_; 
v_key_297_ = lean_ctor_get(v_v_288_, 0);
v_val_298_ = lean_ctor_get(v_v_288_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_v_288_);
if (v_isSharedCheck_308_ == 0)
{
v___x_300_ = v_v_288_;
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_val_298_);
lean_inc(v_key_297_);
lean_dec(v_v_288_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
uint8_t v___x_302_; 
v___x_302_ = l_Lean_instBEqMVarId_beq(v_x_277_, v_key_297_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_del_object(v___x_300_);
v___x_303_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_297_, v_val_298_, v_x_277_, v_x_278_);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
v___y_292_ = v___x_304_;
goto v___jp_291_;
}
else
{
lean_object* v___x_306_; 
lean_dec(v_val_298_);
lean_dec(v_key_297_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_x_278_);
lean_ctor_set(v___x_300_, 0, v_x_277_);
v___x_306_ = v___x_300_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_x_277_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_x_278_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
v___y_292_ = v___x_306_;
goto v___jp_291_;
}
}
}
}
case 1:
{
lean_object* v_node_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_321_; 
v_node_309_ = lean_ctor_get(v_v_288_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_v_288_);
if (v_isSharedCheck_321_ == 0)
{
v___x_311_ = v_v_288_;
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_node_309_);
lean_dec(v_v_288_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_313_ = ((size_t)5ULL);
v___x_314_ = lean_usize_shift_right(v_x_275_, v___x_313_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_add(v_x_276_, v___x_315_);
v___x_317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_node_309_, v___x_314_, v___x_316_, v_x_277_, v_x_278_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_317_);
v___x_319_ = v___x_311_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
v___y_292_ = v___x_319_;
goto v___jp_291_;
}
}
}
default: 
{
lean_object* v___x_322_; 
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v_x_277_);
lean_ctor_set(v___x_322_, 1, v_x_278_);
v___y_292_ = v___x_322_;
goto v___jp_291_;
}
}
v___jp_291_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_array_fset(v_xs_x27_290_, v_j_282_, v___y_292_);
lean_dec(v_j_282_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_293_);
v___x_295_ = v___x_286_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
else
{
lean_object* v_ks_325_; lean_object* v_vs_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_344_; 
v_ks_325_ = lean_ctor_get(v_x_274_, 0);
v_vs_326_ = lean_ctor_get(v_x_274_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_x_274_);
if (v_isSharedCheck_344_ == 0)
{
v___x_328_ = v_x_274_;
v_isShared_329_ = v_isSharedCheck_344_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_vs_326_);
lean_inc(v_ks_325_);
lean_dec(v_x_274_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_344_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_ks_325_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_vs_326_);
v___x_331_ = v_reuseFailAlloc_343_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v_newNode_332_; size_t v___x_333_; uint8_t v___x_334_; 
v_newNode_332_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v___x_331_, v_x_277_, v_x_278_);
v___x_333_ = ((size_t)7ULL);
v___x_334_ = lean_usize_dec_le(v___x_333_, v_x_276_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_335_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_332_);
v___x_336_ = lean_unsigned_to_nat(4u);
v___x_337_ = lean_nat_dec_lt(v___x_335_, v___x_336_);
lean_dec(v___x_335_);
if (v___x_337_ == 0)
{
lean_object* v_ks_338_; lean_object* v_vs_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_ks_338_ = lean_ctor_get(v_newNode_332_, 0);
lean_inc_ref(v_ks_338_);
v_vs_339_ = lean_ctor_get(v_newNode_332_, 1);
lean_inc_ref(v_vs_339_);
lean_dec_ref(v_newNode_332_);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_342_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_x_276_, v_ks_338_, v_vs_339_, v___x_340_, v___x_341_);
lean_dec_ref(v_vs_339_);
lean_dec_ref(v_ks_338_);
return v___x_342_;
}
else
{
return v_newNode_332_;
}
}
else
{
return v_newNode_332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_345_, lean_object* v_keys_346_, lean_object* v_vals_347_, lean_object* v_i_348_, lean_object* v_entries_349_){
_start:
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_array_get_size(v_keys_346_);
v___x_351_ = lean_nat_dec_lt(v_i_348_, v___x_350_);
if (v___x_351_ == 0)
{
lean_dec(v_i_348_);
return v_entries_349_;
}
else
{
lean_object* v_k_352_; lean_object* v_v_353_; uint64_t v___x_354_; size_t v_h_355_; size_t v___x_356_; lean_object* v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v_h_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_k_352_ = lean_array_fget_borrowed(v_keys_346_, v_i_348_);
v_v_353_ = lean_array_fget_borrowed(v_vals_347_, v_i_348_);
v___x_354_ = l_Lean_instHashableMVarId_hash(v_k_352_);
v_h_355_ = lean_uint64_to_usize(v___x_354_);
v___x_356_ = ((size_t)5ULL);
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_sub(v_depth_345_, v___x_358_);
v___x_360_ = lean_usize_mul(v___x_356_, v___x_359_);
v_h_361_ = lean_usize_shift_right(v_h_355_, v___x_360_);
v___x_362_ = lean_nat_add(v_i_348_, v___x_357_);
lean_dec(v_i_348_);
lean_inc(v_v_353_);
lean_inc(v_k_352_);
v___x_363_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_entries_349_, v_h_361_, v_depth_345_, v_k_352_, v_v_353_);
v_i_348_ = v___x_362_;
v_entries_349_ = v___x_363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_365_, lean_object* v_keys_366_, lean_object* v_vals_367_, lean_object* v_i_368_, lean_object* v_entries_369_){
_start:
{
size_t v_depth_boxed_370_; lean_object* v_res_371_; 
v_depth_boxed_370_ = lean_unbox_usize(v_depth_365_);
lean_dec(v_depth_365_);
v_res_371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_370_, v_keys_366_, v_vals_367_, v_i_368_, v_entries_369_);
lean_dec_ref(v_vals_367_);
lean_dec_ref(v_keys_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
size_t v_x_6126__boxed_377_; size_t v_x_6127__boxed_378_; lean_object* v_res_379_; 
v_x_6126__boxed_377_ = lean_unbox_usize(v_x_373_);
lean_dec(v_x_373_);
v_x_6127__boxed_378_ = lean_unbox_usize(v_x_374_);
lean_dec(v_x_374_);
v_res_379_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_372_, v_x_6126__boxed_377_, v_x_6127__boxed_378_, v_x_375_, v_x_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
uint64_t v___x_383_; size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; 
v___x_383_ = l_Lean_instHashableMVarId_hash(v_x_381_);
v___x_384_ = lean_uint64_to_usize(v___x_383_);
v___x_385_ = ((size_t)1ULL);
v___x_386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_380_, v___x_384_, v___x_385_, v_x_381_, v_x_382_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(lean_object* v_mvarId_387_, lean_object* v_val_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; lean_object* v_mctx_392_; lean_object* v_cache_393_; lean_object* v_zetaDeltaFVarIds_394_; lean_object* v_postponed_395_; lean_object* v_diag_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_425_; 
v___x_391_ = lean_st_ref_take(v___y_389_);
v_mctx_392_ = lean_ctor_get(v___x_391_, 0);
v_cache_393_ = lean_ctor_get(v___x_391_, 1);
v_zetaDeltaFVarIds_394_ = lean_ctor_get(v___x_391_, 2);
v_postponed_395_ = lean_ctor_get(v___x_391_, 3);
v_diag_396_ = lean_ctor_get(v___x_391_, 4);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_425_ == 0)
{
v___x_398_ = v___x_391_;
v_isShared_399_ = v_isSharedCheck_425_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_diag_396_);
lean_inc(v_postponed_395_);
lean_inc(v_zetaDeltaFVarIds_394_);
lean_inc(v_cache_393_);
lean_inc(v_mctx_392_);
lean_dec(v___x_391_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_425_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_depth_400_; lean_object* v_levelAssignDepth_401_; lean_object* v_lmvarCounter_402_; lean_object* v_mvarCounter_403_; lean_object* v_lDecls_404_; lean_object* v_decls_405_; lean_object* v_userNames_406_; lean_object* v_lAssignment_407_; lean_object* v_eAssignment_408_; lean_object* v_dAssignment_409_; lean_object* v_instanceTypedMVars_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_424_; 
v_depth_400_ = lean_ctor_get(v_mctx_392_, 0);
v_levelAssignDepth_401_ = lean_ctor_get(v_mctx_392_, 1);
v_lmvarCounter_402_ = lean_ctor_get(v_mctx_392_, 2);
v_mvarCounter_403_ = lean_ctor_get(v_mctx_392_, 3);
v_lDecls_404_ = lean_ctor_get(v_mctx_392_, 4);
v_decls_405_ = lean_ctor_get(v_mctx_392_, 5);
v_userNames_406_ = lean_ctor_get(v_mctx_392_, 6);
v_lAssignment_407_ = lean_ctor_get(v_mctx_392_, 7);
v_eAssignment_408_ = lean_ctor_get(v_mctx_392_, 8);
v_dAssignment_409_ = lean_ctor_get(v_mctx_392_, 9);
v_instanceTypedMVars_410_ = lean_ctor_get(v_mctx_392_, 10);
v_isSharedCheck_424_ = !lean_is_exclusive(v_mctx_392_);
if (v_isSharedCheck_424_ == 0)
{
v___x_412_ = v_mctx_392_;
v_isShared_413_ = v_isSharedCheck_424_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_instanceTypedMVars_410_);
lean_inc(v_dAssignment_409_);
lean_inc(v_eAssignment_408_);
lean_inc(v_lAssignment_407_);
lean_inc(v_userNames_406_);
lean_inc(v_decls_405_);
lean_inc(v_lDecls_404_);
lean_inc(v_mvarCounter_403_);
lean_inc(v_lmvarCounter_402_);
lean_inc(v_levelAssignDepth_401_);
lean_inc(v_depth_400_);
lean_dec(v_mctx_392_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_424_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_eAssignment_408_, v_mvarId_387_, v_val_388_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 8, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_depth_400_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_levelAssignDepth_401_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_lmvarCounter_402_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_mvarCounter_403_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_lDecls_404_);
lean_ctor_set(v_reuseFailAlloc_423_, 5, v_decls_405_);
lean_ctor_set(v_reuseFailAlloc_423_, 6, v_userNames_406_);
lean_ctor_set(v_reuseFailAlloc_423_, 7, v_lAssignment_407_);
lean_ctor_set(v_reuseFailAlloc_423_, 8, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_423_, 9, v_dAssignment_409_);
lean_ctor_set(v_reuseFailAlloc_423_, 10, v_instanceTypedMVars_410_);
v___x_416_ = v_reuseFailAlloc_423_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_416_);
v___x_418_ = v___x_398_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_cache_393_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_zetaDeltaFVarIds_394_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_postponed_395_);
lean_ctor_set(v_reuseFailAlloc_422_, 4, v_diag_396_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_st_ref_put(v___y_389_, v___x_418_);
v___x_420_ = lean_box(0);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg___boxed(lean_object* v_mvarId_426_, lean_object* v_val_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_426_, v_val_427_, v___y_428_);
lean_dec(v___y_428_);
return v_res_430_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_437_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4));
v___x_438_ = lean_unsigned_to_nat(41u);
v___x_439_ = lean_unsigned_to_nat(34u);
v___x_440_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3));
v___x_441_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_442_ = l_mkPanicMessageWithDecl(v___x_441_, v___x_440_, v___x_439_, v___x_438_, v___x_437_);
return v___x_442_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9));
v___x_450_ = l_Lean_stringToMessageData(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18(void){
_start:
{
lean_object* v___x_465_; lean_object* v_dummy_466_; 
v___x_465_ = lean_box(0);
v_dummy_466_ = l_Lean_Expr_sort___override(v___x_465_);
return v_dummy_466_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20));
v___x_473_ = l_Lean_stringToMessageData(v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object* v_mvarId_474_, lean_object* v___x_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; 
lean_inc(v_mvarId_474_);
v___x_481_ = l_Lean_MVarId_getType_x27(v_mvarId_474_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_481_, 1);
v___x_483_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_484_ = lean_unsigned_to_nat(3u);
v___x_485_ = l_Lean_Expr_isAppOfArity(v_a_482_, v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec(v_a_482_);
lean_dec_ref(v___x_475_);
lean_dec(v_mvarId_474_);
v___x_486_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5);
v___x_487_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(v___x_486_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; 
v___x_488_ = lean_box(v___x_485_);
v___f_489_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_489_, 0, v___x_488_);
v___x_490_ = l_Lean_Expr_appFn_x21(v_a_482_);
v___x_491_ = l_Lean_Expr_appArg_x21(v___x_490_);
lean_dec_ref(v___x_490_);
v___x_492_ = 0;
lean_inc_ref(v___x_491_);
v___x_493_ = l_Lean_Meta_delta_x3f(v___x_491_, v___f_489_, v___x_492_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
if (lean_obj_tag(v_a_494_) == 1)
{
lean_object* v_val_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_648_; 
v_val_495_ = lean_ctor_get(v_a_494_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_a_494_);
if (v_isSharedCheck_648_ == 0)
{
v___x_497_ = v_a_494_;
v_isShared_498_ = v_isSharedCheck_648_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_val_495_);
lean_dec(v_a_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_648_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; 
lean_inc(v_val_495_);
v___x_499_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_val_495_, v___y_477_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v_h_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v___x_501_ = lean_box(v___x_492_);
v___x_502_ = lean_box(v___x_485_);
v___f_503_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed), 11, 4);
lean_closure_set(v___f_503_, 0, v___x_491_);
lean_closure_set(v___f_503_, 1, v___x_475_);
lean_closure_set(v___f_503_, 2, v___x_501_);
lean_closure_set(v___f_503_, 3, v___x_502_);
v___x_504_ = l_Lean_Expr_appArg_x21(v_a_482_);
lean_dec(v_a_482_);
v___x_601_ = l_Lean_Expr_cleanupAnnotations(v_a_500_);
v___x_602_ = l_Lean_Expr_isApp(v___x_601_);
if (v___x_602_ == 0)
{
lean_dec_ref(v___x_601_);
v___y_580_ = v___y_476_;
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
goto v___jp_579_;
}
else
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = l_Lean_Expr_appFnCleanup___redArg(v___x_601_);
v___x_604_ = l_Lean_Expr_isApp(v___x_603_);
if (v___x_604_ == 0)
{
lean_dec_ref(v___x_603_);
v___y_580_ = v___y_476_;
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
goto v___jp_579_;
}
else
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = l_Lean_Expr_appFnCleanup___redArg(v___x_603_);
v___x_606_ = l_Lean_Expr_isApp(v___x_605_);
if (v___x_606_ == 0)
{
lean_dec_ref(v___x_605_);
v___y_580_ = v___y_476_;
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
goto v___jp_579_;
}
else
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = l_Lean_Expr_appFnCleanup___redArg(v___x_605_);
v___x_608_ = l_Lean_Expr_isApp(v___x_607_);
if (v___x_608_ == 0)
{
lean_dec_ref(v___x_607_);
v___y_580_ = v___y_476_;
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
goto v___jp_579_;
}
else
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = l_Lean_Expr_appFnCleanup___redArg(v___x_607_);
v___x_610_ = l_Lean_Expr_isApp(v___x_609_);
if (v___x_610_ == 0)
{
lean_dec_ref(v___x_609_);
v___y_580_ = v___y_476_;
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
goto v___jp_579_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = l_Lean_Expr_appFnCleanup___redArg(v___x_609_);
v___x_612_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14));
v___x_613_ = l_Lean_Expr_isConstOf(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = l_Lean_Expr_isApp(v___x_611_);
if (v___x_614_ == 0)
{
lean_dec_ref(v___x_611_);
v___y_580_ = v___y_476_;
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
goto v___jp_579_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_615_ = l_Lean_Expr_appFnCleanup___redArg(v___x_611_);
v___x_616_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15));
v___x_617_ = l_Lean_Expr_isConstOf(v___x_615_, v___x_616_);
lean_dec_ref(v___x_615_);
if (v___x_617_ == 0)
{
v___y_580_ = v___y_476_;
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
goto v___jp_579_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_dummy_622_; lean_object* v_nargs_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
lean_del_object(v___x_497_);
v___x_618_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17));
v___x_619_ = l_Lean_Expr_getAppFn(v_val_495_);
v___x_620_ = l_Lean_Expr_constLevels_x21(v___x_619_);
lean_dec_ref(v___x_619_);
v___x_621_ = l_Lean_mkConst(v___x_618_, v___x_620_);
v_dummy_622_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_623_ = l_Lean_Expr_getAppNumArgs(v_val_495_);
lean_inc(v_nargs_623_);
v___x_624_ = lean_mk_array(v_nargs_623_, v_dummy_622_);
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_sub(v_nargs_623_, v___x_625_);
lean_dec(v_nargs_623_);
lean_inc(v_val_495_);
v___x_627_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_495_, v___x_624_, v___x_626_);
v___x_628_ = l_Lean_mkAppN(v___x_621_, v___x_627_);
lean_dec_ref(v___x_627_);
v_h_506_ = v___x_628_;
v___y_507_ = v___y_476_;
v___y_508_ = v___y_477_;
v___y_509_ = v___y_478_;
v___y_510_ = v___y_479_;
goto v___jp_505_;
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v_dummy_633_; lean_object* v_nargs_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec_ref(v___x_611_);
lean_del_object(v___x_497_);
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19));
v___x_630_ = l_Lean_Expr_getAppFn(v_val_495_);
v___x_631_ = l_Lean_Expr_constLevels_x21(v___x_630_);
lean_dec_ref(v___x_630_);
v___x_632_ = l_Lean_mkConst(v___x_629_, v___x_631_);
v_dummy_633_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_634_ = l_Lean_Expr_getAppNumArgs(v_val_495_);
lean_inc(v_nargs_634_);
v___x_635_ = lean_mk_array(v_nargs_634_, v_dummy_633_);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = lean_nat_sub(v_nargs_634_, v___x_636_);
lean_dec(v_nargs_634_);
lean_inc(v_val_495_);
v___x_638_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_495_, v___x_635_, v___x_637_);
v___x_639_ = l_Lean_mkAppN(v___x_632_, v___x_638_);
lean_dec_ref(v___x_638_);
v_h_506_ = v___x_639_;
v___y_507_ = v___y_476_;
v___y_508_ = v___y_477_;
v___y_509_ = v___y_478_;
v___y_510_ = v___y_479_;
goto v___jp_505_;
}
}
}
}
}
}
v___jp_505_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_511_ = l_Lean_Expr_appFn_x21(v_val_495_);
v___x_512_ = l_Lean_Expr_appArg_x21(v___x_511_);
lean_dec_ref(v___x_511_);
v___x_513_ = l_Lean_Expr_appArg_x21(v_val_495_);
lean_dec(v_val_495_);
lean_inc_ref(v___x_513_);
lean_inc_ref(v___x_512_);
v___x_514_ = l_Lean_Expr_app___override(v___x_512_, v___x_513_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
v___x_515_ = lean_infer_type(v___x_514_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = l_Lean_Expr_bindingDomain_x21(v_a_516_);
lean_dec(v_a_516_);
v___x_518_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_519_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_517_, v___x_518_, v___f_503_, v___x_492_, v___x_492_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = l_Lean_mkAppB(v___x_512_, v___x_513_, v_a_520_);
v___x_522_ = l_Lean_Meta_mkEq(v___x_521_, v___x_504_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = lean_box(0);
v___x_525_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_523_, v___x_524_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc_n(v_a_526_, 2);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = l_Lean_Meta_mkEqTrans(v_h_506_, v_a_526_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v___y_507_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_537_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_527_, 1);
v___x_529_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_474_, v_a_528_, v___y_508_);
lean_dec(v___y_508_);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; 
v_unused_538_ = lean_ctor_get(v___x_529_, 0);
lean_dec(v_unused_538_);
v___x_531_ = v___x_529_;
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
else
{
lean_dec(v___x_529_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = l_Lean_Expr_mvarId_x21(v_a_526_);
lean_dec(v_a_526_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_a_526_);
lean_dec(v___y_508_);
lean_dec(v_mvarId_474_);
v_a_539_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_527_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_527_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec_ref(v_h_506_);
lean_dec(v_mvarId_474_);
v_a_547_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_525_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_525_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec_ref(v_h_506_);
lean_dec(v_mvarId_474_);
v_a_555_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_522_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_522_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec_ref(v___x_513_);
lean_dec_ref(v___x_512_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec_ref(v_h_506_);
lean_dec_ref(v___x_504_);
lean_dec(v_mvarId_474_);
v_a_563_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_519_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_519_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
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
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v___x_513_);
lean_dec_ref(v___x_512_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec_ref(v_h_506_);
lean_dec_ref(v___x_504_);
lean_dec_ref(v___f_503_);
lean_dec(v_mvarId_474_);
v_a_571_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_515_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_515_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
v___jp_579_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_584_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8));
v___x_585_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10);
lean_inc(v_val_495_);
v___x_586_ = l_Lean_MessageData_ofExpr(v_val_495_);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_587_);
v___x_589_ = v___x_497_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_600_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; 
lean_inc(v_mvarId_474_);
v___x_590_ = l_Lean_Meta_throwTacticEx___redArg(v___x_584_, v_mvarId_474_, v___x_589_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v_h_506_ = v_a_591_;
v___y_507_ = v___y_580_;
v___y_508_ = v___y_581_;
v___y_509_ = v___y_582_;
v___y_510_ = v___y_583_;
goto v___jp_505_;
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v___x_504_);
lean_dec_ref(v___f_503_);
lean_dec(v_val_495_);
lean_dec(v_mvarId_474_);
v_a_592_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_590_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_590_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_del_object(v___x_497_);
lean_dec(v_val_495_);
lean_dec_ref(v___x_491_);
lean_dec(v_a_482_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v___x_475_);
lean_dec(v_mvarId_474_);
v_a_640_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_499_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_499_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec(v_a_494_);
lean_dec(v_a_482_);
lean_dec_ref(v___x_475_);
lean_dec(v_mvarId_474_);
v___x_649_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21);
v___x_650_ = l_Lean_MessageData_ofExpr(v___x_491_);
v___x_651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_651_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v___x_652_;
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref(v___x_491_);
lean_dec(v_a_482_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v___x_475_);
lean_dec(v_mvarId_474_);
v_a_653_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_493_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_493_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v___x_475_);
lean_dec(v_mvarId_474_);
v_a_661_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_481_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_481_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed(lean_object* v_mvarId_669_, lean_object* v___x_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(v_mvarId_669_, v___x_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(lean_object* v_mvarId_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___x_683_; lean_object* v___f_684_; lean_object* v___x_685_; 
v___x_683_ = l_Lean_instInhabitedExpr;
lean_inc(v_mvarId_677_);
v___f_684_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed), 7, 2);
lean_closure_set(v___f_684_, 0, v_mvarId_677_);
lean_closure_set(v___f_684_, 1, v___x_683_);
v___x_685_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(v_mvarId_677_, v___f_684_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___boxed(lean_object* v_mvarId_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(lean_object* v_mvarId_693_, lean_object* v_val_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_693_, v_val_694_, v___y_696_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___boxed(lean_object* v_mvarId_701_, lean_object* v_val_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(v_mvarId_701_, v_val_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(lean_object* v_00_u03b1_709_, lean_object* v_msg_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___boxed(lean_object* v_00_u03b1_717_, lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(v_00_u03b1_717_, v_msg_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2(lean_object* v_00_u03b2_725_, lean_object* v_x_726_, lean_object* v_x_727_, lean_object* v_x_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_x_726_, v_x_727_, v_x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_730_, lean_object* v_x_731_, size_t v_x_732_, size_t v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_731_, v_x_732_, v_x_733_, v_x_734_, v_x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_737_, lean_object* v_x_738_, lean_object* v_x_739_, lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
size_t v_x_6901__boxed_743_; size_t v_x_6902__boxed_744_; lean_object* v_res_745_; 
v_x_6901__boxed_743_ = lean_unbox_usize(v_x_739_);
lean_dec(v_x_739_);
v_x_6902__boxed_744_ = lean_unbox_usize(v_x_740_);
lean_dec(v_x_740_);
v_res_745_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(v_00_u03b2_737_, v_x_738_, v_x_6901__boxed_743_, v_x_6902__boxed_744_, v_x_741_, v_x_742_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_746_, lean_object* v_n_747_, lean_object* v_k_748_, lean_object* v_v_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v_n_747_, v_k_748_, v_v_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_751_, size_t v_depth_752_, lean_object* v_keys_753_, lean_object* v_vals_754_, lean_object* v_heq_755_, lean_object* v_i_756_, lean_object* v_entries_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_752_, v_keys_753_, v_vals_754_, v_i_756_, v_entries_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_759_, lean_object* v_depth_760_, lean_object* v_keys_761_, lean_object* v_vals_762_, lean_object* v_heq_763_, lean_object* v_i_764_, lean_object* v_entries_765_){
_start:
{
size_t v_depth_boxed_766_; lean_object* v_res_767_; 
v_depth_boxed_766_ = lean_unbox_usize(v_depth_760_);
lean_dec(v_depth_760_);
v_res_767_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_759_, v_depth_boxed_766_, v_keys_761_, v_vals_762_, v_heq_763_, v_i_764_, v_entries_765_);
lean_dec_ref(v_vals_762_);
lean_dec_ref(v_keys_761_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_768_, lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_769_, v_x_770_, v_x_771_, v_x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(lean_object* v_e_774_, lean_object* v_maxFVars_775_, lean_object* v_k_776_, uint8_t v_cleanupAnnotations_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___f_783_; uint8_t v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___f_783_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_783_, 0, v_k_776_);
v___x_784_ = 1;
v___x_785_ = 0;
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v_maxFVars_775_);
v___x_787_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_774_, v___x_784_, v___x_785_, v___x_784_, v___x_785_, v___x_786_, v___f_783_, v_cleanupAnnotations_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec_ref_known(v___x_786_, 1);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_796_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_787_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_787_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg___boxed(lean_object* v_e_804_, lean_object* v_maxFVars_805_, lean_object* v_k_806_, lean_object* v_cleanupAnnotations_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_813_; lean_object* v_res_814_; 
v_cleanupAnnotations_boxed_813_ = lean_unbox(v_cleanupAnnotations_807_);
v_res_814_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_804_, v_maxFVars_805_, v_k_806_, v_cleanupAnnotations_boxed_813_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(lean_object* v_00_u03b1_815_, lean_object* v_e_816_, lean_object* v_maxFVars_817_, lean_object* v_k_818_, uint8_t v_cleanupAnnotations_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_816_, v_maxFVars_817_, v_k_818_, v_cleanupAnnotations_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___boxed(lean_object* v_00_u03b1_826_, lean_object* v_e_827_, lean_object* v_maxFVars_828_, lean_object* v_k_829_, lean_object* v_cleanupAnnotations_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_836_; lean_object* v_res_837_; 
v_cleanupAnnotations_boxed_836_ = lean_unbox(v_cleanupAnnotations_830_);
v_res_837_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(v_00_u03b1_826_, v_e_827_, v_maxFVars_828_, v_k_829_, v_cleanupAnnotations_boxed_836_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(lean_object* v___x_838_, lean_object* v_xs_839_, lean_object* v_t_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = lean_array_get_size(v_xs_839_);
v___x_850_ = lean_nat_dec_eq(v___x_849_, v___x_838_);
if (v___x_850_ == 0)
{
goto v___jp_846_;
}
else
{
uint8_t v___x_851_; 
v___x_851_ = l_Lean_Expr_isForall(v_t_840_);
if (v___x_851_ == 0)
{
goto v___jp_846_;
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_852_ = l_Lean_Expr_bindingBody_x21(v_t_840_);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_expr_has_loose_bvar(v___x_852_, v___x_853_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; lean_object* v___x_856_; 
v___x_855_ = 1;
v___x_856_ = l_Lean_Meta_mkLambdaFVars(v_xs_839_, v___x_852_, v___x_854_, v___x_851_, v___x_854_, v___x_851_, v___x_855_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_865_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_865_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v_a_857_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_861_);
v___x_863_ = v___x_859_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_a_866_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_856_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_856_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_dec_ref(v___x_852_);
goto v___jp_846_;
}
}
}
v___jp_846_:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_box(0);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed(lean_object* v___x_874_, lean_object* v_xs_875_, lean_object* v_t_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(v___x_874_, v_xs_875_, v_t_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v_t_876_);
lean_dec_ref(v_xs_875_);
lean_dec(v___x_874_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(lean_object* v_matcherApp_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_motive_889_; lean_object* v_discrs_890_; lean_object* v___x_891_; lean_object* v___f_892_; uint8_t v___x_893_; lean_object* v___x_894_; 
v_motive_889_ = lean_ctor_get(v_matcherApp_883_, 4);
lean_inc_ref(v_motive_889_);
v_discrs_890_ = lean_ctor_get(v_matcherApp_883_, 5);
lean_inc_ref(v_discrs_890_);
lean_dec_ref(v_matcherApp_883_);
v___x_891_ = lean_array_get_size(v_discrs_890_);
lean_dec_ref(v_discrs_890_);
v___f_892_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed), 8, 1);
lean_closure_set(v___f_892_, 0, v___x_891_);
v___x_893_ = 0;
v___x_894_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_motive_889_, v___x_891_, v___f_892_, v___x_893_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___boxed(lean_object* v_matcherApp_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_matcherApp_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(lean_object* v_e_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; lean_object* v_env_906_; uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_905_ = lean_st_ref_get(v___y_903_);
v_env_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc_ref(v_env_906_);
lean_dec(v___x_905_);
v___x_907_ = l_Lean_Meta_isMatcherAppCore(v_env_906_, v_e_902_);
v___x_908_ = lean_box(v___x_907_);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg___boxed(lean_object* v_e_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v_e_910_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(lean_object* v_e_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_914_, v___y_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___boxed(lean_object* v_e_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(v_e_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec_ref(v_e_921_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(lean_object* v_msg_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___f_934_; lean_object* v___x_612__overap_935_; lean_object* v___x_936_; 
v___f_934_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_612__overap_935_ = lean_panic_fn_borrowed(v___f_934_, v_msg_928_);
lean_inc(v___y_932_);
lean_inc_ref(v___y_931_);
lean_inc(v___y_930_);
lean_inc_ref(v___y_929_);
v___x_936_ = lean_apply_5(v___x_612__overap_935_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, lean_box(0));
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1___boxed(lean_object* v_msg_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v_msg_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(size_t v_sz_944_, size_t v_i_945_, lean_object* v_bs_946_){
_start:
{
uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_lt(v_i_945_, v_sz_944_);
if (v___x_947_ == 0)
{
return v_bs_946_;
}
else
{
lean_object* v_v_948_; lean_object* v_toInductionSubgoal_949_; lean_object* v_mvarId_950_; lean_object* v___x_951_; lean_object* v_bs_x27_952_; size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
v_v_948_ = lean_array_uget_borrowed(v_bs_946_, v_i_945_);
v_toInductionSubgoal_949_ = lean_ctor_get(v_v_948_, 0);
v_mvarId_950_ = lean_ctor_get(v_toInductionSubgoal_949_, 0);
lean_inc(v_mvarId_950_);
v___x_951_ = lean_unsigned_to_nat(0u);
v_bs_x27_952_ = lean_array_uset(v_bs_946_, v_i_945_, v___x_951_);
v___x_953_ = ((size_t)1ULL);
v___x_954_ = lean_usize_add(v_i_945_, v___x_953_);
v___x_955_ = lean_array_uset(v_bs_x27_952_, v_i_945_, v_mvarId_950_);
v_i_945_ = v___x_954_;
v_bs_946_ = v___x_955_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2___boxed(lean_object* v_sz_957_, lean_object* v_i_958_, lean_object* v_bs_959_){
_start:
{
size_t v_sz_boxed_960_; size_t v_i_boxed_961_; lean_object* v_res_962_; 
v_sz_boxed_960_ = lean_unbox_usize(v_sz_957_);
lean_dec(v_sz_957_);
v_i_boxed_961_ = lean_unbox_usize(v_i_958_);
lean_dec(v_i_958_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_boxed_960_, v_i_boxed_961_, v_bs_959_);
return v_res_962_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_965_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1));
v___x_966_ = lean_unsigned_to_nat(4u);
v___x_967_ = lean_unsigned_to_nat(79u);
v___x_968_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0));
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_970_ = l_mkPanicMessageWithDecl(v___x_969_, v___x_968_, v___x_967_, v___x_966_, v___x_965_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(lean_object* v_mvarId_973_, lean_object* v_e_974_, lean_object* v_matcherInfo_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___x_981_; lean_object* v_a_982_; uint8_t v___x_983_; 
v___x_981_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_974_, v_a_979_);
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref(v___x_981_);
v___x_983_ = lean_unbox(v_a_982_);
if (v___x_983_ == 0)
{
lean_object* v_numParams_984_; lean_object* v_numDiscrs_985_; lean_object* v_nargs_986_; lean_object* v___x_987_; lean_object* v_dummy_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_numParams_984_ = lean_ctor_get(v_matcherInfo_975_, 0);
v_numDiscrs_985_ = lean_ctor_get(v_matcherInfo_975_, 1);
v_nargs_986_ = l_Lean_Expr_getAppNumArgs(v_e_974_);
v___x_987_ = l_Lean_instInhabitedExpr;
v_dummy_988_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_986_);
v___x_989_ = lean_mk_array(v_nargs_986_, v_dummy_988_);
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_sub(v_nargs_986_, v___x_990_);
lean_dec(v_nargs_986_);
v___x_992_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_974_, v___x_989_, v___x_991_);
v___x_993_ = lean_nat_add(v_numParams_984_, v_numDiscrs_985_);
v___x_994_ = lean_array_get(v___x_987_, v___x_992_, v___x_993_);
lean_dec(v___x_993_);
lean_dec_ref(v___x_992_);
v___x_995_ = l_Lean_Expr_isFVar(v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec(v___x_994_);
lean_dec(v_a_982_);
lean_dec(v_mvarId_973_);
v___x_996_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2);
v___x_997_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v___x_996_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_997_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; lean_object* v___x_1002_; 
v___x_998_ = l_Lean_Expr_fvarId_x21(v___x_994_);
lean_dec(v___x_994_);
v___x_999_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3));
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_unbox(v_a_982_);
lean_dec(v_a_982_);
v___x_1002_ = l_Lean_MVarId_cases(v_mvarId_973_, v___x_998_, v___x_999_, v___x_1001_, v___x_1000_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1014_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1014_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1014_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
size_t v_sz_1007_; size_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v_sz_1007_ = lean_array_size(v_a_1003_);
v___x_1008_ = ((size_t)0ULL);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_1007_, v___x_1008_, v_a_1003_);
v___x_1010_ = lean_array_to_list(v___x_1009_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1010_);
v___x_1012_ = v___x_1005_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1002_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1002_);
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
lean_object* v___x_1023_; 
lean_dec(v_a_982_);
v___x_1023_ = l_Lean_Meta_Split_splitMatch(v_mvarId_973_, v_e_974_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___boxed(lean_object* v_mvarId_1024_, lean_object* v_e_1025_, lean_object* v_matcherInfo_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v_mvarId_1024_, v_e_1025_, v_matcherInfo_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec_ref(v_matcherInfo_1026_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(lean_object* v_msg_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___f_1039_; lean_object* v___x_11818__overap_1040_; lean_object* v___x_1041_; 
v___f_1039_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_11818__overap_1040_ = lean_panic_fn_borrowed(v___f_1039_, v_msg_1033_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc_ref(v___y_1034_);
v___x_1041_ = lean_apply_5(v___x_11818__overap_1040_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, lean_box(0));
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1___boxed(lean_object* v_msg_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v_msg_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(lean_object* v_type_1049_, lean_object* v_k_1050_, uint8_t v_cleanupAnnotations_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___f_1057_; uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___f_1057_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1057_, 0, v_k_1050_);
v___x_1058_ = 0;
v___x_1059_ = lean_box(0);
v___x_1060_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1058_, v___x_1059_, v_type_1049_, v___f_1057_, v_cleanupAnnotations_1051_, v___x_1058_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_a_1069_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1060_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1060_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg___boxed(lean_object* v_type_1077_, lean_object* v_k_1078_, lean_object* v_cleanupAnnotations_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1085_; lean_object* v_res_1086_; 
v_cleanupAnnotations_boxed_1085_ = lean_unbox(v_cleanupAnnotations_1079_);
v_res_1086_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1077_, v_k_1078_, v_cleanupAnnotations_boxed_1085_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(lean_object* v_00_u03b1_1087_, lean_object* v_type_1088_, lean_object* v_k_1089_, uint8_t v_cleanupAnnotations_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1088_, v_k_1089_, v_cleanupAnnotations_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___boxed(lean_object* v_00_u03b1_1097_, lean_object* v_type_1098_, lean_object* v_k_1099_, lean_object* v_cleanupAnnotations_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1106_; lean_object* v_res_1107_; 
v_cleanupAnnotations_boxed_1106_ = lean_unbox(v_cleanupAnnotations_1100_);
v_res_1107_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(v_00_u03b1_1097_, v_type_1098_, v_k_1099_, v_cleanupAnnotations_boxed_1106_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(lean_object* v_e_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v___x_1111_; 
v___x_1111_ = l_Lean_Expr_hasMVar(v_e_1108_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_e_1108_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; lean_object* v_mctx_1114_; lean_object* v___x_1115_; lean_object* v_fst_1116_; lean_object* v_snd_1117_; lean_object* v___x_1118_; lean_object* v_cache_1119_; lean_object* v_zetaDeltaFVarIds_1120_; lean_object* v_postponed_1121_; lean_object* v_diag_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1131_; 
v___x_1113_ = lean_st_ref_get(v___y_1109_);
v_mctx_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_mctx_1114_);
lean_dec(v___x_1113_);
v___x_1115_ = l_Lean_instantiateMVarsCore(v_mctx_1114_, v_e_1108_);
v_fst_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_fst_1116_);
v_snd_1117_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_snd_1117_);
lean_dec_ref(v___x_1115_);
v___x_1118_ = lean_st_ref_take(v___y_1109_);
v_cache_1119_ = lean_ctor_get(v___x_1118_, 1);
v_zetaDeltaFVarIds_1120_ = lean_ctor_get(v___x_1118_, 2);
v_postponed_1121_ = lean_ctor_get(v___x_1118_, 3);
v_diag_1122_ = lean_ctor_get(v___x_1118_, 4);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v___x_1118_, 0);
lean_dec(v_unused_1132_);
v___x_1124_ = v___x_1118_;
v_isShared_1125_ = v_isSharedCheck_1131_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_diag_1122_);
lean_inc(v_postponed_1121_);
lean_inc(v_zetaDeltaFVarIds_1120_);
lean_inc(v_cache_1119_);
lean_dec(v___x_1118_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1131_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v_snd_1117_);
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_snd_1117_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_cache_1119_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_zetaDeltaFVarIds_1120_);
lean_ctor_set(v_reuseFailAlloc_1130_, 3, v_postponed_1121_);
lean_ctor_set(v_reuseFailAlloc_1130_, 4, v_diag_1122_);
v___x_1127_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_st_ref_put(v___y_1109_, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_fst_1116_);
return v___x_1129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg___boxed(lean_object* v_e_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1133_, v___y_1134_);
lean_dec(v___y_1134_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(lean_object* v_e_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1137_, v___y_1139_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___boxed(lean_object* v_e_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(v_e_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(lean_object* v_x_1151_, lean_object* v_motiveBody_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Meta_getLevel(v_motiveBody_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0___boxed(lean_object* v_x_1159_, lean_object* v_motiveBody_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(v_x_1159_, v_motiveBody_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v_x_1159_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(lean_object* v___x_1167_, lean_object* v___x_1168_, lean_object* v_alpha_1169_, uint8_t v___x_1170_, lean_object* v_xs_1171_, lean_object* v_x_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; uint8_t v___x_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1178_ = l_Lean_Level_ofNat(v___x_1167_);
v___x_1179_ = l_Lean_Expr_sort___override(v___x_1178_);
v___x_1180_ = l_Lean_Expr_forallE___override(v___x_1168_, v_alpha_1169_, v___x_1179_, v___x_1170_);
v___x_1181_ = 0;
v___x_1182_ = 1;
v___x_1183_ = 1;
v___x_1184_ = l_Lean_Meta_mkForallFVars(v_xs_1171_, v___x_1180_, v___x_1181_, v___x_1182_, v___x_1182_, v___x_1183_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed(lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v_alpha_1187_, lean_object* v___x_1188_, lean_object* v_xs_1189_, lean_object* v_x_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v___x_15863__boxed_1196_; lean_object* v_res_1197_; 
v___x_15863__boxed_1196_ = lean_unbox(v___x_1188_);
v_res_1197_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(v___x_1185_, v___x_1186_, v_alpha_1187_, v___x_15863__boxed_1196_, v_xs_1189_, v_x_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec_ref(v_x_1190_);
lean_dec_ref(v_xs_1189_);
lean_dec(v___x_1185_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(lean_object* v___x_1204_, lean_object* v___x_1205_, lean_object* v_rel_1206_, lean_object* v___x_1207_, lean_object* v_beta_1208_, uint8_t v___x_1209_, lean_object* v_alpha_1210_, uint8_t v___x_1211_, lean_object* v_xs_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1219_ = l_Lean_mkAppN(v___x_1204_, v_xs_1212_);
v___x_1220_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1221_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_xs_1212_);
v___x_1222_ = lean_array_push(v_xs_1212_, v___x_1205_);
v___x_1223_ = l_Lean_mkAppN(v_rel_1206_, v___x_1222_);
lean_dec_ref(v___x_1222_);
v___x_1224_ = l_Lean_Expr_bvar___override(v___x_1207_);
v___x_1225_ = l_Lean_Expr_app___override(v_beta_1208_, v___x_1224_);
v___x_1226_ = l_Lean_Expr_forallE___override(v___x_1221_, v___x_1223_, v___x_1225_, v___x_1209_);
v___x_1227_ = l_Lean_Expr_forallE___override(v___x_1220_, v_alpha_1210_, v___x_1226_, v___x_1209_);
v___x_1228_ = l_Lean_mkArrow(v___x_1227_, v___x_1219_, v___y_1216_, v___y_1217_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; uint8_t v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1230_ = 1;
v___x_1231_ = 1;
v___x_1232_ = l_Lean_Meta_mkLambdaFVars(v_xs_1212_, v_a_1229_, v___x_1211_, v___x_1230_, v___x_1211_, v___x_1230_, v___x_1231_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec_ref(v_xs_1212_);
return v___x_1232_;
}
else
{
lean_dec_ref(v_xs_1212_);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed(lean_object* v___x_1233_, lean_object* v___x_1234_, lean_object* v_rel_1235_, lean_object* v___x_1236_, lean_object* v_beta_1237_, lean_object* v___x_1238_, lean_object* v_alpha_1239_, lean_object* v___x_1240_, lean_object* v_xs_1241_, lean_object* v_x_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
uint8_t v___x_15917__boxed_1248_; uint8_t v___x_15918__boxed_1249_; lean_object* v_res_1250_; 
v___x_15917__boxed_1248_ = lean_unbox(v___x_1238_);
v___x_15918__boxed_1249_ = lean_unbox(v___x_1240_);
v_res_1250_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(v___x_1233_, v___x_1234_, v_rel_1235_, v___x_1236_, v_beta_1237_, v___x_15917__boxed_1248_, v_alpha_1239_, v___x_15918__boxed_1249_, v_xs_1241_, v_x_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v_x_1242_);
return v_res_1250_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1));
v___x_1254_ = lean_unsigned_to_nat(10u);
v___x_1255_ = lean_unsigned_to_nat(146u);
v___x_1256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0));
v___x_1257_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_1258_ = l_mkPanicMessageWithDecl(v___x_1257_, v___x_1256_, v___x_1255_, v___x_1254_, v___x_1253_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(lean_object* v___f_1259_, uint8_t v___x_1260_, lean_object* v_a_1261_, uint8_t v___x_1262_, lean_object* v_ys_1263_, lean_object* v_altBodyType_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
uint8_t v___x_1270_; 
v___x_1270_ = l_Lean_Expr_isForall(v_altBodyType_1264_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec_ref(v_ys_1263_);
lean_dec_ref(v_a_1261_);
lean_dec_ref(v___f_1259_);
v___x_1271_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2);
v___x_1272_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v___x_1271_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = l_Lean_Expr_bindingDomain_x21(v_altBodyType_1264_);
v___x_1274_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_1275_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_1273_, v___x_1274_, v___f_1259_, v___x_1260_, v___x_1260_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1275_, 1);
lean_inc_ref(v_ys_1263_);
v___x_1277_ = lean_array_push(v_ys_1263_, v_a_1276_);
v___x_1278_ = l_Lean_mkAppN(v_a_1261_, v___x_1277_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = 1;
v___x_1280_ = l_Lean_Meta_mkLambdaFVars(v_ys_1263_, v___x_1278_, v___x_1260_, v___x_1262_, v___x_1260_, v___x_1262_, v___x_1279_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec_ref(v_ys_1263_);
return v___x_1280_;
}
else
{
lean_dec_ref(v_ys_1263_);
lean_dec_ref(v_a_1261_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed(lean_object* v___f_1281_, lean_object* v___x_1282_, lean_object* v_a_1283_, lean_object* v___x_1284_, lean_object* v_ys_1285_, lean_object* v_altBodyType_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
uint8_t v___x_16002__boxed_1292_; uint8_t v___x_16003__boxed_1293_; lean_object* v_res_1294_; 
v___x_16002__boxed_1292_ = lean_unbox(v___x_1282_);
v___x_16003__boxed_1293_ = lean_unbox(v___x_1284_);
v_res_1294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(v___f_1281_, v___x_16002__boxed_1292_, v_a_1283_, v___x_16003__boxed_1293_, v_ys_1285_, v_altBodyType_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec_ref(v_altBodyType_1286_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v_f_1297_, uint8_t v___x_1298_, uint8_t v___x_1299_, lean_object* v_ys_1300_, lean_object* v_x_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1307_ = lean_array_get_borrowed(v___x_1295_, v_ys_1300_, v___x_1296_);
lean_inc(v___x_1307_);
v___x_1308_ = l_Lean_Expr_app___override(v_f_1297_, v___x_1307_);
v___x_1309_ = 1;
v___x_1310_ = l_Lean_Meta_mkLambdaFVars(v_ys_1300_, v___x_1308_, v___x_1298_, v___x_1299_, v___x_1298_, v___x_1299_, v___x_1309_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed(lean_object* v___x_1311_, lean_object* v___x_1312_, lean_object* v_f_1313_, lean_object* v___x_1314_, lean_object* v___x_1315_, lean_object* v_ys_1316_, lean_object* v_x_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v___x_16058__boxed_1323_; uint8_t v___x_16059__boxed_1324_; lean_object* v_res_1325_; 
v___x_16058__boxed_1323_ = lean_unbox(v___x_1314_);
v___x_16059__boxed_1324_ = lean_unbox(v___x_1315_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(v___x_1311_, v___x_1312_, v_f_1313_, v___x_16058__boxed_1323_, v___x_16059__boxed_1324_, v_ys_1316_, v_x_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v_x_1317_);
lean_dec_ref(v_ys_1316_);
lean_dec(v___x_1312_);
lean_dec_ref(v___x_1311_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(lean_object* v_f_1326_, lean_object* v_as_1327_, size_t v_sz_1328_, size_t v_i_1329_, lean_object* v_b_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_usize_dec_lt(v_i_1329_, v_sz_1328_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_dec_ref(v_f_1326_);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_b_1330_);
return v___x_1337_;
}
else
{
lean_object* v_snd_1338_; lean_object* v_fst_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1402_; 
v_snd_1338_ = lean_ctor_get(v_b_1330_, 1);
v_fst_1339_ = lean_ctor_get(v_b_1330_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_b_1330_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1341_ = v_b_1330_;
v_isShared_1342_ = v_isSharedCheck_1402_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_snd_1338_);
lean_inc(v_fst_1339_);
lean_dec(v_b_1330_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1402_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_array_1343_; lean_object* v_start_1344_; lean_object* v_stop_1345_; uint8_t v___x_1346_; 
v_array_1343_ = lean_ctor_get(v_snd_1338_, 0);
v_start_1344_ = lean_ctor_get(v_snd_1338_, 1);
v_stop_1345_ = lean_ctor_get(v_snd_1338_, 2);
v___x_1346_ = lean_nat_dec_lt(v_start_1344_, v_stop_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1348_; 
lean_dec_ref(v_f_1326_);
if (v_isShared_1342_ == 0)
{
v___x_1348_ = v___x_1341_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_fst_1339_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_snd_1338_);
v___x_1348_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
else
{
lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1398_; 
lean_inc(v_stop_1345_);
lean_inc(v_start_1344_);
lean_inc_ref(v_array_1343_);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_snd_1338_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; lean_object* v_unused_1400_; lean_object* v_unused_1401_; 
v_unused_1399_ = lean_ctor_get(v_snd_1338_, 2);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_snd_1338_, 1);
lean_dec(v_unused_1400_);
v_unused_1401_ = lean_ctor_get(v_snd_1338_, 0);
lean_dec(v_unused_1401_);
v___x_1352_ = v_snd_1338_;
v_isShared_1353_ = v_isSharedCheck_1398_;
goto v_resetjp_1351_;
}
else
{
lean_dec(v_snd_1338_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1398_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_a_1354_; lean_object* v___x_1355_; 
v_a_1354_ = lean_array_uget_borrowed(v_as_1327_, v_i_1329_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v_a_1354_);
v___x_1355_ = lean_infer_type(v_a_1354_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___f_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = l_Lean_instInhabitedExpr;
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = 0;
v___x_1360_ = lean_box(v___x_1359_);
v___x_1361_ = lean_box(v___x_1346_);
lean_inc_ref(v_f_1326_);
v___f_1362_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1362_, 0, v___x_1357_);
lean_closure_set(v___f_1362_, 1, v___x_1358_);
lean_closure_set(v___f_1362_, 2, v_f_1326_);
lean_closure_set(v___f_1362_, 3, v___x_1360_);
lean_closure_set(v___f_1362_, 4, v___x_1361_);
v___x_1363_ = lean_box(v___x_1359_);
v___x_1364_ = lean_box(v___x_1346_);
lean_inc(v_a_1354_);
v___f_1365_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1365_, 0, v___f_1362_);
lean_closure_set(v___f_1365_, 1, v___x_1363_);
lean_closure_set(v___f_1365_, 2, v_a_1354_);
lean_closure_set(v___f_1365_, 3, v___x_1364_);
v___x_1366_ = lean_array_fget_borrowed(v_array_1343_, v_start_1344_);
lean_inc(v___x_1366_);
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
v___x_1368_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1356_, v___x_1367_, v___f_1365_, v___x_1359_, v___x_1359_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_add(v_start_1344_, v___x_1370_);
lean_dec(v_start_1344_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v___x_1371_);
v___x_1373_ = v___x_1352_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_array_1343_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1381_, 2, v_stop_1345_);
v___x_1373_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = l_Lean_Expr_app___override(v_fst_1339_, v_a_1369_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1373_);
lean_ctor_set(v___x_1341_, 0, v___x_1374_);
v___x_1376_ = v___x_1341_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1373_);
v___x_1376_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
size_t v___x_1377_; size_t v___x_1378_; 
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_add(v_i_1329_, v___x_1377_);
v_i_1329_ = v___x_1378_;
v_b_1330_ = v___x_1376_;
goto _start;
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_del_object(v___x_1352_);
lean_dec(v_stop_1345_);
lean_dec(v_start_1344_);
lean_dec_ref(v_array_1343_);
lean_del_object(v___x_1341_);
lean_dec(v_fst_1339_);
lean_dec_ref(v_f_1326_);
v_a_1382_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1368_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1368_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_del_object(v___x_1352_);
lean_dec(v_stop_1345_);
lean_dec(v_start_1344_);
lean_dec_ref(v_array_1343_);
lean_del_object(v___x_1341_);
lean_dec(v_fst_1339_);
lean_dec_ref(v_f_1326_);
v_a_1390_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1355_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1355_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___boxed(lean_object* v_f_1403_, lean_object* v_as_1404_, lean_object* v_sz_1405_, lean_object* v_i_1406_, lean_object* v_b_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
size_t v_sz_boxed_1413_; size_t v_i_boxed_1414_; lean_object* v_res_1415_; 
v_sz_boxed_1413_ = lean_unbox_usize(v_sz_1405_);
lean_dec(v_sz_1405_);
v_i_boxed_1414_ = lean_unbox_usize(v_i_1406_);
lean_dec(v_i_1406_);
v_res_1415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1403_, v_as_1404_, v_sz_boxed_1413_, v_i_boxed_1414_, v_b_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec_ref(v_as_1404_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(lean_object* v_as_x27_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
if (lean_obj_tag(v_as_x27_1416_) == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_b_1417_);
return v___x_1423_;
}
else
{
lean_object* v_head_1424_; lean_object* v_tail_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; 
v_head_1424_ = lean_ctor_get(v_as_x27_1416_, 0);
v_tail_1425_ = lean_ctor_get(v_as_x27_1416_, 1);
v___x_1426_ = 1;
lean_inc(v_head_1424_);
v___x_1427_ = l_Lean_MVarId_refl(v_head_1424_, v___x_1426_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v___x_1428_; 
lean_dec_ref_known(v___x_1427_, 1);
v___x_1428_ = lean_box(0);
v_as_x27_1416_ = v_tail_1425_;
v_b_1417_ = v___x_1428_;
goto _start;
}
else
{
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg___boxed(lean_object* v_as_x27_1430_, lean_object* v_b_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_1430_, v_b_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v_as_x27_1430_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(lean_object* v___x_1438_, lean_object* v_matcherInfo_1439_, lean_object* v___x_1440_, lean_object* v___x_1441_, lean_object* v_f_1442_, lean_object* v_discrs_1443_, lean_object* v___x_1444_, lean_object* v_rel_1445_, lean_object* v___x_1446_, uint8_t v___x_1447_, lean_object* v_alpha_1448_, lean_object* v___x_1449_, lean_object* v_beta_1450_, lean_object* v___x_1451_, uint8_t v___x_1452_, lean_object* v___x_1453_, lean_object* v___x_1454_, lean_object* v___x_1455_, lean_object* v_alts_1456_, lean_object* v_x_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; size_t v_sz_1468_; size_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1463_ = l_Lean_mkAppN(v___x_1438_, v_alts_1456_);
lean_inc_ref(v_matcherInfo_1439_);
v___x_1464_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_matcherInfo_1439_);
v___x_1465_ = lean_array_get_size(v___x_1464_);
v___x_1466_ = l_Array_toSubarray___redArg(v___x_1464_, v___x_1440_, v___x_1465_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1441_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v_sz_1468_ = lean_array_size(v_alts_1456_);
v___x_1469_ = ((size_t)0ULL);
lean_inc_ref(v_f_1442_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1442_, v_alts_1456_, v_sz_1468_, v___x_1469_, v___x_1467_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v_fst_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1566_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v_fst_1472_ = lean_ctor_get(v_a_1471_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_a_1471_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; 
v_unused_1567_ = lean_ctor_get(v_a_1471_, 1);
lean_dec(v_unused_1567_);
v___x_1474_ = v_a_1471_;
v_isShared_1475_ = v_isSharedCheck_1566_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_fst_1472_);
lean_dec(v_a_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1566_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1476_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1477_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_discrs_1443_);
v___x_1478_ = lean_array_push(v_discrs_1443_, v___x_1444_);
lean_inc_ref(v_rel_1445_);
v___x_1479_ = l_Lean_mkAppN(v_rel_1445_, v___x_1478_);
lean_dec_ref(v___x_1478_);
v___x_1480_ = l_Lean_Expr_bvar___override(v___x_1446_);
lean_inc_ref(v_f_1442_);
v___x_1481_ = l_Lean_Expr_app___override(v_f_1442_, v___x_1480_);
v___x_1482_ = l_Lean_Expr_lam___override(v___x_1477_, v___x_1479_, v___x_1481_, v___x_1447_);
lean_inc_ref(v_alpha_1448_);
v___x_1483_ = l_Lean_Expr_lam___override(v___x_1476_, v_alpha_1448_, v___x_1482_, v___x_1447_);
v___x_1484_ = l_Lean_Expr_app___override(v___x_1463_, v___x_1483_);
lean_inc(v_fst_1472_);
v___x_1485_ = l_Lean_Meta_mkEq(v___x_1484_, v_fst_1472_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc_n(v_a_1486_, 2);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1487_ = lean_box(0);
v___x_1488_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1486_, v___x_1487_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1490_ = l_Lean_Expr_mvarId_x21(v_a_1489_);
v___x_1491_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v___x_1490_, v_fst_1472_, v_matcherInfo_1439_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec_ref(v_matcherInfo_1439_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1493_ = lean_box(0);
v___x_1494_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_a_1492_, v___x_1493_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec(v_a_1492_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v___x_1495_; lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref_known(v___x_1494_, 1);
v___x_1495_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_1489_, v___y_1459_);
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1541_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1541_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1500_ = lean_unsigned_to_nat(5u);
v___x_1501_ = lean_mk_empty_array_with_capacity(v___x_1500_);
v___x_1502_ = lean_array_push(v___x_1501_, v___x_1449_);
v___x_1503_ = lean_array_push(v___x_1502_, v_alpha_1448_);
v___x_1504_ = lean_array_push(v___x_1503_, v_beta_1450_);
v___x_1505_ = lean_array_push(v___x_1504_, v_f_1442_);
v___x_1506_ = lean_array_push(v___x_1505_, v_rel_1445_);
v___x_1507_ = l_Array_append___redArg(v___x_1451_, v___x_1506_);
lean_dec_ref(v___x_1506_);
v___x_1508_ = l_Array_append___redArg(v___x_1507_, v_discrs_1443_);
lean_dec_ref(v_discrs_1443_);
v___x_1509_ = l_Array_append___redArg(v___x_1508_, v_alts_1456_);
v___x_1510_ = 1;
v___x_1511_ = 1;
v___x_1512_ = l_Lean_Meta_mkForallFVars(v___x_1509_, v_a_1486_, v___x_1452_, v___x_1510_, v___x_1510_, v___x_1511_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = l_Lean_Meta_mkLambdaFVars(v___x_1509_, v_a_1496_, v___x_1452_, v___x_1510_, v___x_1452_, v___x_1510_, v___x_1511_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec_ref(v___x_1509_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
lean_inc(v___x_1453_);
v___x_1516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1453_);
lean_ctor_set(v___x_1516_, 1, v___x_1454_);
lean_ctor_set(v___x_1516_, 2, v_a_1513_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set_tag(v___x_1474_, 1);
lean_ctor_set(v___x_1474_, 1, v___x_1455_);
lean_ctor_set(v___x_1474_, 0, v___x_1453_);
v___x_1518_ = v___x_1474_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1455_);
v___x_1518_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1516_);
lean_ctor_set(v___x_1519_, 1, v_a_1515_);
lean_ctor_set(v___x_1519_, 2, v___x_1518_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set_tag(v___x_1498_, 2);
lean_ctor_set(v___x_1498_, 0, v___x_1519_);
v___x_1521_ = v___x_1498_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_addDecl(v___x_1521_, v___x_1452_, v___y_1460_, v___y_1461_);
return v___x_1522_;
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_a_1513_);
lean_del_object(v___x_1498_);
lean_del_object(v___x_1474_);
lean_dec(v___x_1455_);
lean_dec(v___x_1454_);
lean_dec(v___x_1453_);
v_a_1525_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1514_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1514_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v___x_1509_);
lean_del_object(v___x_1498_);
lean_dec(v_a_1496_);
lean_del_object(v___x_1474_);
lean_dec(v___x_1455_);
lean_dec(v___x_1454_);
lean_dec(v___x_1453_);
v_a_1533_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1512_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1512_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
else
{
lean_dec(v_a_1489_);
lean_dec(v_a_1486_);
lean_del_object(v___x_1474_);
lean_dec(v___x_1455_);
lean_dec(v___x_1454_);
lean_dec(v___x_1453_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_beta_1450_);
lean_dec_ref(v___x_1449_);
lean_dec_ref(v_alpha_1448_);
lean_dec_ref(v_rel_1445_);
lean_dec_ref(v_discrs_1443_);
lean_dec_ref(v_f_1442_);
return v___x_1494_;
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec(v_a_1489_);
lean_dec(v_a_1486_);
lean_del_object(v___x_1474_);
lean_dec(v___x_1455_);
lean_dec(v___x_1454_);
lean_dec(v___x_1453_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_beta_1450_);
lean_dec_ref(v___x_1449_);
lean_dec_ref(v_alpha_1448_);
lean_dec_ref(v_rel_1445_);
lean_dec_ref(v_discrs_1443_);
lean_dec_ref(v_f_1442_);
v_a_1542_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1491_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1491_);
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
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec(v_a_1486_);
lean_del_object(v___x_1474_);
lean_dec(v_fst_1472_);
lean_dec(v___x_1455_);
lean_dec(v___x_1454_);
lean_dec(v___x_1453_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_beta_1450_);
lean_dec_ref(v___x_1449_);
lean_dec_ref(v_alpha_1448_);
lean_dec_ref(v_rel_1445_);
lean_dec_ref(v_discrs_1443_);
lean_dec_ref(v_f_1442_);
lean_dec_ref(v_matcherInfo_1439_);
v_a_1550_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1488_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1488_);
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
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1474_);
lean_dec(v_fst_1472_);
lean_dec(v___x_1455_);
lean_dec(v___x_1454_);
lean_dec(v___x_1453_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_beta_1450_);
lean_dec_ref(v___x_1449_);
lean_dec_ref(v_alpha_1448_);
lean_dec_ref(v_rel_1445_);
lean_dec_ref(v_discrs_1443_);
lean_dec_ref(v_f_1442_);
lean_dec_ref(v_matcherInfo_1439_);
v_a_1558_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1485_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1485_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v___x_1463_);
lean_dec(v___x_1455_);
lean_dec(v___x_1454_);
lean_dec(v___x_1453_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_beta_1450_);
lean_dec_ref(v___x_1449_);
lean_dec_ref(v_alpha_1448_);
lean_dec(v___x_1446_);
lean_dec_ref(v_rel_1445_);
lean_dec_ref(v___x_1444_);
lean_dec_ref(v_discrs_1443_);
lean_dec_ref(v_f_1442_);
lean_dec_ref(v_matcherInfo_1439_);
v_a_1568_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1470_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1470_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed(lean_object** _args){
lean_object* v___x_1576_ = _args[0];
lean_object* v_matcherInfo_1577_ = _args[1];
lean_object* v___x_1578_ = _args[2];
lean_object* v___x_1579_ = _args[3];
lean_object* v_f_1580_ = _args[4];
lean_object* v_discrs_1581_ = _args[5];
lean_object* v___x_1582_ = _args[6];
lean_object* v_rel_1583_ = _args[7];
lean_object* v___x_1584_ = _args[8];
lean_object* v___x_1585_ = _args[9];
lean_object* v_alpha_1586_ = _args[10];
lean_object* v___x_1587_ = _args[11];
lean_object* v_beta_1588_ = _args[12];
lean_object* v___x_1589_ = _args[13];
lean_object* v___x_1590_ = _args[14];
lean_object* v___x_1591_ = _args[15];
lean_object* v___x_1592_ = _args[16];
lean_object* v___x_1593_ = _args[17];
lean_object* v_alts_1594_ = _args[18];
lean_object* v_x_1595_ = _args[19];
lean_object* v___y_1596_ = _args[20];
lean_object* v___y_1597_ = _args[21];
lean_object* v___y_1598_ = _args[22];
lean_object* v___y_1599_ = _args[23];
lean_object* v___y_1600_ = _args[24];
_start:
{
uint8_t v___x_16273__boxed_1601_; uint8_t v___x_16276__boxed_1602_; lean_object* v_res_1603_; 
v___x_16273__boxed_1601_ = lean_unbox(v___x_1585_);
v___x_16276__boxed_1602_ = lean_unbox(v___x_1590_);
v_res_1603_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(v___x_1576_, v_matcherInfo_1577_, v___x_1578_, v___x_1579_, v_f_1580_, v_discrs_1581_, v___x_1582_, v_rel_1583_, v___x_1584_, v___x_16273__boxed_1601_, v_alpha_1586_, v___x_1587_, v_beta_1588_, v___x_1589_, v___x_16276__boxed_1602_, v___x_1591_, v___x_1592_, v___x_1593_, v_alts_1594_, v_x_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec_ref(v_x_1595_);
lean_dec_ref(v_alts_1594_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(lean_object* v___x_1604_, lean_object* v___x_1605_, lean_object* v_matcherInfo_1606_, lean_object* v___x_1607_, lean_object* v_f_1608_, lean_object* v___x_1609_, lean_object* v_rel_1610_, lean_object* v___x_1611_, uint8_t v___x_1612_, lean_object* v_alpha_1613_, lean_object* v___x_1614_, lean_object* v_beta_1615_, lean_object* v___x_1616_, uint8_t v___x_1617_, lean_object* v___x_1618_, lean_object* v___x_1619_, lean_object* v___x_1620_, lean_object* v_discrs_1621_, lean_object* v_x_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = l_Lean_mkAppN(v___x_1604_, v_discrs_1621_);
lean_inc(v___y_1626_);
lean_inc_ref(v___y_1625_);
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc_ref(v___x_1628_);
v___x_1629_ = lean_infer_type(v___x_1628_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___f_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = l_Lean_mkAppN(v___x_1605_, v_discrs_1621_);
v___x_1632_ = lean_box(v___x_1612_);
v___x_1633_ = lean_box(v___x_1617_);
lean_inc_ref(v_matcherInfo_1606_);
v___f_1634_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1634_, 0, v___x_1628_);
lean_closure_set(v___f_1634_, 1, v_matcherInfo_1606_);
lean_closure_set(v___f_1634_, 2, v___x_1607_);
lean_closure_set(v___f_1634_, 3, v___x_1631_);
lean_closure_set(v___f_1634_, 4, v_f_1608_);
lean_closure_set(v___f_1634_, 5, v_discrs_1621_);
lean_closure_set(v___f_1634_, 6, v___x_1609_);
lean_closure_set(v___f_1634_, 7, v_rel_1610_);
lean_closure_set(v___f_1634_, 8, v___x_1611_);
lean_closure_set(v___f_1634_, 9, v___x_1632_);
lean_closure_set(v___f_1634_, 10, v_alpha_1613_);
lean_closure_set(v___f_1634_, 11, v___x_1614_);
lean_closure_set(v___f_1634_, 12, v_beta_1615_);
lean_closure_set(v___f_1634_, 13, v___x_1616_);
lean_closure_set(v___f_1634_, 14, v___x_1633_);
lean_closure_set(v___f_1634_, 15, v___x_1618_);
lean_closure_set(v___f_1634_, 16, v___x_1619_);
lean_closure_set(v___f_1634_, 17, v___x_1620_);
v___x_1635_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_matcherInfo_1606_);
lean_dec_ref(v_matcherInfo_1606_);
v___x_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
v___x_1637_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1630_, v___x_1636_, v___f_1634_, v___x_1617_, v___x_1617_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1637_;
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v___x_1628_);
lean_dec_ref(v_discrs_1621_);
lean_dec(v___x_1620_);
lean_dec(v___x_1619_);
lean_dec(v___x_1618_);
lean_dec_ref(v___x_1616_);
lean_dec_ref(v_beta_1615_);
lean_dec_ref(v___x_1614_);
lean_dec_ref(v_alpha_1613_);
lean_dec(v___x_1611_);
lean_dec_ref(v_rel_1610_);
lean_dec_ref(v___x_1609_);
lean_dec_ref(v_f_1608_);
lean_dec(v___x_1607_);
lean_dec_ref(v_matcherInfo_1606_);
lean_dec_ref(v___x_1605_);
v_a_1638_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1629_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1629_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed(lean_object** _args){
lean_object* v___x_1646_ = _args[0];
lean_object* v___x_1647_ = _args[1];
lean_object* v_matcherInfo_1648_ = _args[2];
lean_object* v___x_1649_ = _args[3];
lean_object* v_f_1650_ = _args[4];
lean_object* v___x_1651_ = _args[5];
lean_object* v_rel_1652_ = _args[6];
lean_object* v___x_1653_ = _args[7];
lean_object* v___x_1654_ = _args[8];
lean_object* v_alpha_1655_ = _args[9];
lean_object* v___x_1656_ = _args[10];
lean_object* v_beta_1657_ = _args[11];
lean_object* v___x_1658_ = _args[12];
lean_object* v___x_1659_ = _args[13];
lean_object* v___x_1660_ = _args[14];
lean_object* v___x_1661_ = _args[15];
lean_object* v___x_1662_ = _args[16];
lean_object* v_discrs_1663_ = _args[17];
lean_object* v_x_1664_ = _args[18];
lean_object* v___y_1665_ = _args[19];
lean_object* v___y_1666_ = _args[20];
lean_object* v___y_1667_ = _args[21];
lean_object* v___y_1668_ = _args[22];
lean_object* v___y_1669_ = _args[23];
_start:
{
uint8_t v___x_16554__boxed_1670_; uint8_t v___x_16557__boxed_1671_; lean_object* v_res_1672_; 
v___x_16554__boxed_1670_ = lean_unbox(v___x_1654_);
v___x_16557__boxed_1671_ = lean_unbox(v___x_1659_);
v_res_1672_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(v___x_1646_, v___x_1647_, v_matcherInfo_1648_, v___x_1649_, v_f_1650_, v___x_1651_, v_rel_1652_, v___x_1653_, v___x_16554__boxed_1670_, v_alpha_1655_, v___x_1656_, v_beta_1657_, v___x_1658_, v___x_16557__boxed_1671_, v___x_1660_, v___x_1661_, v___x_1662_, v_discrs_1663_, v_x_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec_ref(v_x_1664_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
if (lean_obj_tag(v_a_1673_) == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = l_List_reverse___redArg(v_a_1674_);
return v___x_1675_;
}
else
{
lean_object* v_head_1676_; lean_object* v_tail_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1686_; 
v_head_1676_ = lean_ctor_get(v_a_1673_, 0);
v_tail_1677_ = lean_ctor_get(v_a_1673_, 1);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_a_1673_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1679_ = v_a_1673_;
v_isShared_1680_ = v_isSharedCheck_1686_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_tail_1677_);
lean_inc(v_head_1676_);
lean_dec(v_a_1673_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1686_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = l_Lean_mkLevelParam(v_head_1676_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v_a_1674_);
lean_ctor_set(v___x_1679_, 0, v___x_1681_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_a_1674_);
v___x_1683_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
v_a_1673_ = v_tail_1677_;
v_a_1674_ = v___x_1683_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__0));
v___x_1689_ = l_Lean_stringToMessageData(v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__2));
v___x_1692_ = l_Lean_stringToMessageData(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(lean_object* v___x_1693_, lean_object* v___x_1694_, lean_object* v___x_1695_, lean_object* v_beta_1696_, uint8_t v___x_1697_, lean_object* v_alpha_1698_, uint8_t v___x_1699_, lean_object* v_numDiscrs_1700_, lean_object* v___f_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_levelParams_1704_, lean_object* v_matcherName_1705_, lean_object* v___x_1706_, lean_object* v_matcherInfo_1707_, lean_object* v___x_1708_, lean_object* v_f_1709_, lean_object* v___x_1710_, lean_object* v_uElimPos_x3f_1711_, lean_object* v_rel_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
lean_inc(v___y_1714_);
lean_inc_ref(v___y_1713_);
lean_inc_ref(v___x_1693_);
v___x_1718_ = lean_infer_type(v___x_1693_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___f_1722_; lean_object* v___x_1723_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = lean_box(v___x_1697_);
v___x_1721_ = lean_box(v___x_1699_);
lean_inc_ref(v_alpha_1698_);
lean_inc_ref(v_beta_1696_);
lean_inc(v___x_1695_);
lean_inc_ref(v_rel_1712_);
lean_inc_ref(v___x_1694_);
lean_inc_ref(v___x_1693_);
v___f_1722_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed), 15, 8);
lean_closure_set(v___f_1722_, 0, v___x_1693_);
lean_closure_set(v___f_1722_, 1, v___x_1694_);
lean_closure_set(v___f_1722_, 2, v_rel_1712_);
lean_closure_set(v___f_1722_, 3, v___x_1695_);
lean_closure_set(v___f_1722_, 4, v_beta_1696_);
lean_closure_set(v___f_1722_, 5, v___x_1720_);
lean_closure_set(v___f_1722_, 6, v_alpha_1698_);
lean_closure_set(v___f_1722_, 7, v___x_1721_);
v___x_1723_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1719_, v___f_1722_, v___x_1699_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc_n(v_a_1724_, 2);
lean_dec_ref_known(v___x_1723_, 1);
lean_inc(v_numDiscrs_1700_);
v___x_1725_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_a_1724_, v_numDiscrs_1700_, v___f_1701_, v___x_1699_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v_matcherLevels_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = lean_box(0);
v___x_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1728_, 0, v_a_1702_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1729_, 0, v_a_1703_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
lean_inc(v_levelParams_1704_);
v___x_1730_ = l_List_appendTR___redArg(v_levelParams_1704_, v___x_1729_);
v___x_1731_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_1704_, v___x_1727_);
if (lean_obj_tag(v_uElimPos_x3f_1711_) == 0)
{
uint8_t v___x_1760_; 
v___x_1760_ = l_Lean_Level_isZero(v_a_1726_);
lean_dec(v_a_1726_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec(v___x_1731_);
lean_dec(v___x_1730_);
lean_dec(v_a_1724_);
lean_dec_ref(v_rel_1712_);
lean_dec(v___x_1710_);
lean_dec_ref(v_f_1709_);
lean_dec(v___x_1708_);
lean_dec_ref(v_matcherInfo_1707_);
lean_dec_ref(v___x_1706_);
lean_dec(v_numDiscrs_1700_);
lean_dec_ref(v_alpha_1698_);
lean_dec_ref(v_beta_1696_);
lean_dec(v___x_1695_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1693_);
v___x_1761_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1);
v___x_1762_ = l_Lean_MessageData_ofConstName(v_matcherName_1705_, v___x_1699_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_1765_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1766_;
}
else
{
lean_inc(v___x_1731_);
v_matcherLevels_1733_ = v___x_1731_;
v___y_1734_ = v___y_1713_;
v___y_1735_ = v___y_1714_;
v___y_1736_ = v___y_1715_;
v___y_1737_ = v___y_1716_;
goto v___jp_1732_;
}
}
else
{
lean_object* v_val_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_val_1767_ = lean_ctor_get(v_uElimPos_x3f_1711_, 0);
lean_inc(v___x_1731_);
v___x_1768_ = lean_array_mk(v___x_1731_);
v___x_1769_ = lean_array_set(v___x_1768_, v_val_1767_, v_a_1726_);
v___x_1770_ = lean_array_to_list(v___x_1769_);
v_matcherLevels_1733_ = v___x_1770_;
v___y_1734_ = v___y_1713_;
v___y_1735_ = v___y_1714_;
v___y_1736_ = v___y_1715_;
v___y_1737_ = v___y_1716_;
goto v___jp_1732_;
}
v___jp_1732_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_inc(v_matcherName_1705_);
v___x_1738_ = l_Lean_Expr_const___override(v_matcherName_1705_, v_matcherLevels_1733_);
v___x_1739_ = l_Subarray_copy___redArg(v___x_1706_);
v___x_1740_ = l_Lean_mkAppN(v___x_1738_, v___x_1739_);
v___x_1741_ = l_Lean_Expr_app___override(v___x_1740_, v_a_1724_);
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1736_);
lean_inc(v___y_1735_);
lean_inc_ref(v___y_1734_);
lean_inc_ref(v___x_1741_);
v___x_1742_ = lean_infer_type(v___x_1741_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___f_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v___x_1744_ = l_Lean_Expr_const___override(v_matcherName_1705_, v___x_1731_);
v___x_1745_ = l_Lean_mkAppN(v___x_1744_, v___x_1739_);
lean_inc_ref(v___x_1693_);
v___x_1746_ = l_Lean_Expr_app___override(v___x_1745_, v___x_1693_);
v___x_1747_ = lean_box(v___x_1697_);
v___x_1748_ = lean_box(v___x_1699_);
v___f_1749_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed), 24, 17);
lean_closure_set(v___f_1749_, 0, v___x_1741_);
lean_closure_set(v___f_1749_, 1, v___x_1746_);
lean_closure_set(v___f_1749_, 2, v_matcherInfo_1707_);
lean_closure_set(v___f_1749_, 3, v___x_1708_);
lean_closure_set(v___f_1749_, 4, v_f_1709_);
lean_closure_set(v___f_1749_, 5, v___x_1694_);
lean_closure_set(v___f_1749_, 6, v_rel_1712_);
lean_closure_set(v___f_1749_, 7, v___x_1695_);
lean_closure_set(v___f_1749_, 8, v___x_1747_);
lean_closure_set(v___f_1749_, 9, v_alpha_1698_);
lean_closure_set(v___f_1749_, 10, v___x_1693_);
lean_closure_set(v___f_1749_, 11, v_beta_1696_);
lean_closure_set(v___f_1749_, 12, v___x_1739_);
lean_closure_set(v___f_1749_, 13, v___x_1748_);
lean_closure_set(v___f_1749_, 14, v___x_1710_);
lean_closure_set(v___f_1749_, 15, v___x_1730_);
lean_closure_set(v___f_1749_, 16, v___x_1727_);
v___x_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_numDiscrs_1700_);
v___x_1751_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1743_, v___x_1750_, v___f_1749_, v___x_1699_, v___x_1699_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
return v___x_1751_;
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v___x_1741_);
lean_dec_ref(v___x_1739_);
lean_dec(v___x_1731_);
lean_dec(v___x_1730_);
lean_dec_ref(v_rel_1712_);
lean_dec(v___x_1710_);
lean_dec_ref(v_f_1709_);
lean_dec(v___x_1708_);
lean_dec_ref(v_matcherInfo_1707_);
lean_dec(v_matcherName_1705_);
lean_dec(v_numDiscrs_1700_);
lean_dec_ref(v_alpha_1698_);
lean_dec_ref(v_beta_1696_);
lean_dec(v___x_1695_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1693_);
v_a_1752_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1742_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1742_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_a_1724_);
lean_dec_ref(v_rel_1712_);
lean_dec(v___x_1710_);
lean_dec_ref(v_f_1709_);
lean_dec(v___x_1708_);
lean_dec_ref(v_matcherInfo_1707_);
lean_dec_ref(v___x_1706_);
lean_dec(v_matcherName_1705_);
lean_dec(v_levelParams_1704_);
lean_dec(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec(v_numDiscrs_1700_);
lean_dec_ref(v_alpha_1698_);
lean_dec_ref(v_beta_1696_);
lean_dec(v___x_1695_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1693_);
v_a_1771_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1725_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1725_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v_rel_1712_);
lean_dec(v___x_1710_);
lean_dec_ref(v_f_1709_);
lean_dec(v___x_1708_);
lean_dec_ref(v_matcherInfo_1707_);
lean_dec_ref(v___x_1706_);
lean_dec(v_matcherName_1705_);
lean_dec(v_levelParams_1704_);
lean_dec(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v___f_1701_);
lean_dec(v_numDiscrs_1700_);
lean_dec_ref(v_alpha_1698_);
lean_dec_ref(v_beta_1696_);
lean_dec(v___x_1695_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1693_);
v_a_1779_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1723_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1723_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_rel_1712_);
lean_dec(v___x_1710_);
lean_dec_ref(v_f_1709_);
lean_dec(v___x_1708_);
lean_dec_ref(v_matcherInfo_1707_);
lean_dec_ref(v___x_1706_);
lean_dec(v_matcherName_1705_);
lean_dec(v_levelParams_1704_);
lean_dec(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v___f_1701_);
lean_dec(v_numDiscrs_1700_);
lean_dec_ref(v_alpha_1698_);
lean_dec_ref(v_beta_1696_);
lean_dec(v___x_1695_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___x_1693_);
v_a_1787_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1718_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1718_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed(lean_object** _args){
lean_object* v___x_1795_ = _args[0];
lean_object* v___x_1796_ = _args[1];
lean_object* v___x_1797_ = _args[2];
lean_object* v_beta_1798_ = _args[3];
lean_object* v___x_1799_ = _args[4];
lean_object* v_alpha_1800_ = _args[5];
lean_object* v___x_1801_ = _args[6];
lean_object* v_numDiscrs_1802_ = _args[7];
lean_object* v___f_1803_ = _args[8];
lean_object* v_a_1804_ = _args[9];
lean_object* v_a_1805_ = _args[10];
lean_object* v_levelParams_1806_ = _args[11];
lean_object* v_matcherName_1807_ = _args[12];
lean_object* v___x_1808_ = _args[13];
lean_object* v_matcherInfo_1809_ = _args[14];
lean_object* v___x_1810_ = _args[15];
lean_object* v_f_1811_ = _args[16];
lean_object* v___x_1812_ = _args[17];
lean_object* v_uElimPos_x3f_1813_ = _args[18];
lean_object* v_rel_1814_ = _args[19];
lean_object* v___y_1815_ = _args[20];
lean_object* v___y_1816_ = _args[21];
lean_object* v___y_1817_ = _args[22];
lean_object* v___y_1818_ = _args[23];
lean_object* v___y_1819_ = _args[24];
_start:
{
uint8_t v___x_16682__boxed_1820_; uint8_t v___x_16683__boxed_1821_; lean_object* v_res_1822_; 
v___x_16682__boxed_1820_ = lean_unbox(v___x_1799_);
v___x_16683__boxed_1821_ = lean_unbox(v___x_1801_);
v_res_1822_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(v___x_1795_, v___x_1796_, v___x_1797_, v_beta_1798_, v___x_16682__boxed_1820_, v_alpha_1800_, v___x_16683__boxed_1821_, v_numDiscrs_1802_, v___f_1803_, v_a_1804_, v_a_1805_, v_levelParams_1806_, v_matcherName_1807_, v___x_1808_, v_matcherInfo_1809_, v___x_1810_, v_f_1811_, v___x_1812_, v_uElimPos_x3f_1813_, v_rel_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v_uElimPos_x3f_1813_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(lean_object* v_k_1823_, lean_object* v_b_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; 
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
v___x_1830_ = lean_apply_6(v_k_1823_, v_b_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, lean_box(0));
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v_k_1831_, lean_object* v_b_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(v_k_1831_, v_b_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(lean_object* v_name_1839_, uint8_t v_bi_1840_, lean_object* v_type_1841_, lean_object* v_k_1842_, uint8_t v_kind_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___f_1849_; lean_object* v___x_1850_; 
v___f_1849_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1849_, 0, v_k_1842_);
v___x_1850_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1839_, v_bi_1840_, v_type_1841_, v___f_1849_, v_kind_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_a_1859_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1850_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1850_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
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
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___boxed(lean_object* v_name_1867_, lean_object* v_bi_1868_, lean_object* v_type_1869_, lean_object* v_k_1870_, lean_object* v_kind_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
uint8_t v_bi_boxed_1877_; uint8_t v_kind_boxed_1878_; lean_object* v_res_1879_; 
v_bi_boxed_1877_ = lean_unbox(v_bi_1868_);
v_kind_boxed_1878_ = lean_unbox(v_kind_1871_);
v_res_1879_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1867_, v_bi_boxed_1877_, v_type_1869_, v_k_1870_, v_kind_boxed_1878_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(lean_object* v_name_1880_, lean_object* v_type_1881_, lean_object* v_k_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
uint8_t v___x_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = 0;
v___x_1889_ = 0;
v___x_1890_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1880_, v___x_1888_, v_type_1881_, v_k_1882_, v___x_1889_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg___boxed(lean_object* v_name_1891_, lean_object* v_type_1892_, lean_object* v_k_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_1891_, v_type_1892_, v_k_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(lean_object* v___x_1903_, lean_object* v___f_1904_, lean_object* v___x_1905_, lean_object* v___x_1906_, lean_object* v_beta_1907_, uint8_t v___x_1908_, lean_object* v_alpha_1909_, lean_object* v_numDiscrs_1910_, lean_object* v___f_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_levelParams_1914_, lean_object* v_matcherName_1915_, lean_object* v___x_1916_, lean_object* v_matcherInfo_1917_, lean_object* v___x_1918_, lean_object* v___x_1919_, lean_object* v_uElimPos_x3f_1920_, lean_object* v_f_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; 
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
lean_inc(v___y_1923_);
lean_inc_ref(v___y_1922_);
lean_inc_ref(v___x_1903_);
v___x_1927_ = lean_infer_type(v___x_1903_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = 0;
v___x_1930_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1928_, v___f_1904_, v___x_1929_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1932_ = lean_box(v___x_1908_);
v___x_1933_ = lean_box(v___x_1929_);
v___f_1934_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed), 25, 19);
lean_closure_set(v___f_1934_, 0, v___x_1903_);
lean_closure_set(v___f_1934_, 1, v___x_1905_);
lean_closure_set(v___f_1934_, 2, v___x_1906_);
lean_closure_set(v___f_1934_, 3, v_beta_1907_);
lean_closure_set(v___f_1934_, 4, v___x_1932_);
lean_closure_set(v___f_1934_, 5, v_alpha_1909_);
lean_closure_set(v___f_1934_, 6, v___x_1933_);
lean_closure_set(v___f_1934_, 7, v_numDiscrs_1910_);
lean_closure_set(v___f_1934_, 8, v___f_1911_);
lean_closure_set(v___f_1934_, 9, v_a_1912_);
lean_closure_set(v___f_1934_, 10, v_a_1913_);
lean_closure_set(v___f_1934_, 11, v_levelParams_1914_);
lean_closure_set(v___f_1934_, 12, v_matcherName_1915_);
lean_closure_set(v___f_1934_, 13, v___x_1916_);
lean_closure_set(v___f_1934_, 14, v_matcherInfo_1917_);
lean_closure_set(v___f_1934_, 15, v___x_1918_);
lean_closure_set(v___f_1934_, 16, v_f_1921_);
lean_closure_set(v___f_1934_, 17, v___x_1919_);
lean_closure_set(v___f_1934_, 18, v_uElimPos_x3f_1920_);
v___x_1935_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__1));
v___x_1936_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_1935_, v_a_1931_, v___f_1934_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
return v___x_1936_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_f_1921_);
lean_dec(v_uElimPos_x3f_1920_);
lean_dec(v___x_1919_);
lean_dec(v___x_1918_);
lean_dec_ref(v_matcherInfo_1917_);
lean_dec_ref(v___x_1916_);
lean_dec(v_matcherName_1915_);
lean_dec(v_levelParams_1914_);
lean_dec(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v___f_1911_);
lean_dec(v_numDiscrs_1910_);
lean_dec_ref(v_alpha_1909_);
lean_dec_ref(v_beta_1907_);
lean_dec(v___x_1906_);
lean_dec_ref(v___x_1905_);
lean_dec_ref(v___x_1903_);
v_a_1937_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1930_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1930_);
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
lean_dec_ref(v_f_1921_);
lean_dec(v_uElimPos_x3f_1920_);
lean_dec(v___x_1919_);
lean_dec(v___x_1918_);
lean_dec_ref(v_matcherInfo_1917_);
lean_dec_ref(v___x_1916_);
lean_dec(v_matcherName_1915_);
lean_dec(v_levelParams_1914_);
lean_dec(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v___f_1911_);
lean_dec(v_numDiscrs_1910_);
lean_dec_ref(v_alpha_1909_);
lean_dec_ref(v_beta_1907_);
lean_dec(v___x_1906_);
lean_dec_ref(v___x_1905_);
lean_dec_ref(v___f_1904_);
lean_dec_ref(v___x_1903_);
v_a_1945_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1927_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1927_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed(lean_object** _args){
lean_object* v___x_1953_ = _args[0];
lean_object* v___f_1954_ = _args[1];
lean_object* v___x_1955_ = _args[2];
lean_object* v___x_1956_ = _args[3];
lean_object* v_beta_1957_ = _args[4];
lean_object* v___x_1958_ = _args[5];
lean_object* v_alpha_1959_ = _args[6];
lean_object* v_numDiscrs_1960_ = _args[7];
lean_object* v___f_1961_ = _args[8];
lean_object* v_a_1962_ = _args[9];
lean_object* v_a_1963_ = _args[10];
lean_object* v_levelParams_1964_ = _args[11];
lean_object* v_matcherName_1965_ = _args[12];
lean_object* v___x_1966_ = _args[13];
lean_object* v_matcherInfo_1967_ = _args[14];
lean_object* v___x_1968_ = _args[15];
lean_object* v___x_1969_ = _args[16];
lean_object* v_uElimPos_x3f_1970_ = _args[17];
lean_object* v_f_1971_ = _args[18];
lean_object* v___y_1972_ = _args[19];
lean_object* v___y_1973_ = _args[20];
lean_object* v___y_1974_ = _args[21];
lean_object* v___y_1975_ = _args[22];
lean_object* v___y_1976_ = _args[23];
_start:
{
uint8_t v___x_16986__boxed_1977_; lean_object* v_res_1978_; 
v___x_16986__boxed_1977_ = lean_unbox(v___x_1958_);
v_res_1978_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(v___x_1953_, v___f_1954_, v___x_1955_, v___x_1956_, v_beta_1957_, v___x_16986__boxed_1977_, v_alpha_1959_, v_numDiscrs_1960_, v___f_1961_, v_a_1962_, v_a_1963_, v_levelParams_1964_, v_matcherName_1965_, v___x_1966_, v_matcherInfo_1967_, v___x_1968_, v___x_1969_, v_uElimPos_x3f_1970_, v_f_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(lean_object* v___x_1985_, lean_object* v_alpha_1986_, lean_object* v___x_1987_, lean_object* v___x_1988_, lean_object* v_numDiscrs_1989_, lean_object* v___f_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_levelParams_1993_, lean_object* v_matcherName_1994_, lean_object* v___x_1995_, lean_object* v_matcherInfo_1996_, lean_object* v___x_1997_, lean_object* v_uElimPos_x3f_1998_, lean_object* v_beta_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v___f_2011_; lean_object* v___x_2012_; lean_object* v___f_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2005_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__1));
v___x_2006_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__3));
lean_inc_n(v___x_1985_, 2);
v___x_2007_ = l_Lean_Expr_bvar___override(v___x_1985_);
lean_inc_ref(v___x_2007_);
lean_inc_ref(v_beta_1999_);
v___x_2008_ = l_Lean_Expr_app___override(v_beta_1999_, v___x_2007_);
v___x_2009_ = 0;
v___x_2010_ = lean_box(v___x_2009_);
lean_inc_ref_n(v_alpha_1986_, 2);
v___f_2011_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2011_, 0, v___x_1985_);
lean_closure_set(v___f_2011_, 1, v___x_2006_);
lean_closure_set(v___f_2011_, 2, v_alpha_1986_);
lean_closure_set(v___f_2011_, 3, v___x_2010_);
v___x_2012_ = lean_box(v___x_2009_);
v___f_2013_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed), 24, 18);
lean_closure_set(v___f_2013_, 0, v___x_1987_);
lean_closure_set(v___f_2013_, 1, v___f_2011_);
lean_closure_set(v___f_2013_, 2, v___x_2007_);
lean_closure_set(v___f_2013_, 3, v___x_1988_);
lean_closure_set(v___f_2013_, 4, v_beta_1999_);
lean_closure_set(v___f_2013_, 5, v___x_2012_);
lean_closure_set(v___f_2013_, 6, v_alpha_1986_);
lean_closure_set(v___f_2013_, 7, v_numDiscrs_1989_);
lean_closure_set(v___f_2013_, 8, v___f_1990_);
lean_closure_set(v___f_2013_, 9, v_a_1991_);
lean_closure_set(v___f_2013_, 10, v_a_1992_);
lean_closure_set(v___f_2013_, 11, v_levelParams_1993_);
lean_closure_set(v___f_2013_, 12, v_matcherName_1994_);
lean_closure_set(v___f_2013_, 13, v___x_1995_);
lean_closure_set(v___f_2013_, 14, v_matcherInfo_1996_);
lean_closure_set(v___f_2013_, 15, v___x_1985_);
lean_closure_set(v___f_2013_, 16, v___x_1997_);
lean_closure_set(v___f_2013_, 17, v_uElimPos_x3f_1998_);
v___x_2014_ = l_Lean_Expr_forallE___override(v___x_2006_, v_alpha_1986_, v___x_2008_, v___x_2009_);
v___x_2015_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2005_, v___x_2014_, v___f_2013_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed(lean_object** _args){
lean_object* v___x_2016_ = _args[0];
lean_object* v_alpha_2017_ = _args[1];
lean_object* v___x_2018_ = _args[2];
lean_object* v___x_2019_ = _args[3];
lean_object* v_numDiscrs_2020_ = _args[4];
lean_object* v___f_2021_ = _args[5];
lean_object* v_a_2022_ = _args[6];
lean_object* v_a_2023_ = _args[7];
lean_object* v_levelParams_2024_ = _args[8];
lean_object* v_matcherName_2025_ = _args[9];
lean_object* v___x_2026_ = _args[10];
lean_object* v_matcherInfo_2027_ = _args[11];
lean_object* v___x_2028_ = _args[12];
lean_object* v_uElimPos_x3f_2029_ = _args[13];
lean_object* v_beta_2030_ = _args[14];
lean_object* v___y_2031_ = _args[15];
lean_object* v___y_2032_ = _args[16];
lean_object* v___y_2033_ = _args[17];
lean_object* v___y_2034_ = _args[18];
lean_object* v___y_2035_ = _args[19];
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(v___x_2016_, v_alpha_2017_, v___x_2018_, v___x_2019_, v_numDiscrs_2020_, v___f_2021_, v_a_2022_, v_a_2023_, v_levelParams_2024_, v_matcherName_2025_, v___x_2026_, v_matcherInfo_2027_, v___x_2028_, v_uElimPos_x3f_2029_, v_beta_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(lean_object* v_a_2040_, lean_object* v___x_2041_, lean_object* v___x_2042_, lean_object* v___x_2043_, lean_object* v_numDiscrs_2044_, lean_object* v___f_2045_, lean_object* v_a_2046_, lean_object* v_levelParams_2047_, lean_object* v_matcherName_2048_, lean_object* v___x_2049_, lean_object* v_matcherInfo_2050_, lean_object* v___x_2051_, lean_object* v_uElimPos_x3f_2052_, lean_object* v_alpha_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_inc(v_a_2040_);
v___x_2059_ = l_Lean_Level_param___override(v_a_2040_);
v___x_2060_ = l_Lean_Expr_sort___override(v___x_2059_);
lean_inc_ref(v_alpha_2053_);
v___x_2061_ = l_Lean_mkArrow(v_alpha_2053_, v___x_2060_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___f_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___f_2063_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed), 20, 14);
lean_closure_set(v___f_2063_, 0, v___x_2041_);
lean_closure_set(v___f_2063_, 1, v_alpha_2053_);
lean_closure_set(v___f_2063_, 2, v___x_2042_);
lean_closure_set(v___f_2063_, 3, v___x_2043_);
lean_closure_set(v___f_2063_, 4, v_numDiscrs_2044_);
lean_closure_set(v___f_2063_, 5, v___f_2045_);
lean_closure_set(v___f_2063_, 6, v_a_2040_);
lean_closure_set(v___f_2063_, 7, v_a_2046_);
lean_closure_set(v___f_2063_, 8, v_levelParams_2047_);
lean_closure_set(v___f_2063_, 9, v_matcherName_2048_);
lean_closure_set(v___f_2063_, 10, v___x_2049_);
lean_closure_set(v___f_2063_, 11, v_matcherInfo_2050_);
lean_closure_set(v___f_2063_, 12, v___x_2051_);
lean_closure_set(v___f_2063_, 13, v_uElimPos_x3f_2052_);
v___x_2064_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__1));
v___x_2065_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2064_, v_a_2062_, v___f_2063_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2065_;
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v_alpha_2053_);
lean_dec(v_uElimPos_x3f_2052_);
lean_dec(v___x_2051_);
lean_dec_ref(v_matcherInfo_2050_);
lean_dec_ref(v___x_2049_);
lean_dec(v_matcherName_2048_);
lean_dec(v_levelParams_2047_);
lean_dec(v_a_2046_);
lean_dec_ref(v___f_2045_);
lean_dec(v_numDiscrs_2044_);
lean_dec(v___x_2043_);
lean_dec_ref(v___x_2042_);
lean_dec(v___x_2041_);
lean_dec(v_a_2040_);
v_a_2066_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2061_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2061_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed(lean_object** _args){
lean_object* v_a_2074_ = _args[0];
lean_object* v___x_2075_ = _args[1];
lean_object* v___x_2076_ = _args[2];
lean_object* v___x_2077_ = _args[3];
lean_object* v_numDiscrs_2078_ = _args[4];
lean_object* v___f_2079_ = _args[5];
lean_object* v_a_2080_ = _args[6];
lean_object* v_levelParams_2081_ = _args[7];
lean_object* v_matcherName_2082_ = _args[8];
lean_object* v___x_2083_ = _args[9];
lean_object* v_matcherInfo_2084_ = _args[10];
lean_object* v___x_2085_ = _args[11];
lean_object* v_uElimPos_x3f_2086_ = _args[12];
lean_object* v_alpha_2087_ = _args[13];
lean_object* v___y_2088_ = _args[14];
lean_object* v___y_2089_ = _args[15];
lean_object* v___y_2090_ = _args[16];
lean_object* v___y_2091_ = _args[17];
lean_object* v___y_2092_ = _args[18];
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(v_a_2074_, v___x_2075_, v___x_2076_, v___x_2077_, v_numDiscrs_2078_, v___f_2079_, v_a_2080_, v_levelParams_2081_, v_matcherName_2082_, v___x_2083_, v_matcherInfo_2084_, v___x_2085_, v_uElimPos_x3f_2086_, v_alpha_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(lean_object* v_numParams_2103_, lean_object* v___x_2104_, lean_object* v___x_2105_, lean_object* v_numDiscrs_2106_, lean_object* v___f_2107_, lean_object* v_levelParams_2108_, lean_object* v_matcherName_2109_, lean_object* v_matcherInfo_2110_, lean_object* v___x_2111_, lean_object* v_uElimPos_x3f_2112_, lean_object* v_xs_2113_, lean_object* v_x_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__1));
v___x_2121_ = l_Lean_Core_mkFreshUserName(v___x_2120_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__3));
v___x_2124_ = l_Lean_Core_mkFreshUserName(v___x_2123_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2103_);
lean_inc_ref(v_xs_2113_);
v___x_2127_ = l_Array_toSubarray___redArg(v_xs_2113_, v___x_2126_, v_numParams_2103_);
v___x_2128_ = lean_array_get(v___x_2104_, v_xs_2113_, v_numParams_2103_);
lean_dec(v_numParams_2103_);
lean_dec_ref(v_xs_2113_);
lean_inc(v_a_2122_);
v___f_2129_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed), 19, 13);
lean_closure_set(v___f_2129_, 0, v_a_2125_);
lean_closure_set(v___f_2129_, 1, v___x_2126_);
lean_closure_set(v___f_2129_, 2, v___x_2128_);
lean_closure_set(v___f_2129_, 3, v___x_2105_);
lean_closure_set(v___f_2129_, 4, v_numDiscrs_2106_);
lean_closure_set(v___f_2129_, 5, v___f_2107_);
lean_closure_set(v___f_2129_, 6, v_a_2122_);
lean_closure_set(v___f_2129_, 7, v_levelParams_2108_);
lean_closure_set(v___f_2129_, 8, v_matcherName_2109_);
lean_closure_set(v___f_2129_, 9, v___x_2127_);
lean_closure_set(v___f_2129_, 10, v_matcherInfo_2110_);
lean_closure_set(v___f_2129_, 11, v___x_2111_);
lean_closure_set(v___f_2129_, 12, v_uElimPos_x3f_2112_);
v___x_2130_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__5));
v___x_2131_ = l_Lean_Level_param___override(v_a_2122_);
v___x_2132_ = l_Lean_Expr_sort___override(v___x_2131_);
v___x_2133_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2130_, v___x_2132_, v___f_2129_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2133_;
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_a_2122_);
lean_dec_ref(v_xs_2113_);
lean_dec(v_uElimPos_x3f_2112_);
lean_dec(v___x_2111_);
lean_dec_ref(v_matcherInfo_2110_);
lean_dec(v_matcherName_2109_);
lean_dec(v_levelParams_2108_);
lean_dec_ref(v___f_2107_);
lean_dec(v_numDiscrs_2106_);
lean_dec(v___x_2105_);
lean_dec(v_numParams_2103_);
v_a_2134_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2124_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2124_);
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
lean_dec_ref(v_xs_2113_);
lean_dec(v_uElimPos_x3f_2112_);
lean_dec(v___x_2111_);
lean_dec_ref(v_matcherInfo_2110_);
lean_dec(v_matcherName_2109_);
lean_dec(v_levelParams_2108_);
lean_dec_ref(v___f_2107_);
lean_dec(v_numDiscrs_2106_);
lean_dec(v___x_2105_);
lean_dec(v_numParams_2103_);
v_a_2142_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2121_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2121_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed(lean_object** _args){
lean_object* v_numParams_2150_ = _args[0];
lean_object* v___x_2151_ = _args[1];
lean_object* v___x_2152_ = _args[2];
lean_object* v_numDiscrs_2153_ = _args[3];
lean_object* v___f_2154_ = _args[4];
lean_object* v_levelParams_2155_ = _args[5];
lean_object* v_matcherName_2156_ = _args[6];
lean_object* v_matcherInfo_2157_ = _args[7];
lean_object* v___x_2158_ = _args[8];
lean_object* v_uElimPos_x3f_2159_ = _args[9];
lean_object* v_xs_2160_ = _args[10];
lean_object* v_x_2161_ = _args[11];
lean_object* v___y_2162_ = _args[12];
lean_object* v___y_2163_ = _args[13];
lean_object* v___y_2164_ = _args[14];
lean_object* v___y_2165_ = _args[15];
lean_object* v___y_2166_ = _args[16];
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(v_numParams_2150_, v___x_2151_, v___x_2152_, v_numDiscrs_2153_, v___f_2154_, v_levelParams_2155_, v_matcherName_2156_, v_matcherInfo_2157_, v___x_2158_, v_uElimPos_x3f_2159_, v_xs_2160_, v_x_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec_ref(v_x_2161_);
lean_dec_ref(v___x_2151_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(lean_object* v_ref_2168_, lean_object* v_msg_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_toCold_2175_; lean_object* v_currRecDepth_2176_; lean_object* v_ref_2177_; uint8_t v_diag_2178_; uint8_t v_suppressElabErrors_2179_; lean_object* v_ref_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_toCold_2175_ = lean_ctor_get(v___y_2172_, 0);
v_currRecDepth_2176_ = lean_ctor_get(v___y_2172_, 1);
v_ref_2177_ = lean_ctor_get(v___y_2172_, 2);
v_diag_2178_ = lean_ctor_get_uint8(v___y_2172_, sizeof(void*)*3);
v_suppressElabErrors_2179_ = lean_ctor_get_uint8(v___y_2172_, sizeof(void*)*3 + 1);
v_ref_2180_ = l_Lean_replaceRef(v_ref_2168_, v_ref_2177_);
lean_inc(v_currRecDepth_2176_);
lean_inc_ref(v_toCold_2175_);
v___x_2181_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2181_, 0, v_toCold_2175_);
lean_ctor_set(v___x_2181_, 1, v_currRecDepth_2176_);
lean_ctor_set(v___x_2181_, 2, v_ref_2180_);
lean_ctor_set_uint8(v___x_2181_, sizeof(void*)*3, v_diag_2178_);
lean_ctor_set_uint8(v___x_2181_, sizeof(void*)*3 + 1, v_suppressElabErrors_2179_);
v___x_2182_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_2169_, v___y_2170_, v___y_2171_, v___x_2181_, v___y_2173_);
lean_dec_ref_known(v___x_2181_, 3);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2183_, lean_object* v_msg_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2183_, v_msg_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v_ref_2183_);
return v_res_2190_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
lean_ctor_set(v___x_2196_, 2, v___x_2195_);
lean_ctor_set(v___x_2196_, 3, v___x_2195_);
lean_ctor_set(v___x_2196_, 4, v___x_2194_);
lean_ctor_set(v___x_2196_, 5, v___x_2194_);
lean_ctor_set(v___x_2196_, 6, v___x_2194_);
lean_ctor_set(v___x_2196_, 7, v___x_2194_);
lean_ctor_set(v___x_2196_, 8, v___x_2194_);
lean_ctor_set(v___x_2196_, 9, v___x_2194_);
lean_ctor_set(v___x_2196_, 10, v___x_2194_);
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_unsigned_to_nat(32u);
v___x_2198_ = lean_mk_empty_array_with_capacity(v___x_2197_);
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2200_ = ((size_t)5ULL);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = lean_unsigned_to_nat(32u);
v___x_2203_ = lean_mk_empty_array_with_capacity(v___x_2202_);
v___x_2204_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3);
v___x_2205_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v___x_2203_);
lean_ctor_set(v___x_2205_, 2, v___x_2201_);
lean_ctor_set(v___x_2205_, 3, v___x_2201_);
lean_ctor_set_usize(v___x_2205_, 4, v___x_2200_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = lean_box(1);
v___x_2207_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4);
v___x_2208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2207_);
lean_ctor_set(v___x_2209_, 2, v___x_2206_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__6));
v___x_2212_ = l_Lean_stringToMessageData(v___x_2211_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__8));
v___x_2215_ = l_Lean_stringToMessageData(v___x_2214_);
return v___x_2215_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__10));
v___x_2218_ = l_Lean_stringToMessageData(v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__12));
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__14));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16));
v___x_2227_ = l_Lean_stringToMessageData(v___x_2226_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18));
v___x_2230_ = l_Lean_stringToMessageData(v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2231_, lean_object* v_declHint_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; lean_object* v_env_2236_; uint8_t v___x_2237_; 
v___x_2235_ = lean_st_ref_get(v___y_2233_);
v_env_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc_ref(v_env_2236_);
lean_dec(v___x_2235_);
v___x_2237_ = l_Lean_Name_isAnonymous(v_declHint_2232_);
if (v___x_2237_ == 0)
{
uint8_t v_isExporting_2238_; 
v_isExporting_2238_ = lean_ctor_get_uint8(v_env_2236_, sizeof(void*)*8);
if (v_isExporting_2238_ == 0)
{
lean_object* v___x_2239_; 
lean_dec_ref(v_env_2236_);
lean_dec(v_declHint_2232_);
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v_msg_2231_);
return v___x_2239_;
}
else
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
lean_inc_ref(v_env_2236_);
v___x_2240_ = l_Lean_Environment_setExporting(v_env_2236_, v___x_2237_);
lean_inc(v_declHint_2232_);
lean_inc_ref(v___x_2240_);
v___x_2241_ = l_Lean_Environment_contains(v___x_2240_, v_declHint_2232_, v_isExporting_2238_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_dec_ref(v___x_2240_);
lean_dec_ref(v_env_2236_);
lean_dec(v_declHint_2232_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v_msg_2231_);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v_c_2248_; lean_object* v___x_2249_; 
v___x_2243_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2244_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2245_ = l_Lean_Options_empty;
v___x_2246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2240_);
lean_ctor_set(v___x_2246_, 1, v___x_2243_);
lean_ctor_set(v___x_2246_, 2, v___x_2244_);
lean_ctor_set(v___x_2246_, 3, v___x_2245_);
lean_inc(v_declHint_2232_);
v___x_2247_ = l_Lean_MessageData_ofConstName(v_declHint_2232_, v___x_2237_);
v_c_2248_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2248_, 0, v___x_2246_);
lean_ctor_set(v_c_2248_, 1, v___x_2247_);
v___x_2249_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2236_, v_declHint_2232_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec_ref(v_env_2236_);
lean_dec(v_declHint_2232_);
v___x_2250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set(v___x_2251_, 1, v_c_2248_);
v___x_2252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = l_Lean_MessageData_note(v___x_2253_);
v___x_2255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2255_, 0, v_msg_2231_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
else
{
lean_object* v_val_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2292_; 
v_val_2257_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2259_ = v___x_2249_;
v_isShared_2260_ = v_isSharedCheck_2292_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_val_2257_);
lean_dec(v___x_2249_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2292_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v_mod_2264_; uint8_t v___x_2265_; 
v___x_2261_ = lean_box(0);
v___x_2262_ = l_Lean_Environment_header(v_env_2236_);
lean_dec_ref(v_env_2236_);
v___x_2263_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2262_);
v_mod_2264_ = lean_array_get(v___x_2261_, v___x_2263_, v_val_2257_);
lean_dec(v_val_2257_);
lean_dec_ref(v___x_2263_);
v___x_2265_ = l_Lean_isPrivateName(v_declHint_2232_);
lean_dec(v_declHint_2232_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2266_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v_c_2248_);
v___x_2268_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = l_Lean_MessageData_ofName(v_mod_2264_);
v___x_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = l_Lean_MessageData_note(v___x_2273_);
v___x_2275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2275_, 0, v_msg_2231_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2275_);
v___x_2277_ = v___x_2259_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2279_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v_c_2248_);
v___x_2281_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = l_Lean_MessageData_ofName(v_mod_2264_);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = l_Lean_MessageData_note(v___x_2286_);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v_msg_2231_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2288_);
v___x_2290_ = v___x_2259_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2293_; 
lean_dec_ref(v_env_2236_);
lean_dec(v_declHint_2232_);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v_msg_2231_);
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2294_, lean_object* v_declHint_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2294_, v_declHint_2295_, v___y_2296_);
lean_dec(v___y_2296_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(lean_object* v_msg_2299_, lean_object* v_declHint_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2316_; 
v___x_2306_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2299_, v_declHint_2300_, v___y_2304_);
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2311_ = l_Lean_unknownIdentifierMessageTag;
v___x_2312_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v_a_2307_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2312_);
v___x_2314_ = v___x_2309_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11___boxed(lean_object* v_msg_2317_, lean_object* v_declHint_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2317_, v_declHint_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_ref_2325_, lean_object* v_msg_2326_, lean_object* v_declHint_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; lean_object* v_a_2334_; lean_object* v___x_2335_; 
v___x_2333_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2326_, v_declHint_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v___x_2333_);
v___x_2335_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2325_, v_a_2334_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_ref_2336_, lean_object* v_msg_2337_, lean_object* v_declHint_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2336_, v_msg_2337_, v_declHint_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v_ref_2336_);
return v_res_2344_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_2347_ = l_Lean_stringToMessageData(v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_2350_ = l_Lean_stringToMessageData(v___x_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_2351_, lean_object* v_constName_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2358_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_2359_ = 0;
lean_inc(v_constName_2352_);
v___x_2360_ = l_Lean_MessageData_ofConstName(v_constName_2352_, v___x_2359_);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2358_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2351_, v___x_2363_, v_constName_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_2365_, lean_object* v_constName_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2365_, v_constName_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v_ref_2365_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(lean_object* v_constName_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_ref_2379_; lean_object* v___x_2380_; 
v_ref_2379_ = lean_ctor_get(v___y_2376_, 2);
v___x_2380_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2379_, v_constName_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(lean_object* v_constName_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v_env_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; 
v___x_2394_ = lean_st_ref_get(v___y_2392_);
v_env_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc_ref(v_env_2395_);
lean_dec(v___x_2394_);
v___x_2396_ = 0;
lean_inc(v_constName_2388_);
v___x_2397_ = l_Lean_Environment_findConstVal_x3f(v_env_2395_, v_constName_2388_, v___x_2396_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
return v___x_2398_;
}
else
{
lean_object* v_val_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v_constName_2388_);
v_val_2399_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2397_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_val_2399_);
lean_dec(v___x_2397_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
lean_ctor_set_tag(v___x_2401_, 0);
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_val_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0___boxed(lean_object* v_constName_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_constName_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(lean_object* v_matcherName_2414_, lean_object* v_matcherInfo_2415_, lean_object* v___x_2416_, lean_object* v___f_2417_, lean_object* v___x_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; 
lean_inc(v_matcherName_2414_);
v___x_2424_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_matcherName_2414_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v_levelParams_2426_; lean_object* v_type_2427_; lean_object* v_numParams_2428_; lean_object* v_numDiscrs_2429_; lean_object* v_uElimPos_x3f_2430_; lean_object* v___x_2431_; lean_object* v___f_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; lean_object* v___x_2436_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v_levelParams_2426_ = lean_ctor_get(v_a_2425_, 1);
lean_inc(v_levelParams_2426_);
v_type_2427_ = lean_ctor_get(v_a_2425_, 2);
lean_inc_ref(v_type_2427_);
lean_dec(v_a_2425_);
v_numParams_2428_ = lean_ctor_get(v_matcherInfo_2415_, 0);
lean_inc_n(v_numParams_2428_, 2);
v_numDiscrs_2429_ = lean_ctor_get(v_matcherInfo_2415_, 1);
lean_inc(v_numDiscrs_2429_);
v_uElimPos_x3f_2430_ = lean_ctor_get(v_matcherInfo_2415_, 3);
lean_inc(v_uElimPos_x3f_2430_);
v___x_2431_ = lean_unsigned_to_nat(1u);
v___f_2432_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed), 17, 10);
lean_closure_set(v___f_2432_, 0, v_numParams_2428_);
lean_closure_set(v___f_2432_, 1, v___x_2416_);
lean_closure_set(v___f_2432_, 2, v___x_2431_);
lean_closure_set(v___f_2432_, 3, v_numDiscrs_2429_);
lean_closure_set(v___f_2432_, 4, v___f_2417_);
lean_closure_set(v___f_2432_, 5, v_levelParams_2426_);
lean_closure_set(v___f_2432_, 6, v_matcherName_2414_);
lean_closure_set(v___f_2432_, 7, v_matcherInfo_2415_);
lean_closure_set(v___f_2432_, 8, v___x_2418_);
lean_closure_set(v___f_2432_, 9, v_uElimPos_x3f_2430_);
v___x_2433_ = lean_nat_add(v_numParams_2428_, v___x_2431_);
lean_dec(v_numParams_2428_);
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
v___x_2435_ = 0;
v___x_2436_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_2427_, v___x_2434_, v___f_2432_, v___x_2435_, v___x_2435_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
return v___x_2436_;
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v___x_2418_);
lean_dec_ref(v___f_2417_);
lean_dec_ref(v___x_2416_);
lean_dec_ref(v_matcherInfo_2415_);
lean_dec(v_matcherName_2414_);
v_a_2437_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2424_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2424_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed(lean_object* v_matcherName_2445_, lean_object* v_matcherInfo_2446_, lean_object* v___x_2447_, lean_object* v___f_2448_, lean_object* v___x_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(v_matcherName_2445_, v_matcherInfo_2446_, v___x_2447_, v___f_2448_, v___x_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11(lean_object* v___x_2456_, lean_object* v_e_2457_){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = l_Lean_indentD(v_e_2457_);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2456_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(lean_object* v___f_2460_, lean_object* v___f_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2460_, v___f_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2467_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2467_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed(lean_object* v___f_2484_, lean_object* v___f_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(v___f_2484_, v___f_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
return v_res_2491_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__3));
v___x_2498_ = l_Lean_stringToMessageData(v___x_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(lean_object* v_matcherName_2499_, lean_object* v_matcherInfo_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v___x_2506_; lean_object* v_env_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___f_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___f_2517_; lean_object* v___f_2518_; lean_object* v___x_2519_; 
v___x_2506_ = lean_st_ref_get(v_a_2504_);
v_env_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc_ref(v_env_2507_);
lean_dec(v___x_2506_);
v___f_2508_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__0));
v___x_2509_ = l_Lean_instInhabitedExpr;
lean_inc_n(v_matcherName_2499_, 3);
v___x_2510_ = l_Lean_mkPrivateName(v_env_2507_, v_matcherName_2499_);
lean_dec_ref(v_env_2507_);
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__2));
v___x_2512_ = l_Lean_Name_append(v___x_2510_, v___x_2511_);
lean_inc_n(v___x_2512_, 2);
v___f_2513_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed), 10, 5);
lean_closure_set(v___f_2513_, 0, v_matcherName_2499_);
lean_closure_set(v___f_2513_, 1, v_matcherInfo_2500_);
lean_closure_set(v___f_2513_, 2, v___x_2509_);
lean_closure_set(v___f_2513_, 3, v___f_2508_);
lean_closure_set(v___f_2513_, 4, v___x_2512_);
v___x_2514_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4);
v___x_2515_ = l_Lean_MessageData_ofName(v_matcherName_2499_);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___f_2517_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_2517_, 0, v___x_2516_);
v___f_2518_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed), 7, 2);
lean_closure_set(v___f_2518_, 0, v___f_2513_);
lean_closure_set(v___f_2518_, 1, v___f_2517_);
v___x_2519_ = l_Lean_Meta_realizeConst(v_matcherName_2499_, v___x_2512_, v___f_2518_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v___x_2519_, 0);
lean_dec(v_unused_2527_);
v___x_2521_ = v___x_2519_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_dec(v___x_2519_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2512_);
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2512_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v___x_2512_);
v_a_2528_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2519_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2519_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___boxed(lean_object* v_matcherName_2536_, lean_object* v_matcherInfo_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_2536_, v_matcherInfo_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(lean_object* v_as_2544_, lean_object* v_as_x27_2545_, lean_object* v_b_2546_, lean_object* v_a_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_2545_, v_b_2546_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___boxed(lean_object* v_as_2554_, lean_object* v_as_x27_2555_, lean_object* v_b_2556_, lean_object* v_a_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(v_as_2554_, v_as_x27_2555_, v_b_2556_, v_a_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v_as_x27_2555_);
lean_dec(v_as_2554_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(lean_object* v_00_u03b1_2564_, lean_object* v_name_2565_, uint8_t v_bi_2566_, lean_object* v_type_2567_, lean_object* v_k_2568_, uint8_t v_kind_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_2565_, v_bi_2566_, v_type_2567_, v_k_2568_, v_kind_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2576_, lean_object* v_name_2577_, lean_object* v_bi_2578_, lean_object* v_type_2579_, lean_object* v_k_2580_, lean_object* v_kind_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
uint8_t v_bi_boxed_2587_; uint8_t v_kind_boxed_2588_; lean_object* v_res_2589_; 
v_bi_boxed_2587_ = lean_unbox(v_bi_2578_);
v_kind_boxed_2588_ = lean_unbox(v_kind_2581_);
v_res_2589_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(v_00_u03b1_2576_, v_name_2577_, v_bi_boxed_2587_, v_type_2579_, v_k_2580_, v_kind_boxed_2588_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(lean_object* v_00_u03b1_2590_, lean_object* v_name_2591_, lean_object* v_type_2592_, lean_object* v_k_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_2591_, v_type_2592_, v_k_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___boxed(lean_object* v_00_u03b1_2600_, lean_object* v_name_2601_, lean_object* v_type_2602_, lean_object* v_k_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(v_00_u03b1_2600_, v_name_2601_, v_type_2602_, v_k_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(lean_object* v_00_u03b1_2610_, lean_object* v_constName_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2618_, lean_object* v_constName_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(v_00_u03b1_2618_, v_constName_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2626_, lean_object* v_ref_2627_, lean_object* v_constName_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2627_, v_constName_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2635_, lean_object* v_ref_2636_, lean_object* v_constName_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(v_00_u03b1_2635_, v_ref_2636_, v_constName_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v_ref_2636_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b1_2644_, lean_object* v_ref_2645_, lean_object* v_msg_2646_, lean_object* v_declHint_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2645_, v_msg_2646_, v_declHint_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b1_2654_, lean_object* v_ref_2655_, lean_object* v_msg_2656_, lean_object* v_declHint_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(v_00_u03b1_2654_, v_ref_2655_, v_msg_2656_, v_declHint_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v_ref_2655_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(lean_object* v_msg_2664_, lean_object* v_declHint_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2664_, v_declHint_2665_, v___y_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_2672_, lean_object* v_declHint_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(v_msg_2672_, v_declHint_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_2680_, lean_object* v_ref_2681_, lean_object* v_msg_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2681_, v_msg_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_2689_, lean_object* v_ref_2690_, lean_object* v_msg_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(v_00_u03b1_2689_, v_ref_2690_, v_msg_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v_ref_2690_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(lean_object* v_msg_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___f_2708_; lean_object* v___x_34392__overap_2709_; lean_object* v___x_2710_; 
v___f_2708_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0));
v___x_34392__overap_2709_ = lean_panic_fn_borrowed(v___f_2708_, v_msg_2699_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v___y_2704_);
lean_inc_ref(v___y_2703_);
lean_inc(v___y_2702_);
lean_inc_ref(v___y_2701_);
lean_inc(v___y_2700_);
v___x_2710_ = lean_apply_8(v___x_34392__overap_2709_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, lean_box(0));
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___boxed(lean_object* v_msg_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v_msg_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(lean_object* v_k_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v_b_2725_, lean_object* v_c_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
lean_inc(v___y_2728_);
lean_inc_ref(v___y_2727_);
lean_inc(v___y_2724_);
lean_inc_ref(v___y_2723_);
lean_inc(v___y_2722_);
v___x_2732_ = lean_apply_10(v_k_2721_, v_b_2725_, v_c_2726_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, lean_box(0));
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed(lean_object* v_k_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v_b_2737_, lean_object* v_c_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(v_k_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v_b_2737_, v_c_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(lean_object* v_e_2745_, lean_object* v_k_2746_, uint8_t v_cleanupAnnotations_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v___f_2756_; uint8_t v___x_2757_; uint8_t v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2749_);
lean_inc(v___y_2748_);
v___f_2756_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2756_, 0, v_k_2746_);
lean_closure_set(v___f_2756_, 1, v___y_2748_);
lean_closure_set(v___f_2756_, 2, v___y_2749_);
lean_closure_set(v___f_2756_, 3, v___y_2750_);
v___x_2757_ = 1;
v___x_2758_ = 0;
v___x_2759_ = lean_box(0);
v___x_2760_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2745_, v___x_2757_, v___x_2758_, v___x_2757_, v___x_2758_, v___x_2759_, v___f_2756_, v_cleanupAnnotations_2747_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
if (lean_obj_tag(v___x_2760_) == 0)
{
return v___x_2760_;
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2760_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2760_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___boxed(lean_object* v_e_2769_, lean_object* v_k_2770_, lean_object* v_cleanupAnnotations_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2780_; lean_object* v_res_2781_; 
v_cleanupAnnotations_boxed_2780_ = lean_unbox(v_cleanupAnnotations_2771_);
v_res_2781_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2769_, v_k_2770_, v_cleanupAnnotations_boxed_2780_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(lean_object* v_00_u03b1_2782_, lean_object* v_e_2783_, lean_object* v_k_2784_, uint8_t v_cleanupAnnotations_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2783_, v_k_2784_, v_cleanupAnnotations_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___boxed(lean_object* v_00_u03b1_2795_, lean_object* v_e_2796_, lean_object* v_k_2797_, lean_object* v_cleanupAnnotations_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2807_; lean_object* v_res_2808_; 
v_cleanupAnnotations_boxed_2807_ = lean_unbox(v_cleanupAnnotations_2798_);
v_res_2808_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(v_00_u03b1_2795_, v_e_2796_, v_k_2797_, v_cleanupAnnotations_boxed_2807_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(uint8_t v___x_2809_, uint8_t v___x_2810_, uint8_t v___x_2811_, lean_object* v_xs_2812_, lean_object* v_motiveBody_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2822_ = l_Lean_Expr_bindingDomain_x21(v_motiveBody_2813_);
v___x_2823_ = l_Lean_Expr_bindingName_x21(v___x_2822_);
v___x_2824_ = l_Lean_Expr_bindingDomain_x21(v___x_2822_);
v___x_2825_ = l_Lean_Expr_bindingBody_x21(v___x_2822_);
lean_dec_ref(v___x_2822_);
v___x_2826_ = l_Lean_Expr_bindingDomain_x21(v___x_2825_);
lean_dec_ref(v___x_2825_);
v___x_2827_ = l_Lean_Expr_lam___override(v___x_2823_, v___x_2824_, v___x_2826_, v___x_2809_);
v___x_2828_ = 1;
v___x_2829_ = l_Lean_Meta_mkLambdaFVars(v_xs_2812_, v___x_2827_, v___x_2810_, v___x_2811_, v___x_2810_, v___x_2811_, v___x_2828_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed(lean_object* v___x_2830_, lean_object* v___x_2831_, lean_object* v___x_2832_, lean_object* v_xs_2833_, lean_object* v_motiveBody_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
uint8_t v___x_41733__boxed_2843_; uint8_t v___x_41734__boxed_2844_; uint8_t v___x_41735__boxed_2845_; lean_object* v_res_2846_; 
v___x_41733__boxed_2843_ = lean_unbox(v___x_2830_);
v___x_41734__boxed_2844_ = lean_unbox(v___x_2831_);
v___x_41735__boxed_2845_ = lean_unbox(v___x_2832_);
v_res_2846_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(v___x_41733__boxed_2843_, v___x_41734__boxed_2844_, v___x_41735__boxed_2845_, v_xs_2833_, v_motiveBody_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v_motiveBody_2834_);
lean_dec_ref(v_xs_2833_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(size_t v_sz_2847_, size_t v_i_2848_, lean_object* v_bs_2849_){
_start:
{
uint8_t v___x_2850_; 
v___x_2850_ = lean_usize_dec_lt(v_i_2848_, v_sz_2847_);
if (v___x_2850_ == 0)
{
return v_bs_2849_;
}
else
{
lean_object* v_v_2851_; lean_object* v___x_2852_; lean_object* v_bs_x27_2853_; lean_object* v___x_2854_; size_t v___x_2855_; size_t v___x_2856_; lean_object* v___x_2857_; 
v_v_2851_ = lean_array_uget(v_bs_2849_, v_i_2848_);
v___x_2852_ = lean_unsigned_to_nat(0u);
v_bs_x27_2853_ = lean_array_uset(v_bs_2849_, v_i_2848_, v___x_2852_);
v___x_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2854_, 0, v_v_2851_);
v___x_2855_ = ((size_t)1ULL);
v___x_2856_ = lean_usize_add(v_i_2848_, v___x_2855_);
v___x_2857_ = lean_array_uset(v_bs_x27_2853_, v_i_2848_, v___x_2854_);
v_i_2848_ = v___x_2856_;
v_bs_2849_ = v___x_2857_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4___boxed(lean_object* v_sz_2859_, lean_object* v_i_2860_, lean_object* v_bs_2861_){
_start:
{
size_t v_sz_boxed_2862_; size_t v_i_boxed_2863_; lean_object* v_res_2864_; 
v_sz_boxed_2862_ = lean_unbox_usize(v_sz_2859_);
lean_dec(v_sz_2859_);
v_i_boxed_2863_ = lean_unbox_usize(v_i_2860_);
lean_dec(v_i_2860_);
v_res_2864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_boxed_2862_, v_i_boxed_2863_, v_bs_2861_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(lean_object* v_msg_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_ref_2871_; lean_object* v___x_2872_; lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2881_; 
v_ref_2871_ = lean_ctor_get(v___y_2868_, 2);
v___x_2872_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2875_ = v___x_2872_;
v_isShared_2876_ = v_isSharedCheck_2881_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2881_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
lean_inc(v_ref_2871_);
v___x_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2877_, 0, v_ref_2871_);
lean_ctor_set(v___x_2877_, 1, v_a_2873_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set_tag(v___x_2875_, 1);
lean_ctor_set(v___x_2875_, 0, v___x_2877_);
v___x_2879_ = v___x_2875_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg___boxed(lean_object* v_msg_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(lean_object* v_declName_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___x_2892_; lean_object* v_env_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2892_ = lean_st_ref_get(v___y_2890_);
v_env_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc_ref(v_env_2893_);
lean_dec(v___x_2892_);
v___x_2894_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2893_, v_declName_2889_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg___boxed(lean_object* v_declName_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_2896_, v___y_2897_);
lean_dec(v___y_2897_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(lean_object* v_ref_2900_, lean_object* v_msg_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_toCold_2910_; lean_object* v_currRecDepth_2911_; lean_object* v_ref_2912_; uint8_t v_diag_2913_; uint8_t v_suppressElabErrors_2914_; lean_object* v_ref_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v_toCold_2910_ = lean_ctor_get(v___y_2907_, 0);
v_currRecDepth_2911_ = lean_ctor_get(v___y_2907_, 1);
v_ref_2912_ = lean_ctor_get(v___y_2907_, 2);
v_diag_2913_ = lean_ctor_get_uint8(v___y_2907_, sizeof(void*)*3);
v_suppressElabErrors_2914_ = lean_ctor_get_uint8(v___y_2907_, sizeof(void*)*3 + 1);
v_ref_2915_ = l_Lean_replaceRef(v_ref_2900_, v_ref_2912_);
lean_inc(v_currRecDepth_2911_);
lean_inc_ref(v_toCold_2910_);
v___x_2916_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2916_, 0, v_toCold_2910_);
lean_ctor_set(v___x_2916_, 1, v_currRecDepth_2911_);
lean_ctor_set(v___x_2916_, 2, v_ref_2915_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*3, v_diag_2913_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*3 + 1, v_suppressElabErrors_2914_);
v___x_2917_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2901_, v___y_2905_, v___y_2906_, v___x_2916_, v___y_2908_);
lean_dec_ref_known(v___x_2916_, 3);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2918_, lean_object* v_msg_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_2918_, v_msg_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec(v_ref_2918_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2929_, lean_object* v_declHint_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v___x_2933_; lean_object* v_env_2934_; uint8_t v___x_2935_; 
v___x_2933_ = lean_st_ref_get(v___y_2931_);
v_env_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc_ref(v_env_2934_);
lean_dec(v___x_2933_);
v___x_2935_ = l_Lean_Name_isAnonymous(v_declHint_2930_);
if (v___x_2935_ == 0)
{
uint8_t v_isExporting_2936_; 
v_isExporting_2936_ = lean_ctor_get_uint8(v_env_2934_, sizeof(void*)*8);
if (v_isExporting_2936_ == 0)
{
lean_object* v___x_2937_; 
lean_dec_ref(v_env_2934_);
lean_dec(v_declHint_2930_);
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_msg_2929_);
return v___x_2937_;
}
else
{
lean_object* v___x_2938_; uint8_t v___x_2939_; 
lean_inc_ref(v_env_2934_);
v___x_2938_ = l_Lean_Environment_setExporting(v_env_2934_, v___x_2935_);
lean_inc(v_declHint_2930_);
lean_inc_ref(v___x_2938_);
v___x_2939_ = l_Lean_Environment_contains(v___x_2938_, v_declHint_2930_, v_isExporting_2936_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; 
lean_dec_ref(v___x_2938_);
lean_dec_ref(v_env_2934_);
lean_dec(v_declHint_2930_);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v_msg_2929_);
return v___x_2940_;
}
else
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v_c_2948_; lean_object* v___x_2949_; 
v___x_2941_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2942_ = lean_unsigned_to_nat(32u);
v___x_2943_ = lean_mk_empty_array_with_capacity(v___x_2942_);
lean_dec_ref(v___x_2943_);
v___x_2944_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2945_ = l_Lean_Options_empty;
v___x_2946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2938_);
lean_ctor_set(v___x_2946_, 1, v___x_2941_);
lean_ctor_set(v___x_2946_, 2, v___x_2944_);
lean_ctor_set(v___x_2946_, 3, v___x_2945_);
lean_inc(v_declHint_2930_);
v___x_2947_ = l_Lean_MessageData_ofConstName(v_declHint_2930_, v___x_2935_);
v_c_2948_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2948_, 0, v___x_2946_);
lean_ctor_set(v_c_2948_, 1, v___x_2947_);
v___x_2949_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2934_, v_declHint_2930_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec_ref(v_env_2934_);
lean_dec(v_declHint_2930_);
v___x_2950_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v_c_2948_);
v___x_2952_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2951_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = l_Lean_MessageData_note(v___x_2953_);
v___x_2955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2955_, 0, v_msg_2929_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
return v___x_2956_;
}
else
{
lean_object* v_val_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2992_; 
v_val_2957_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2959_ = v___x_2949_;
v_isShared_2960_ = v_isSharedCheck_2992_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_val_2957_);
lean_dec(v___x_2949_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2992_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v_mod_2964_; uint8_t v___x_2965_; 
v___x_2961_ = lean_box(0);
v___x_2962_ = l_Lean_Environment_header(v_env_2934_);
lean_dec_ref(v_env_2934_);
v___x_2963_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2962_);
v_mod_2964_ = lean_array_get(v___x_2961_, v___x_2963_, v_val_2957_);
lean_dec(v_val_2957_);
lean_dec_ref(v___x_2963_);
v___x_2965_ = l_Lean_isPrivateName(v_declHint_2930_);
lean_dec(v_declHint_2930_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2966_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
lean_ctor_set(v___x_2967_, 1, v_c_2948_);
v___x_2968_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2967_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___x_2970_ = l_Lean_MessageData_ofName(v_mod_2964_);
v___x_2971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2969_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l_Lean_MessageData_note(v___x_2973_);
v___x_2975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2975_, 0, v_msg_2929_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set_tag(v___x_2959_, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2975_);
v___x_2977_ = v___x_2959_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2979_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
lean_ctor_set(v___x_2980_, 1, v_c_2948_);
v___x_2981_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_2982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = l_Lean_MessageData_ofName(v_mod_2964_);
v___x_2984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_2986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = l_Lean_MessageData_note(v___x_2986_);
v___x_2988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2988_, 0, v_msg_2929_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set_tag(v___x_2959_, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2988_);
v___x_2990_ = v___x_2959_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2993_; 
lean_dec_ref(v_env_2934_);
lean_dec(v_declHint_2930_);
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v_msg_2929_);
return v___x_2993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2994_, lean_object* v_declHint_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_2994_, v_declHint_2995_, v___y_2996_);
lean_dec(v___y_2996_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(lean_object* v_msg_2999_, lean_object* v_declHint_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v___x_3009_; lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3019_; 
v___x_3009_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_2999_, v_declHint_3000_, v___y_3007_);
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3019_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3019_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3017_; 
v___x_3014_ = l_Lean_unknownIdentifierMessageTag;
v___x_3015_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
lean_ctor_set(v___x_3015_, 1, v_a_3010_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___x_3015_);
v___x_3017_ = v___x_3012_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3015_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11___boxed(lean_object* v_msg_3020_, lean_object* v_declHint_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3020_, v_declHint_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object* v_ref_3031_, lean_object* v_msg_3032_, lean_object* v_declHint_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v_a_3043_; lean_object* v___x_3044_; 
v___x_3042_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3032_, v_declHint_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3042_);
v___x_3044_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3031_, v_a_3043_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_ref_3045_, lean_object* v_msg_3046_, lean_object* v_declHint_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3045_, v_msg_3046_, v_declHint_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec(v_ref_3045_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(lean_object* v_ref_3057_, lean_object* v_constName_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___x_3067_; uint8_t v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3067_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3068_ = 0;
lean_inc(v_constName_3058_);
v___x_3069_ = l_Lean_MessageData_ofConstName(v_constName_3058_, v___x_3068_);
v___x_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3067_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3070_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3057_, v___x_3072_, v_constName_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_ref_3074_, lean_object* v_constName_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3074_, v_constName_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec(v_ref_3074_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_ref_3094_; lean_object* v___x_3095_; 
v_ref_3094_ = lean_ctor_get(v___y_3091_, 2);
v___x_3095_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3094_, v_constName_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(lean_object* v_constName_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; lean_object* v_env_3116_; uint8_t v___x_3117_; lean_object* v___x_3118_; 
v___x_3115_ = lean_st_ref_get(v___y_3113_);
v_env_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc_ref(v_env_3116_);
lean_dec(v___x_3115_);
v___x_3117_ = 0;
lean_inc(v_constName_3106_);
v___x_3118_ = l_Lean_Environment_find_x3f(v_env_3116_, v_constName_3106_, v___x_3117_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v___x_3119_; 
v___x_3119_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
return v___x_3119_;
}
else
{
lean_object* v_val_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v_constName_3106_);
v_val_3120_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3118_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_val_3120_);
lean_dec(v___x_3118_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set_tag(v___x_3122_, 0);
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_val_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0___boxed(lean_object* v_constName_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_constName_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
return v_res_3137_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_instMonadEIO(lean_box(0));
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(lean_object* v_msg_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v_toApplicative_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3218_; 
v___x_3152_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0);
v___x_3153_ = l_StateRefT_x27_instMonad___redArg(v___x_3152_);
v_toApplicative_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3218_ == 0)
{
lean_object* v_unused_3219_; 
v_unused_3219_ = lean_ctor_get(v___x_3153_, 1);
lean_dec(v_unused_3219_);
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3218_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_toApplicative_3154_);
lean_dec(v___x_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3218_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v_toFunctor_3158_; lean_object* v_toSeq_3159_; lean_object* v_toSeqLeft_3160_; lean_object* v_toSeqRight_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3216_; 
v_toFunctor_3158_ = lean_ctor_get(v_toApplicative_3154_, 0);
v_toSeq_3159_ = lean_ctor_get(v_toApplicative_3154_, 2);
v_toSeqLeft_3160_ = lean_ctor_get(v_toApplicative_3154_, 3);
v_toSeqRight_3161_ = lean_ctor_get(v_toApplicative_3154_, 4);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_toApplicative_3154_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; 
v_unused_3217_ = lean_ctor_get(v_toApplicative_3154_, 1);
lean_dec(v_unused_3217_);
v___x_3163_ = v_toApplicative_3154_;
v_isShared_3164_ = v_isSharedCheck_3216_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_toSeqRight_3161_);
lean_inc(v_toSeqLeft_3160_);
lean_inc(v_toSeq_3159_);
lean_inc(v_toFunctor_3158_);
lean_dec(v_toApplicative_3154_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3216_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___f_3165_; lean_object* v___f_3166_; lean_object* v___f_3167_; lean_object* v___f_3168_; lean_object* v___x_3169_; lean_object* v___f_3170_; lean_object* v___f_3171_; lean_object* v___f_3172_; lean_object* v___x_3174_; 
v___f_3165_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__1));
v___f_3166_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3158_);
v___f_3167_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3167_, 0, v_toFunctor_3158_);
v___f_3168_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3168_, 0, v_toFunctor_3158_);
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___f_3167_);
lean_ctor_set(v___x_3169_, 1, v___f_3168_);
v___f_3170_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3170_, 0, v_toSeqRight_3161_);
v___f_3171_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3171_, 0, v_toSeqLeft_3160_);
v___f_3172_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3172_, 0, v_toSeq_3159_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v___f_3170_);
lean_ctor_set(v___x_3163_, 3, v___f_3171_);
lean_ctor_set(v___x_3163_, 2, v___f_3172_);
lean_ctor_set(v___x_3163_, 1, v___f_3165_);
lean_ctor_set(v___x_3163_, 0, v___x_3169_);
v___x_3174_ = v___x_3163_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___f_3165_);
lean_ctor_set(v_reuseFailAlloc_3215_, 2, v___f_3172_);
lean_ctor_set(v_reuseFailAlloc_3215_, 3, v___f_3171_);
lean_ctor_set(v_reuseFailAlloc_3215_, 4, v___f_3170_);
v___x_3174_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
lean_object* v___x_3176_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 1, v___f_3166_);
lean_ctor_set(v___x_3156_, 0, v___x_3174_);
v___x_3176_ = v___x_3156_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v___f_3166_);
v___x_3176_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
lean_object* v___x_3177_; lean_object* v_toApplicative_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3212_; 
v___x_3177_ = l_StateRefT_x27_instMonad___redArg(v___x_3176_);
v_toApplicative_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v___x_3177_, 1);
lean_dec(v_unused_3213_);
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3212_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_toApplicative_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3212_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_toFunctor_3182_; lean_object* v_toSeq_3183_; lean_object* v_toSeqLeft_3184_; lean_object* v_toSeqRight_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3210_; 
v_toFunctor_3182_ = lean_ctor_get(v_toApplicative_3178_, 0);
v_toSeq_3183_ = lean_ctor_get(v_toApplicative_3178_, 2);
v_toSeqLeft_3184_ = lean_ctor_get(v_toApplicative_3178_, 3);
v_toSeqRight_3185_ = lean_ctor_get(v_toApplicative_3178_, 4);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_toApplicative_3178_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v_toApplicative_3178_, 1);
lean_dec(v_unused_3211_);
v___x_3187_ = v_toApplicative_3178_;
v_isShared_3188_ = v_isSharedCheck_3210_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_toSeqRight_3185_);
lean_inc(v_toSeqLeft_3184_);
lean_inc(v_toSeq_3183_);
lean_inc(v_toFunctor_3182_);
lean_dec(v_toApplicative_3178_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3210_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___f_3189_; lean_object* v___f_3190_; lean_object* v___f_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; lean_object* v___f_3194_; lean_object* v___f_3195_; lean_object* v___f_3196_; lean_object* v___x_3198_; 
v___f_3189_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__3));
v___f_3190_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3182_);
v___f_3191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3191_, 0, v_toFunctor_3182_);
v___f_3192_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3192_, 0, v_toFunctor_3182_);
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___f_3191_);
lean_ctor_set(v___x_3193_, 1, v___f_3192_);
v___f_3194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3194_, 0, v_toSeqRight_3185_);
v___f_3195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3195_, 0, v_toSeqLeft_3184_);
v___f_3196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3196_, 0, v_toSeq_3183_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 4, v___f_3194_);
lean_ctor_set(v___x_3187_, 3, v___f_3195_);
lean_ctor_set(v___x_3187_, 2, v___f_3196_);
lean_ctor_set(v___x_3187_, 1, v___f_3189_);
lean_ctor_set(v___x_3187_, 0, v___x_3193_);
v___x_3198_ = v___x_3187_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v___f_3189_);
lean_ctor_set(v_reuseFailAlloc_3209_, 2, v___f_3196_);
lean_ctor_set(v_reuseFailAlloc_3209_, 3, v___f_3195_);
lean_ctor_set(v_reuseFailAlloc_3209_, 4, v___f_3194_);
v___x_3198_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3200_; 
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 1, v___f_3190_);
lean_ctor_set(v___x_3180_, 0, v___x_3198_);
v___x_3200_ = v___x_3180_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v___f_3190_);
v___x_3200_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_36464__overap_3206_; lean_object* v___x_3207_; 
v___x_3201_ = l_StateRefT_x27_instMonad___redArg(v___x_3200_);
v___x_3202_ = l_ReaderT_instMonad___redArg(v___x_3201_);
v___x_3203_ = l_ReaderT_instMonad___redArg(v___x_3202_);
v___x_3204_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3205_ = l_instInhabitedOfMonad___redArg(v___x_3203_, v___x_3204_);
v___x_36464__overap_3206_ = lean_panic_fn_borrowed(v___x_3205_, v_msg_3143_);
lean_dec(v___x_3205_);
lean_inc(v___y_3150_);
lean_inc_ref(v___y_3149_);
lean_inc(v___y_3148_);
lean_inc_ref(v___y_3147_);
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
lean_inc(v___y_3144_);
v___x_3207_ = lean_apply_8(v___x_36464__overap_3206_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, lean_box(0));
return v___x_3207_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___boxed(lean_object* v_msg_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v_msg_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
return v_res_3229_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__2));
v___x_3234_ = lean_unsigned_to_nat(53u);
v___x_3235_ = lean_unsigned_to_nat(62u);
v___x_3236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__1));
v___x_3237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__0));
v___x_3238_ = l_mkPanicMessageWithDecl(v___x_3237_, v___x_3236_, v___x_3235_, v___x_3234_, v___x_3233_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(size_t v_sz_3239_, size_t v_i_3240_, lean_object* v_bs_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
uint8_t v___x_3250_; 
v___x_3250_ = lean_usize_dec_lt(v_i_3240_, v_sz_3239_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; 
v___x_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3251_, 0, v_bs_3241_);
return v___x_3251_;
}
else
{
lean_object* v_v_3252_; lean_object* v___x_3253_; 
v_v_3252_ = lean_array_uget_borrowed(v_bs_3241_, v_i_3240_);
lean_inc(v_v_3252_);
v___x_3253_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_v_3252_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3255_; lean_object* v_bs_x27_3256_; lean_object* v_a_3258_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref_known(v___x_3253_, 1);
v___x_3255_ = lean_unsigned_to_nat(0u);
v_bs_x27_3256_ = lean_array_uset(v_bs_3241_, v_i_3240_, v___x_3255_);
if (lean_obj_tag(v_a_3254_) == 6)
{
lean_object* v_val_3263_; lean_object* v_numFields_3264_; uint8_t v___x_3265_; lean_object* v___x_3266_; 
v_val_3263_ = lean_ctor_get(v_a_3254_, 0);
lean_inc_ref(v_val_3263_);
lean_dec_ref_known(v_a_3254_, 1);
v_numFields_3264_ = lean_ctor_get(v_val_3263_, 4);
lean_inc(v_numFields_3264_);
lean_dec_ref(v_val_3263_);
v___x_3265_ = 0;
v___x_3266_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3266_, 0, v_numFields_3264_);
lean_ctor_set(v___x_3266_, 1, v___x_3255_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*2, v___x_3265_);
v_a_3258_ = v___x_3266_;
goto v___jp_3257_;
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
lean_dec(v_a_3254_);
v___x_3267_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3);
v___x_3268_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v___x_3267_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
v_a_3258_ = v_a_3269_;
goto v___jp_3257_;
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v_bs_x27_3256_);
v_a_3270_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3268_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3268_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
v___jp_3257_:
{
size_t v___x_3259_; size_t v___x_3260_; lean_object* v___x_3261_; 
v___x_3259_ = ((size_t)1ULL);
v___x_3260_ = lean_usize_add(v_i_3240_, v___x_3259_);
v___x_3261_ = lean_array_uset(v_bs_x27_3256_, v_i_3240_, v_a_3258_);
v_i_3240_ = v___x_3260_;
v_bs_3241_ = v___x_3261_;
goto _start;
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec_ref(v_bs_3241_);
v_a_3278_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3253_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3253_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___boxed(lean_object* v_sz_3286_, lean_object* v_i_3287_, lean_object* v_bs_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
size_t v_sz_boxed_3297_; size_t v_i_boxed_3298_; lean_object* v_res_3299_; 
v_sz_boxed_3297_ = lean_unbox_usize(v_sz_3286_);
lean_dec(v_sz_3286_);
v_i_boxed_3298_ = lean_unbox_usize(v_i_3287_);
lean_dec(v_i_3287_);
v_res_3299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_boxed_3297_, v_i_boxed_3298_, v_bs_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
return v_res_3299_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_unsigned_to_nat(16u);
v___x_3302_ = lean_mk_array(v___x_3301_, v___x_3300_);
return v___x_3302_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0);
v___x_3304_ = lean_unsigned_to_nat(0u);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v___x_3303_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(lean_object* v_e_3308_, uint8_t v_alsoCasesOn_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
uint8_t v___x_3321_; 
v___x_3321_ = l_Lean_Expr_isApp(v_e_3308_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_dec_ref(v_e_3308_);
v___x_3322_ = lean_box(0);
v___x_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
return v___x_3323_;
}
else
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Lean_Expr_getAppFn(v_e_3308_);
if (lean_obj_tag(v___x_3324_) == 4)
{
lean_object* v_declName_3325_; lean_object* v_us_3326_; lean_object* v___x_3327_; lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3481_; 
v_declName_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc_n(v_declName_3325_, 2);
v_us_3326_ = lean_ctor_get(v___x_3324_, 1);
lean_inc(v_us_3326_);
lean_dec_ref_known(v___x_3324_, 2);
v___x_3327_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3325_, v___y_3316_);
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3330_ = v___x_3327_;
v_isShared_3331_ = v_isSharedCheck_3481_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3481_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_a_3328_) == 1)
{
lean_object* v_val_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3374_; 
v_val_3333_ = lean_ctor_get(v_a_3328_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_a_3328_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3335_ = v_a_3328_;
v_isShared_3336_ = v_isSharedCheck_3374_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_val_3333_);
lean_dec(v_a_3328_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3374_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v_dummy_3337_; lean_object* v_nargs_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v_args_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v_dummy_3337_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_3338_ = l_Lean_Expr_getAppNumArgs(v_e_3308_);
lean_inc(v_nargs_3338_);
v___x_3339_ = lean_mk_array(v_nargs_3338_, v_dummy_3337_);
v___x_3340_ = lean_unsigned_to_nat(1u);
v___x_3341_ = lean_nat_sub(v_nargs_3338_, v___x_3340_);
lean_dec(v_nargs_3338_);
v_args_3342_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3308_, v___x_3339_, v___x_3341_);
v___x_3343_ = lean_array_get_size(v_args_3342_);
v___x_3344_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_3333_);
v___x_3345_ = lean_nat_dec_lt(v___x_3343_, v___x_3344_);
lean_dec(v___x_3344_);
if (v___x_3345_ == 0)
{
lean_object* v_numParams_3346_; lean_object* v_numDiscrs_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
v_numParams_3346_ = lean_ctor_get(v_val_3333_, 0);
v_numDiscrs_3347_ = lean_ctor_get(v_val_3333_, 1);
v___x_3348_ = lean_array_mk(v_us_3326_);
v___x_3349_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3346_);
v___x_3350_ = l_Array_extract___redArg(v_args_3342_, v___x_3349_, v_numParams_3346_);
v___x_3351_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3333_);
v___x_3352_ = lean_array_get(v___x_3332_, v_args_3342_, v___x_3351_);
lean_dec(v___x_3351_);
v___x_3353_ = lean_nat_add(v_numParams_3346_, v___x_3340_);
v___x_3354_ = lean_nat_add(v___x_3353_, v_numDiscrs_3347_);
lean_inc(v___x_3354_);
lean_inc_ref_n(v_args_3342_, 2);
v___x_3355_ = l_Array_toSubarray___redArg(v_args_3342_, v___x_3353_, v___x_3354_);
v___x_3356_ = l_Subarray_copy___redArg(v___x_3355_);
v___x_3357_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3333_);
v___x_3358_ = lean_nat_add(v___x_3354_, v___x_3357_);
lean_dec(v___x_3357_);
lean_inc(v___x_3358_);
v___x_3359_ = l_Array_toSubarray___redArg(v_args_3342_, v___x_3354_, v___x_3358_);
v___x_3360_ = l_Subarray_copy___redArg(v___x_3359_);
v___x_3361_ = l_Array_toSubarray___redArg(v_args_3342_, v___x_3358_, v___x_3343_);
v___x_3362_ = l_Subarray_copy___redArg(v___x_3361_);
v___x_3363_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3363_, 0, v_val_3333_);
lean_ctor_set(v___x_3363_, 1, v_declName_3325_);
lean_ctor_set(v___x_3363_, 2, v___x_3348_);
lean_ctor_set(v___x_3363_, 3, v___x_3350_);
lean_ctor_set(v___x_3363_, 4, v___x_3352_);
lean_ctor_set(v___x_3363_, 5, v___x_3356_);
lean_ctor_set(v___x_3363_, 6, v___x_3360_);
lean_ctor_set(v___x_3363_, 7, v___x_3362_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3363_);
v___x_3365_ = v___x_3335_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3367_; 
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3365_);
v___x_3367_ = v___x_3330_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
else
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
lean_dec_ref(v_args_3342_);
lean_del_object(v___x_3335_);
lean_dec(v_val_3333_);
lean_dec(v_us_3326_);
lean_dec(v_declName_3325_);
v___x_3370_ = lean_box(0);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3370_);
v___x_3372_ = v___x_3330_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
lean_object* v___x_3375_; 
lean_del_object(v___x_3330_);
lean_dec(v_a_3328_);
v___x_3375_ = lean_st_ref_get(v___y_3316_);
if (v_alsoCasesOn_3309_ == 0)
{
lean_dec(v___x_3375_);
lean_dec(v_us_3326_);
lean_dec(v_declName_3325_);
lean_dec_ref(v_e_3308_);
goto v___jp_3318_;
}
else
{
lean_object* v_env_3376_; uint8_t v___x_3377_; 
v_env_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc_ref(v_env_3376_);
lean_dec(v___x_3375_);
lean_inc(v_declName_3325_);
v___x_3377_ = l_Lean_isCasesOnRecursor(v_env_3376_, v_declName_3325_);
if (v___x_3377_ == 0)
{
lean_dec(v_us_3326_);
lean_dec(v_declName_3325_);
lean_dec_ref(v_e_3308_);
goto v___jp_3318_;
}
else
{
lean_object* v_indName_3378_; lean_object* v___x_3379_; 
v_indName_3378_ = l_Lean_Name_getPrefix(v_declName_3325_);
v___x_3379_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_indName_3378_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3472_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3382_ = v___x_3379_;
v_isShared_3383_ = v_isSharedCheck_3472_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3472_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
if (lean_obj_tag(v_a_3380_) == 5)
{
lean_object* v_val_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3467_; 
v_val_3384_ = lean_ctor_get(v_a_3380_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_a_3380_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3386_ = v_a_3380_;
v_isShared_3387_ = v_isSharedCheck_3467_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_val_3384_);
lean_dec(v_a_3380_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3467_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v_toConstantVal_3388_; lean_object* v_numParams_3389_; lean_object* v_numIndices_3390_; lean_object* v_ctors_3391_; lean_object* v_nargs_3392_; lean_object* v_dummy_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v_args_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v_toConstantVal_3388_ = lean_ctor_get(v_val_3384_, 0);
lean_inc_ref(v_toConstantVal_3388_);
v_numParams_3389_ = lean_ctor_get(v_val_3384_, 1);
lean_inc(v_numParams_3389_);
v_numIndices_3390_ = lean_ctor_get(v_val_3384_, 2);
lean_inc(v_numIndices_3390_);
v_ctors_3391_ = lean_ctor_get(v_val_3384_, 4);
lean_inc(v_ctors_3391_);
v_nargs_3392_ = l_Lean_Expr_getAppNumArgs(v_e_3308_);
v_dummy_3393_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_3392_);
v___x_3394_ = lean_mk_array(v_nargs_3392_, v_dummy_3393_);
v___x_3395_ = lean_unsigned_to_nat(1u);
v___x_3396_ = lean_nat_sub(v_nargs_3392_, v___x_3395_);
lean_dec(v_nargs_3392_);
v_args_3397_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3308_, v___x_3394_, v___x_3396_);
v___x_3398_ = lean_nat_add(v_numParams_3389_, v___x_3395_);
v___x_3399_ = lean_nat_add(v___x_3398_, v_numIndices_3390_);
v___x_3400_ = lean_nat_add(v___x_3399_, v___x_3395_);
lean_dec(v___x_3399_);
v___x_3401_ = l_Lean_InductiveVal_numCtors(v_val_3384_);
lean_dec_ref(v_val_3384_);
v___x_3402_ = lean_nat_add(v___x_3400_, v___x_3401_);
lean_dec(v___x_3401_);
v___x_3403_ = lean_array_get_size(v_args_3397_);
v___x_3404_ = lean_nat_dec_le(v___x_3402_, v___x_3403_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
lean_dec(v___x_3402_);
lean_dec(v___x_3400_);
lean_dec(v___x_3398_);
lean_dec_ref(v_args_3397_);
lean_dec(v_ctors_3391_);
lean_dec(v_numIndices_3390_);
lean_dec(v_numParams_3389_);
lean_dec_ref(v_toConstantVal_3388_);
lean_del_object(v___x_3386_);
lean_dec(v_us_3326_);
lean_dec(v_declName_3325_);
v___x_3405_ = lean_box(0);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3405_);
v___x_3407_ = v___x_3382_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
else
{
lean_object* v___x_3409_; lean_object* v_params_3410_; lean_object* v_motive_3411_; lean_object* v_discrs_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v_discrInfos_3415_; lean_object* v_alts_3416_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v_lower_3458_; lean_object* v_upper_3459_; uint8_t v___x_3466_; 
lean_del_object(v___x_3382_);
v___x_3409_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3389_);
lean_inc_ref_n(v_args_3397_, 3);
v_params_3410_ = l_Array_toSubarray___redArg(v_args_3397_, v___x_3409_, v_numParams_3389_);
v_motive_3411_ = lean_array_get(v___x_3332_, v_args_3397_, v_numParams_3389_);
lean_dec(v_numParams_3389_);
lean_inc(v___x_3400_);
v_discrs_3412_ = l_Array_toSubarray___redArg(v_args_3397_, v___x_3398_, v___x_3400_);
v___x_3413_ = lean_nat_add(v_numIndices_3390_, v___x_3395_);
lean_dec(v_numIndices_3390_);
v___x_3414_ = lean_box(0);
v_discrInfos_3415_ = lean_mk_array(v___x_3413_, v___x_3414_);
lean_inc(v___x_3402_);
v_alts_3416_ = l_Array_toSubarray___redArg(v_args_3397_, v___x_3400_, v___x_3402_);
v___x_3466_ = lean_nat_dec_le(v___x_3402_, v___x_3409_);
if (v___x_3466_ == 0)
{
v_lower_3458_ = v___x_3402_;
v_upper_3459_ = v___x_3403_;
goto v___jp_3457_;
}
else
{
lean_dec(v___x_3402_);
v_lower_3458_ = v___x_3409_;
v_upper_3459_ = v___x_3403_;
goto v___jp_3457_;
}
v___jp_3417_:
{
lean_object* v___x_3420_; size_t v_sz_3421_; size_t v___x_3422_; lean_object* v___x_3423_; 
v___x_3420_ = lean_array_mk(v_ctors_3391_);
v_sz_3421_ = lean_array_size(v___x_3420_);
v___x_3422_ = ((size_t)0ULL);
v___x_3423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_3421_, v___x_3422_, v___x_3420_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3448_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3426_ = v___x_3423_;
v_isShared_3427_ = v_isSharedCheck_3448_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3423_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3448_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_start_3428_; lean_object* v_stop_3429_; lean_object* v_start_3430_; lean_object* v_stop_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v_start_3428_ = lean_ctor_get(v_params_3410_, 1);
lean_inc(v_start_3428_);
v_stop_3429_ = lean_ctor_get(v_params_3410_, 2);
lean_inc(v_stop_3429_);
v_start_3430_ = lean_ctor_get(v_discrs_3412_, 1);
lean_inc(v_start_3430_);
v_stop_3431_ = lean_ctor_get(v_discrs_3412_, 2);
lean_inc(v_stop_3431_);
v___x_3432_ = lean_nat_sub(v_stop_3429_, v_start_3428_);
lean_dec(v_start_3428_);
lean_dec(v_stop_3429_);
v___x_3433_ = lean_nat_sub(v_stop_3431_, v_start_3430_);
lean_dec(v_start_3430_);
lean_dec(v_stop_3431_);
v___x_3434_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1);
v___x_3435_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3432_);
lean_ctor_set(v___x_3435_, 1, v___x_3433_);
lean_ctor_set(v___x_3435_, 2, v_a_3424_);
lean_ctor_set(v___x_3435_, 3, v___y_3419_);
lean_ctor_set(v___x_3435_, 4, v_discrInfos_3415_);
lean_ctor_set(v___x_3435_, 5, v___x_3434_);
v___x_3436_ = lean_array_mk(v_us_3326_);
v___x_3437_ = l_Subarray_copy___redArg(v_params_3410_);
v___x_3438_ = l_Subarray_copy___redArg(v_discrs_3412_);
v___x_3439_ = l_Subarray_copy___redArg(v_alts_3416_);
v___x_3440_ = l_Subarray_copy___redArg(v___y_3418_);
v___x_3441_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3435_);
lean_ctor_set(v___x_3441_, 1, v_declName_3325_);
lean_ctor_set(v___x_3441_, 2, v___x_3436_);
lean_ctor_set(v___x_3441_, 3, v___x_3437_);
lean_ctor_set(v___x_3441_, 4, v_motive_3411_);
lean_ctor_set(v___x_3441_, 5, v___x_3438_);
lean_ctor_set(v___x_3441_, 6, v___x_3439_);
lean_ctor_set(v___x_3441_, 7, v___x_3440_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set_tag(v___x_3386_, 1);
lean_ctor_set(v___x_3386_, 0, v___x_3441_);
v___x_3443_ = v___x_3386_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3445_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3443_);
v___x_3445_ = v___x_3426_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v_alts_3416_);
lean_dec_ref(v_discrInfos_3415_);
lean_dec_ref(v_discrs_3412_);
lean_dec(v_motive_3411_);
lean_dec_ref(v_params_3410_);
lean_del_object(v___x_3386_);
lean_dec(v_us_3326_);
lean_dec(v_declName_3325_);
v_a_3449_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3423_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3423_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
v___jp_3457_:
{
lean_object* v_levelParams_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v_levelParams_3460_ = lean_ctor_get(v_toConstantVal_3388_, 1);
lean_inc(v_levelParams_3460_);
lean_dec_ref(v_toConstantVal_3388_);
v___x_3461_ = l_Array_toSubarray___redArg(v_args_3397_, v_lower_3458_, v_upper_3459_);
v___x_3462_ = l_List_lengthTR___redArg(v_levelParams_3460_);
lean_dec(v_levelParams_3460_);
v___x_3463_ = l_List_lengthTR___redArg(v_us_3326_);
v___x_3464_ = lean_nat_dec_eq(v___x_3462_, v___x_3463_);
lean_dec(v___x_3463_);
lean_dec(v___x_3462_);
if (v___x_3464_ == 0)
{
lean_object* v___x_3465_; 
v___x_3465_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__2));
v___y_3418_ = v___x_3461_;
v___y_3419_ = v___x_3465_;
goto v___jp_3417_;
}
else
{
v___y_3418_ = v___x_3461_;
v___y_3419_ = v___x_3414_;
goto v___jp_3417_;
}
}
}
}
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3470_; 
lean_dec(v_a_3380_);
lean_dec(v_us_3326_);
lean_dec(v_declName_3325_);
lean_dec_ref(v_e_3308_);
v___x_3468_ = lean_box(0);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3468_);
v___x_3470_ = v___x_3382_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec(v_us_3326_);
lean_dec(v_declName_3325_);
lean_dec_ref(v_e_3308_);
v_a_3473_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3379_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3379_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
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
lean_dec_ref(v___x_3324_);
lean_dec_ref(v_e_3308_);
goto v___jp_3318_;
}
}
v___jp_3318_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = lean_box(0);
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
return v___x_3320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___boxed(lean_object* v_e_3482_, lean_object* v_alsoCasesOn_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
uint8_t v_alsoCasesOn_boxed_3492_; lean_object* v_res_3493_; 
v_alsoCasesOn_boxed_3492_ = lean_unbox(v_alsoCasesOn_3483_);
v_res_3493_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3482_, v_alsoCasesOn_boxed_3492_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
return v_res_3493_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2(void){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__1));
v___x_3498_ = l_Lean_stringToMessageData(v___x_3497_);
return v___x_3498_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = lean_unsigned_to_nat(1u);
v___x_3500_ = l_Lean_Expr_bvar___override(v___x_3499_);
return v___x_3500_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3503_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__5));
v___x_3504_ = lean_unsigned_to_nat(2u);
v___x_3505_ = lean_unsigned_to_nat(182u);
v___x_3506_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__4));
v___x_3507_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_3508_ = l_mkPanicMessageWithDecl(v___x_3507_, v___x_3506_, v___x_3505_, v___x_3504_, v___x_3503_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(lean_object* v_e_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_e_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; 
v_e_3518_ = l_Lean_Expr_headBeta(v_e_3509_);
v___x_3519_ = 1;
v___x_3520_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3518_, v___x_3519_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3770_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3523_ = v___x_3520_;
v_isShared_3524_ = v_isSharedCheck_3770_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3520_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3770_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
if (lean_obj_tag(v_a_3521_) == 1)
{
lean_object* v_val_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3765_; 
v_val_3525_ = lean_ctor_get(v_a_3521_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_a_3521_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3527_ = v_a_3521_;
v_isShared_3528_ = v_isSharedCheck_3765_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_val_3525_);
lean_dec(v_a_3521_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3765_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v_toMatcherInfo_3529_; lean_object* v_matcherName_3530_; lean_object* v_params_3531_; lean_object* v_motive_3532_; lean_object* v_discrs_3533_; lean_object* v_alts_3534_; lean_object* v_remaining_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; uint8_t v___x_3538_; 
v_toMatcherInfo_3529_ = lean_ctor_get(v_val_3525_, 0);
lean_inc_ref(v_toMatcherInfo_3529_);
v_matcherName_3530_ = lean_ctor_get(v_val_3525_, 1);
lean_inc(v_matcherName_3530_);
v_params_3531_ = lean_ctor_get(v_val_3525_, 3);
lean_inc_ref(v_params_3531_);
v_motive_3532_ = lean_ctor_get(v_val_3525_, 4);
lean_inc_ref(v_motive_3532_);
v_discrs_3533_ = lean_ctor_get(v_val_3525_, 5);
lean_inc_ref(v_discrs_3533_);
v_alts_3534_ = lean_ctor_get(v_val_3525_, 6);
lean_inc_ref(v_alts_3534_);
v_remaining_3535_ = lean_ctor_get(v_val_3525_, 7);
lean_inc_ref(v_remaining_3535_);
v___x_3536_ = lean_unsigned_to_nat(0u);
v___x_3537_ = lean_array_get_size(v_remaining_3535_);
v___x_3538_ = lean_nat_dec_lt(v___x_3536_, v___x_3537_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; lean_object* v___x_3541_; 
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
lean_dec(v_val_3525_);
v___x_3539_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3539_);
v___x_3541_ = v___x_3523_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
else
{
lean_object* v___x_3543_; uint8_t v___x_3544_; 
v___x_3543_ = lean_array_fget_borrowed(v_remaining_3535_, v___x_3536_);
v___x_3544_ = l_Lean_Expr_isLambda(v___x_3543_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; lean_object* v___x_3547_; 
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
lean_dec(v_val_3525_);
v___x_3545_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3545_);
v___x_3547_ = v___x_3523_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
else
{
lean_object* v___x_3549_; uint8_t v___x_3550_; 
v___x_3549_ = l_Lean_Expr_bindingBody_x21(v___x_3543_);
v___x_3550_ = l_Lean_Expr_isLambda(v___x_3549_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; lean_object* v___x_3553_; 
lean_dec_ref(v___x_3549_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
lean_dec(v_val_3525_);
v___x_3551_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3551_);
v___x_3553_ = v___x_3523_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
else
{
lean_object* v___x_3555_; uint8_t v___x_3556_; 
v___x_3555_ = l_Lean_Expr_bindingBody_x21(v___x_3549_);
lean_dec_ref(v___x_3549_);
v___x_3556_ = l_Lean_Expr_isApp(v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
lean_dec_ref(v___x_3555_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
lean_dec(v_val_3525_);
v___x_3557_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3557_);
v___x_3559_ = v___x_3523_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
else
{
uint8_t v___x_3561_; 
v___x_3561_ = lean_expr_has_loose_bvar(v___x_3555_, v___x_3536_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___y_3565_; lean_object* v___x_3628_; uint8_t v___x_3629_; 
v___x_3562_ = l_Lean_Expr_appArg_x21(v___x_3555_);
v___x_3563_ = lean_unsigned_to_nat(1u);
v___x_3628_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3);
v___x_3629_ = lean_expr_eqv(v___x_3562_, v___x_3628_);
lean_dec_ref(v___x_3562_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; lean_object* v___x_3632_; 
lean_dec_ref(v___x_3555_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
lean_dec(v_val_3525_);
v___x_3630_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3630_);
v___x_3632_ = v___x_3523_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3630_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
else
{
lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3634_ = l_Lean_Expr_appFn_x21(v___x_3555_);
lean_dec_ref(v___x_3555_);
v___x_3635_ = lean_expr_has_loose_bvar(v___x_3634_, v___x_3563_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; 
lean_del_object(v___x_3523_);
lean_inc(v_a_3516_);
lean_inc_ref(v_a_3515_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
lean_inc_ref(v___x_3634_);
v___x_3636_ = lean_infer_type(v___x_3634_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3638_; uint8_t v_transparency_3639_; uint8_t v___x_3640_; lean_object* v___y_3642_; uint8_t v___x_3733_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v___x_3638_ = l_Lean_Meta_Context_config(v_a_3513_);
v_transparency_3639_ = lean_ctor_get_uint8(v___x_3638_, 9);
v___x_3640_ = 0;
v___x_3733_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3639_, v___x_3640_);
if (v___x_3733_ == 0)
{
lean_object* v_keyedConfig_3734_; uint8_t v_trackZetaDelta_3735_; lean_object* v_zetaDeltaSet_3736_; lean_object* v_lctx_3737_; lean_object* v_localInstances_3738_; lean_object* v_defEqCtx_x3f_3739_; lean_object* v_synthPendingDepth_3740_; lean_object* v_customCanUnfoldPredicate_x3f_3741_; uint8_t v_univApprox_3742_; uint8_t v_inTypeClassResolution_3743_; uint8_t v_cacheInferType_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v_keyedConfig_3734_ = lean_ctor_get(v_a_3513_, 0);
v_trackZetaDelta_3735_ = lean_ctor_get_uint8(v_a_3513_, sizeof(void*)*7);
v_zetaDeltaSet_3736_ = lean_ctor_get(v_a_3513_, 1);
v_lctx_3737_ = lean_ctor_get(v_a_3513_, 2);
v_localInstances_3738_ = lean_ctor_get(v_a_3513_, 3);
v_defEqCtx_x3f_3739_ = lean_ctor_get(v_a_3513_, 4);
v_synthPendingDepth_3740_ = lean_ctor_get(v_a_3513_, 5);
v_customCanUnfoldPredicate_x3f_3741_ = lean_ctor_get(v_a_3513_, 6);
v_univApprox_3742_ = lean_ctor_get_uint8(v_a_3513_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3743_ = lean_ctor_get_uint8(v_a_3513_, sizeof(void*)*7 + 2);
v_cacheInferType_3744_ = lean_ctor_get_uint8(v_a_3513_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3734_);
v___x_3745_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3640_, v_keyedConfig_3734_);
lean_inc(v_customCanUnfoldPredicate_x3f_3741_);
lean_inc(v_synthPendingDepth_3740_);
lean_inc(v_defEqCtx_x3f_3739_);
lean_inc_ref(v_localInstances_3738_);
lean_inc_ref(v_lctx_3737_);
lean_inc(v_zetaDeltaSet_3736_);
v___x_3746_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
lean_ctor_set(v___x_3746_, 1, v_zetaDeltaSet_3736_);
lean_ctor_set(v___x_3746_, 2, v_lctx_3737_);
lean_ctor_set(v___x_3746_, 3, v_localInstances_3738_);
lean_ctor_set(v___x_3746_, 4, v_defEqCtx_x3f_3739_);
lean_ctor_set(v___x_3746_, 5, v_synthPendingDepth_3740_);
lean_ctor_set(v___x_3746_, 6, v_customCanUnfoldPredicate_x3f_3741_);
lean_ctor_set_uint8(v___x_3746_, sizeof(void*)*7, v_trackZetaDelta_3735_);
lean_ctor_set_uint8(v___x_3746_, sizeof(void*)*7 + 1, v_univApprox_3742_);
lean_ctor_set_uint8(v___x_3746_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3743_);
lean_ctor_set_uint8(v___x_3746_, sizeof(void*)*7 + 3, v_cacheInferType_3744_);
v___x_3747_ = l_Lean_Meta_whnfForall(v_a_3637_, v___x_3746_, v_a_3514_, v_a_3515_, v_a_3516_);
lean_dec_ref_known(v___x_3746_, 7);
v___y_3642_ = v___x_3747_;
goto v___jp_3641_;
}
else
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Lean_Meta_whnfForall(v_a_3637_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
v___y_3642_ = v___x_3748_;
goto v___jp_3641_;
}
v___jp_3641_:
{
if (lean_obj_tag(v___y_3642_) == 0)
{
lean_object* v_a_3643_; uint8_t v___x_3644_; 
v_a_3643_ = lean_ctor_get(v___y_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref_known(v___y_3642_, 1);
v___x_3644_ = l_Lean_Expr_isForall(v_a_3643_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
lean_dec(v_a_3643_);
lean_dec_ref(v___x_3638_);
lean_dec_ref(v___x_3634_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
lean_dec(v_val_3525_);
v___x_3645_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6);
v___x_3646_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v___x_3645_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
return v___x_3646_;
}
else
{
lean_object* v___x_3647_; 
v___x_3647_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_val_3525_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3716_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3716_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3716_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
if (lean_obj_tag(v_a_3648_) == 1)
{
lean_object* v_val_3652_; uint8_t v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___f_3657_; lean_object* v___x_3658_; 
lean_del_object(v___x_3650_);
v_val_3652_ = lean_ctor_get(v_a_3648_, 0);
lean_inc(v_val_3652_);
lean_dec_ref_known(v_a_3648_, 1);
v___x_3653_ = 0;
v___x_3654_ = lean_box(v___x_3653_);
v___x_3655_ = lean_box(v___x_3635_);
v___x_3656_ = lean_box(v___x_3519_);
v___f_3657_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3657_, 0, v___x_3654_);
lean_closure_set(v___f_3657_, 1, v___x_3655_);
lean_closure_set(v___f_3657_, 2, v___x_3656_);
v___x_3658_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_motive_3532_, v___f_3657_, v___x_3635_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3660_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref_known(v___x_3658_, 1);
v___x_3660_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_3530_, v_toMatcherInfo_3529_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; uint8_t v_transparency_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; size_t v_sz_3677_; size_t v___x_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v___x_3660_, 1);
v_transparency_3662_ = lean_ctor_get_uint8(v___x_3638_, 9);
lean_dec_ref(v___x_3638_);
v___x_3663_ = l_Lean_Expr_bindingDomain_x21(v_a_3643_);
v___x_3664_ = l_Lean_Expr_bindingName_x21(v_a_3643_);
v___x_3665_ = l_Lean_Expr_bindingBody_x21(v_a_3643_);
lean_dec(v_a_3643_);
lean_inc_ref(v___x_3663_);
v___x_3666_ = l_Lean_Expr_lam___override(v___x_3664_, v___x_3663_, v___x_3665_, v___x_3653_);
v___x_3667_ = lean_unsigned_to_nat(5u);
v___x_3668_ = lean_mk_empty_array_with_capacity(v___x_3667_);
v___x_3669_ = lean_array_push(v___x_3668_, v_val_3652_);
v___x_3670_ = lean_array_push(v___x_3669_, v___x_3663_);
v___x_3671_ = lean_array_push(v___x_3670_, v___x_3666_);
v___x_3672_ = lean_array_push(v___x_3671_, v___x_3634_);
v___x_3673_ = lean_array_push(v___x_3672_, v_a_3659_);
v___x_3674_ = l_Array_append___redArg(v_params_3531_, v___x_3673_);
lean_dec_ref(v___x_3673_);
v___x_3675_ = l_Array_append___redArg(v___x_3674_, v_discrs_3533_);
lean_dec_ref(v_discrs_3533_);
v___x_3676_ = l_Array_append___redArg(v___x_3675_, v_alts_3534_);
lean_dec_ref(v_alts_3534_);
v_sz_3677_ = lean_array_size(v___x_3676_);
v___x_3678_ = ((size_t)0ULL);
v___x_3679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_3677_, v___x_3678_, v___x_3676_);
v___x_3680_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3662_, v___x_3640_);
if (v___x_3680_ == 0)
{
lean_object* v_keyedConfig_3681_; uint8_t v_trackZetaDelta_3682_; lean_object* v_zetaDeltaSet_3683_; lean_object* v_lctx_3684_; lean_object* v_localInstances_3685_; lean_object* v_defEqCtx_x3f_3686_; lean_object* v_synthPendingDepth_3687_; lean_object* v_customCanUnfoldPredicate_x3f_3688_; uint8_t v_univApprox_3689_; uint8_t v_inTypeClassResolution_3690_; uint8_t v_cacheInferType_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_keyedConfig_3681_ = lean_ctor_get(v_a_3513_, 0);
v_trackZetaDelta_3682_ = lean_ctor_get_uint8(v_a_3513_, sizeof(void*)*7);
v_zetaDeltaSet_3683_ = lean_ctor_get(v_a_3513_, 1);
v_lctx_3684_ = lean_ctor_get(v_a_3513_, 2);
v_localInstances_3685_ = lean_ctor_get(v_a_3513_, 3);
v_defEqCtx_x3f_3686_ = lean_ctor_get(v_a_3513_, 4);
v_synthPendingDepth_3687_ = lean_ctor_get(v_a_3513_, 5);
v_customCanUnfoldPredicate_x3f_3688_ = lean_ctor_get(v_a_3513_, 6);
v_univApprox_3689_ = lean_ctor_get_uint8(v_a_3513_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3690_ = lean_ctor_get_uint8(v_a_3513_, sizeof(void*)*7 + 2);
v_cacheInferType_3691_ = lean_ctor_get_uint8(v_a_3513_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3681_);
v___x_3692_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3640_, v_keyedConfig_3681_);
lean_inc(v_customCanUnfoldPredicate_x3f_3688_);
lean_inc(v_synthPendingDepth_3687_);
lean_inc(v_defEqCtx_x3f_3686_);
lean_inc_ref(v_localInstances_3685_);
lean_inc_ref(v_lctx_3684_);
lean_inc(v_zetaDeltaSet_3683_);
v___x_3693_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
lean_ctor_set(v___x_3693_, 1, v_zetaDeltaSet_3683_);
lean_ctor_set(v___x_3693_, 2, v_lctx_3684_);
lean_ctor_set(v___x_3693_, 3, v_localInstances_3685_);
lean_ctor_set(v___x_3693_, 4, v_defEqCtx_x3f_3686_);
lean_ctor_set(v___x_3693_, 5, v_synthPendingDepth_3687_);
lean_ctor_set(v___x_3693_, 6, v_customCanUnfoldPredicate_x3f_3688_);
lean_ctor_set_uint8(v___x_3693_, sizeof(void*)*7, v_trackZetaDelta_3682_);
lean_ctor_set_uint8(v___x_3693_, sizeof(void*)*7 + 1, v_univApprox_3689_);
lean_ctor_set_uint8(v___x_3693_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3690_);
lean_ctor_set_uint8(v___x_3693_, sizeof(void*)*7 + 3, v_cacheInferType_3691_);
v___x_3694_ = l_Lean_Meta_mkAppOptM(v_a_3661_, v___x_3679_, v___x_3693_, v_a_3514_, v_a_3515_, v_a_3516_);
lean_dec_ref_known(v___x_3693_, 7);
v___y_3565_ = v___x_3694_;
goto v___jp_3564_;
}
else
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Lean_Meta_mkAppOptM(v_a_3661_, v___x_3679_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
v___y_3565_ = v___x_3695_;
goto v___jp_3564_;
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v_a_3659_);
lean_dec(v_val_3652_);
lean_dec(v_a_3643_);
lean_dec_ref(v___x_3638_);
lean_dec_ref(v___x_3634_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_params_3531_);
lean_del_object(v___x_3527_);
v_a_3696_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3660_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3660_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v_val_3652_);
lean_dec(v_a_3643_);
lean_dec_ref(v___x_3638_);
lean_dec_ref(v___x_3634_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
v_a_3704_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3658_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3658_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v___x_3712_; lean_object* v___x_3714_; 
lean_dec(v_a_3648_);
lean_dec(v_a_3643_);
lean_dec_ref(v___x_3638_);
lean_dec_ref(v___x_3634_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
v___x_3712_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3712_);
v___x_3714_ = v___x_3650_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3712_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec(v_a_3643_);
lean_dec_ref(v___x_3638_);
lean_dec_ref(v___x_3634_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
v_a_3717_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3647_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3647_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec_ref(v___x_3638_);
lean_dec_ref(v___x_3634_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
lean_dec(v_val_3525_);
v_a_3725_ = lean_ctor_get(v___y_3642_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___y_3642_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___y_3642_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___y_3642_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec_ref(v___x_3634_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
lean_dec(v_val_3525_);
v_a_3749_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3636_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3636_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3759_; 
lean_dec_ref(v___x_3634_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
lean_dec(v_val_3525_);
v___x_3757_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3757_);
v___x_3759_ = v___x_3523_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
v___jp_3564_:
{
if (lean_obj_tag(v___y_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3567_; 
v_a_3566_ = lean_ctor_get(v___y_3565_, 0);
lean_inc_n(v_a_3566_, 2);
lean_dec_ref_known(v___y_3565_, 1);
lean_inc(v_a_3516_);
lean_inc_ref(v_a_3515_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
v___x_3567_ = lean_infer_type(v_a_3566_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v___x_3569_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_3570_ = lean_unsigned_to_nat(3u);
v___x_3571_ = l_Lean_Expr_isAppOfArity(v_a_3568_, v___x_3569_, v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; 
lean_dec(v_a_3568_);
lean_dec_ref(v_remaining_3535_);
lean_del_object(v___x_3527_);
lean_inc(v_a_3516_);
lean_inc_ref(v_a_3515_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
v___x_3572_ = lean_infer_type(v_a_3566_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v___x_3572_, 1);
v___x_3574_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2);
v___x_3575_ = l_Lean_indentExpr(v_a_3573_);
v___x_3576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3574_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v___x_3576_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
return v___x_3577_;
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
v_a_3578_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3572_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3572_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3586_ = l_Lean_Expr_appArg_x21(v_a_3568_);
lean_dec(v_a_3568_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v_a_3566_);
v___x_3588_ = v___x_3527_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3566_);
v___x_3588_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3589_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3589_, 0, v___x_3586_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
lean_ctor_set_uint8(v___x_3589_, sizeof(void*)*2, v___x_3519_);
v___x_3590_ = l_Array_toSubarray___redArg(v_remaining_3535_, v___x_3563_, v___x_3537_);
v___x_3591_ = l_Subarray_copy___redArg(v___x_3590_);
v___x_3592_ = l_Lean_Meta_Simp_Result_addExtraArgs(v___x_3589_, v___x_3591_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
lean_dec_ref(v___x_3591_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3602_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3595_ = v___x_3592_;
v_isShared_3596_ = v_isSharedCheck_3602_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3592_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3602_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3600_; 
v___x_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3597_, 0, v_a_3593_);
v___x_3598_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 0, v___x_3598_);
v___x_3600_ = v___x_3595_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
v_a_3603_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3592_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3592_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v_a_3566_);
lean_dec_ref(v_remaining_3535_);
lean_del_object(v___x_3527_);
v_a_3612_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3567_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3567_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec_ref(v_remaining_3535_);
lean_del_object(v___x_3527_);
v_a_3620_ = lean_ctor_get(v___y_3565_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___y_3565_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___y_3565_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___y_3565_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
else
{
lean_object* v___x_3761_; lean_object* v___x_3763_; 
lean_dec_ref(v___x_3555_);
lean_dec_ref(v_remaining_3535_);
lean_dec_ref(v_alts_3534_);
lean_dec_ref(v_discrs_3533_);
lean_dec_ref(v_motive_3532_);
lean_dec_ref(v_params_3531_);
lean_dec(v_matcherName_3530_);
lean_dec_ref(v_toMatcherInfo_3529_);
lean_del_object(v___x_3527_);
lean_dec(v_val_3525_);
v___x_3761_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3761_);
v___x_3763_ = v___x_3523_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3761_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
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
lean_object* v___x_3766_; lean_object* v___x_3768_; 
lean_dec(v_a_3521_);
v___x_3766_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3766_);
v___x_3768_ = v___x_3523_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
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
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
v_a_3771_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3520_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3520_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed(lean_object* v_e_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(v_e_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_);
lean_dec(v_a_3786_);
lean_dec_ref(v_a_3785_);
lean_dec(v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(lean_object* v_declName_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3789_, v___y_3796_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___boxed(lean_object* v_declName_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(v_declName_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(lean_object* v_00_u03b1_3809_, lean_object* v_msg_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v___x_3819_; 
v___x_3819_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_3810_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___boxed(lean_object* v_00_u03b1_3820_, lean_object* v_msg_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(v_00_u03b1_3820_, v_msg_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3831_, lean_object* v_constName_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3842_, lean_object* v_constName_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(v_00_u03b1_3842_, v_constName_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b1_3853_, lean_object* v_ref_3854_, lean_object* v_constName_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3854_, v_constName_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b1_3865_, lean_object* v_ref_3866_, lean_object* v_constName_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(v_00_u03b1_3865_, v_ref_3866_, v_constName_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec(v_ref_3866_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3877_, lean_object* v_ref_3878_, lean_object* v_msg_3879_, lean_object* v_declHint_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3878_, v_msg_3879_, v_declHint_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3890_, lean_object* v_ref_3891_, lean_object* v_msg_3892_, lean_object* v_declHint_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_3890_, v_ref_3891_, v_msg_3892_, v_declHint_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec(v_ref_3891_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_3903_, lean_object* v_declHint_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3903_, v_declHint_3904_, v___y_3911_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_3914_, lean_object* v_declHint_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(v_msg_3914_, v_declHint_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(lean_object* v_00_u03b1_3925_, lean_object* v_ref_3926_, lean_object* v_msg_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3926_, v_msg_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___boxed(lean_object* v_00_u03b1_3937_, lean_object* v_ref_3938_, lean_object* v_msg_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(v_00_u03b1_3937_, v_ref_3938_, v_msg_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec(v_ref_3938_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3994_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_3995_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_3996_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed), 9, 0);
v___x_3997_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3994_, v___x_3995_, v___x_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10____boxed(lean_object* v_a_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_();
return v_res_3999_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0(void){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4000_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0);
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
return v___x_4002_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2(void){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4003_ = lean_unsigned_to_nat(32u);
v___x_4004_ = lean_mk_empty_array_with_capacity(v___x_4003_);
v___x_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
return v___x_4005_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__4(void){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3));
v___x_4008_ = l_Lean_stringToMessageData(v___x_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(lean_object* v___x_4009_, lean_object* v___x_4010_, lean_object* v___x_4011_, lean_object* v___x_4012_, lean_object* v___x_4013_, uint8_t v___x_4014_, lean_object* v_mvarId_4015_, uint8_t v___x_4016_, lean_object* v_declName_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_4009_, v___x_4010_, v___x_4011_, v___x_4012_, v___y_4018_, v___y_4020_, v___y_4021_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4023_, 1);
v___x_4025_ = lean_mk_empty_array_with_capacity(v___x_4013_);
v___x_4026_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4027_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4028_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4029_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
lean_inc(v___x_4013_);
v___x_4030_ = l_Lean_Name_num___override(v___x_4029_, v___x_4013_);
v___x_4031_ = l_Lean_Name_str___override(v___x_4030_, v___x_4026_);
v___x_4032_ = l_Lean_Name_str___override(v___x_4031_, v___x_4027_);
v___x_4033_ = l_Lean_Name_str___override(v___x_4032_, v___x_4028_);
v___x_4034_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4035_ = l_Lean_Name_str___override(v___x_4033_, v___x_4034_);
v___x_4036_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_4025_, v___x_4035_, v___x_4014_, v___y_4020_, v___y_4021_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; size_t v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4036_, 1);
v___x_4038_ = lean_box(0);
v___x_4039_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1);
lean_inc_n(v___x_4013_, 2);
v___x_4040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4039_);
lean_ctor_set(v___x_4040_, 1, v___x_4013_);
v___x_4041_ = lean_unsigned_to_nat(32u);
v___x_4042_ = lean_mk_empty_array_with_capacity(v___x_4041_);
v___x_4043_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2);
v___x_4044_ = ((size_t)5ULL);
v___x_4045_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set(v___x_4045_, 1, v___x_4042_);
lean_ctor_set(v___x_4045_, 2, v___x_4013_);
lean_ctor_set(v___x_4045_, 3, v___x_4013_);
lean_ctor_set_usize(v___x_4045_, 4, v___x_4044_);
v___x_4046_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4039_);
lean_ctor_set(v___x_4046_, 1, v___x_4039_);
lean_ctor_set(v___x_4046_, 2, v___x_4039_);
lean_ctor_set(v___x_4046_, 3, v___x_4045_);
v___x_4047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4040_);
lean_ctor_set(v___x_4047_, 1, v___x_4046_);
v___x_4048_ = l_Lean_Meta_simpTarget(v_mvarId_4015_, v_a_4024_, v_a_4037_, v___x_4038_, v___x_4016_, v___x_4047_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4091_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4051_ = v___x_4048_;
v_isShared_4052_ = v_isSharedCheck_4091_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4048_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4091_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v_fst_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4089_; 
v_fst_4053_ = lean_ctor_get(v_a_4049_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_a_4049_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; 
v_unused_4090_ = lean_ctor_get(v_a_4049_, 1);
lean_dec(v_unused_4090_);
v___x_4055_ = v_a_4049_;
v_isShared_4056_ = v_isSharedCheck_4089_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_fst_4053_);
lean_dec(v_a_4049_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4089_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
if (lean_obj_tag(v_fst_4053_) == 0)
{
lean_object* v___x_4057_; lean_object* v___x_4059_; 
lean_del_object(v___x_4055_);
lean_dec(v_declName_4017_);
v___x_4057_ = lean_box(0);
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 0, v___x_4057_);
v___x_4059_ = v___x_4051_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
else
{
lean_object* v_val_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4065_; 
lean_del_object(v___x_4051_);
v_val_4061_ = lean_ctor_get(v_fst_4053_, 0);
lean_inc(v_val_4061_);
lean_dec_ref_known(v_fst_4053_, 1);
v___x_4062_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__4);
v___x_4063_ = l_Lean_MessageData_ofConstName(v_declName_4017_, v___x_4014_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set_tag(v___x_4055_, 7);
lean_ctor_set(v___x_4055_, 1, v___x_4063_);
lean_ctor_set(v___x_4055_, 0, v___x_4062_);
v___x_4065_ = v___x_4055_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___f_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4066_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_4067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4065_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___f_4068_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4068_, 0, v___x_4067_);
v___x_4069_ = lean_box(v___x_4016_);
v___x_4070_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___boxed), 7, 2);
lean_closure_set(v___x_4070_, 0, v_val_4061_);
lean_closure_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4070_, v___f_4068_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4079_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4074_ = v___x_4071_;
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4071_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4075_ == 0)
{
v___x_4077_ = v___x_4074_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4072_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
else
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
v_a_4080_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4082_ = v___x_4071_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4071_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4080_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
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
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec(v_declName_4017_);
v_a_4092_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4048_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4048_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec(v_a_4024_);
lean_dec(v_declName_4017_);
lean_dec(v_mvarId_4015_);
lean_dec(v___x_4013_);
v_a_4100_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4036_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4036_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v_declName_4017_);
lean_dec(v_mvarId_4015_);
lean_dec(v___x_4013_);
v_a_4108_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4023_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4023_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___boxed(lean_object* v___x_4116_, lean_object* v___x_4117_, lean_object* v___x_4118_, lean_object* v___x_4119_, lean_object* v___x_4120_, lean_object* v___x_4121_, lean_object* v_mvarId_4122_, lean_object* v___x_4123_, lean_object* v_declName_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
uint8_t v___x_1408__boxed_4130_; uint8_t v___x_1409__boxed_4131_; lean_object* v_res_4132_; 
v___x_1408__boxed_4130_ = lean_unbox(v___x_4121_);
v___x_1409__boxed_4131_ = lean_unbox(v___x_4123_);
v_res_4132_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4116_, v___x_4117_, v___x_4118_, v___x_4119_, v___x_4120_, v___x_1408__boxed_4130_, v_mvarId_4122_, v___x_1409__boxed_4131_, v_declName_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
return v_res_4132_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2(void){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4142_ = lean_box(0);
v___x_4143_ = lean_unsigned_to_nat(16u);
v___x_4144_ = lean_mk_array(v___x_4143_, v___x_4142_);
return v___x_4144_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3(void){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4145_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2);
v___x_4146_ = lean_unsigned_to_nat(0u);
v___x_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
lean_ctor_set(v___x_4147_, 1, v___x_4145_);
return v___x_4147_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4(void){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4148_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5(void){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4);
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
return v___x_4150_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6(void){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; lean_object* v___x_4154_; 
v___x_4151_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4152_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3);
v___x_4153_ = 1;
v___x_4154_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4154_, 0, v___x_4152_);
lean_ctor_set(v___x_4154_, 1, v___x_4151_);
lean_ctor_set_uint8(v___x_4154_, sizeof(void*)*2, v___x_4153_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object* v_declName_4155_, lean_object* v_mvarId_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_){
_start:
{
lean_object* v___y_4163_; uint8_t v___x_4180_; uint8_t v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; uint8_t v_transparency_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; uint8_t v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v___x_4180_ = 0;
v___x_4181_ = 1;
v___x_4182_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0));
v___x_4183_ = l_Lean_Meta_Context_config(v_a_4157_);
v_transparency_4184_ = lean_ctor_get_uint8(v___x_4183_, 9);
lean_dec_ref(v___x_4183_);
v___x_4185_ = lean_unsigned_to_nat(0u);
v___x_4186_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1));
v___x_4187_ = 0;
v___x_4188_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6);
v___x_4189_ = l_Lean_Options_empty;
v___x_4190_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4184_, v___x_4187_);
if (v___x_4190_ == 0)
{
lean_object* v_keyedConfig_4191_; uint8_t v_trackZetaDelta_4192_; lean_object* v_zetaDeltaSet_4193_; lean_object* v_lctx_4194_; lean_object* v_localInstances_4195_; lean_object* v_defEqCtx_x3f_4196_; lean_object* v_synthPendingDepth_4197_; lean_object* v_customCanUnfoldPredicate_x3f_4198_; uint8_t v_univApprox_4199_; uint8_t v_inTypeClassResolution_4200_; uint8_t v_cacheInferType_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v_keyedConfig_4191_ = lean_ctor_get(v_a_4157_, 0);
v_trackZetaDelta_4192_ = lean_ctor_get_uint8(v_a_4157_, sizeof(void*)*7);
v_zetaDeltaSet_4193_ = lean_ctor_get(v_a_4157_, 1);
v_lctx_4194_ = lean_ctor_get(v_a_4157_, 2);
v_localInstances_4195_ = lean_ctor_get(v_a_4157_, 3);
v_defEqCtx_x3f_4196_ = lean_ctor_get(v_a_4157_, 4);
v_synthPendingDepth_4197_ = lean_ctor_get(v_a_4157_, 5);
v_customCanUnfoldPredicate_x3f_4198_ = lean_ctor_get(v_a_4157_, 6);
v_univApprox_4199_ = lean_ctor_get_uint8(v_a_4157_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4200_ = lean_ctor_get_uint8(v_a_4157_, sizeof(void*)*7 + 2);
v_cacheInferType_4201_ = lean_ctor_get_uint8(v_a_4157_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4191_);
v___x_4202_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4187_, v_keyedConfig_4191_);
lean_inc(v_customCanUnfoldPredicate_x3f_4198_);
lean_inc(v_synthPendingDepth_4197_);
lean_inc(v_defEqCtx_x3f_4196_);
lean_inc_ref(v_localInstances_4195_);
lean_inc_ref(v_lctx_4194_);
lean_inc(v_zetaDeltaSet_4193_);
v___x_4203_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
lean_ctor_set(v___x_4203_, 1, v_zetaDeltaSet_4193_);
lean_ctor_set(v___x_4203_, 2, v_lctx_4194_);
lean_ctor_set(v___x_4203_, 3, v_localInstances_4195_);
lean_ctor_set(v___x_4203_, 4, v_defEqCtx_x3f_4196_);
lean_ctor_set(v___x_4203_, 5, v_synthPendingDepth_4197_);
lean_ctor_set(v___x_4203_, 6, v_customCanUnfoldPredicate_x3f_4198_);
lean_ctor_set_uint8(v___x_4203_, sizeof(void*)*7, v_trackZetaDelta_4192_);
lean_ctor_set_uint8(v___x_4203_, sizeof(void*)*7 + 1, v_univApprox_4199_);
lean_ctor_set_uint8(v___x_4203_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4200_);
lean_ctor_set_uint8(v___x_4203_, sizeof(void*)*7 + 3, v_cacheInferType_4201_);
v___x_4204_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4182_, v___x_4186_, v___x_4188_, v___x_4189_, v___x_4185_, v___x_4180_, v_mvarId_4156_, v___x_4181_, v_declName_4155_, v___x_4203_, v_a_4158_, v_a_4159_, v_a_4160_);
lean_dec_ref_known(v___x_4203_, 7);
v___y_4163_ = v___x_4204_;
goto v___jp_4162_;
}
else
{
lean_object* v___x_4205_; 
v___x_4205_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4182_, v___x_4186_, v___x_4188_, v___x_4189_, v___x_4185_, v___x_4180_, v_mvarId_4156_, v___x_4181_, v_declName_4155_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_);
v___y_4163_ = v___x_4205_;
goto v___jp_4162_;
}
v___jp_4162_:
{
if (lean_obj_tag(v___y_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
v_a_4164_ = lean_ctor_get(v___y_4163_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___y_4163_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___y_4163_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___y_4163_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
v_a_4172_ = lean_ctor_get(v___y_4163_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___y_4163_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___y_4163_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___y_4163_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___boxed(lean_object* v_declName_4206_, lean_object* v_mvarId_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4206_, v_mvarId_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(lean_object* v_e_4214_, lean_object* v_k_4215_, uint8_t v_cleanupAnnotations_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v___f_4222_; uint8_t v___x_4223_; uint8_t v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___f_4222_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4222_, 0, v_k_4215_);
v___x_4223_ = 1;
v___x_4224_ = 0;
v___x_4225_ = lean_box(0);
v___x_4226_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4214_, v___x_4223_, v___x_4224_, v___x_4223_, v___x_4224_, v___x_4225_, v___f_4222_, v_cleanupAnnotations_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4226_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4226_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
v_a_4235_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4226_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4226_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg___boxed(lean_object* v_e_4243_, lean_object* v_k_4244_, lean_object* v_cleanupAnnotations_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4251_; lean_object* v_res_4252_; 
v_cleanupAnnotations_boxed_4251_ = lean_unbox(v_cleanupAnnotations_4245_);
v_res_4252_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4243_, v_k_4244_, v_cleanupAnnotations_boxed_4251_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_object* v_00_u03b1_4253_, lean_object* v_e_4254_, lean_object* v_k_4255_, uint8_t v_cleanupAnnotations_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v___x_4262_; 
v___x_4262_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4254_, v_k_4255_, v_cleanupAnnotations_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed(lean_object* v_00_u03b1_4263_, lean_object* v_e_4264_, lean_object* v_k_4265_, lean_object* v_cleanupAnnotations_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4272_; lean_object* v_res_4273_; 
v_cleanupAnnotations_boxed_4272_ = lean_unbox(v_cleanupAnnotations_4266_);
v_res_4273_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(v_00_u03b1_4263_, v_e_4264_, v_k_4265_, v_cleanupAnnotations_boxed_4272_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
return v_res_4273_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object* v_opts_4274_, lean_object* v_opt_4275_){
_start:
{
lean_object* v_name_4276_; lean_object* v_defValue_4277_; lean_object* v_map_4278_; lean_object* v___x_4279_; 
v_name_4276_ = lean_ctor_get(v_opt_4275_, 0);
v_defValue_4277_ = lean_ctor_get(v_opt_4275_, 1);
v_map_4278_ = lean_ctor_get(v_opts_4274_, 0);
v___x_4279_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4278_, v_name_4276_);
if (lean_obj_tag(v___x_4279_) == 0)
{
uint8_t v___x_4280_; 
v___x_4280_ = lean_unbox(v_defValue_4277_);
return v___x_4280_;
}
else
{
lean_object* v_val_4281_; 
v_val_4281_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_val_4281_);
lean_dec_ref_known(v___x_4279_, 1);
if (lean_obj_tag(v_val_4281_) == 1)
{
uint8_t v_v_4282_; 
v_v_4282_ = lean_ctor_get_uint8(v_val_4281_, 0);
lean_dec_ref_known(v_val_4281_, 0);
return v_v_4282_;
}
else
{
uint8_t v___x_4283_; 
lean_dec(v_val_4281_);
v___x_4283_ = lean_unbox(v_defValue_4277_);
return v___x_4283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object* v_opts_4284_, lean_object* v_opt_4285_){
_start:
{
uint8_t v_res_4286_; lean_object* v_r_4287_; 
v_res_4286_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v_opts_4284_, v_opt_4285_);
lean_dec_ref(v_opt_4285_);
lean_dec_ref(v_opts_4284_);
v_r_4287_ = lean_box(v_res_4286_);
return v_r_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(lean_object* v_opts_4288_, lean_object* v_opt_4289_){
_start:
{
lean_object* v_name_4290_; lean_object* v_defValue_4291_; lean_object* v_map_4292_; lean_object* v___x_4293_; 
v_name_4290_ = lean_ctor_get(v_opt_4289_, 0);
v_defValue_4291_ = lean_ctor_get(v_opt_4289_, 1);
v_map_4292_ = lean_ctor_get(v_opts_4288_, 0);
v___x_4293_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4292_, v_name_4290_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_inc(v_defValue_4291_);
return v_defValue_4291_;
}
else
{
lean_object* v_val_4294_; 
v_val_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_val_4294_);
lean_dec_ref_known(v___x_4293_, 1);
if (lean_obj_tag(v_val_4294_) == 3)
{
lean_object* v_v_4295_; 
v_v_4295_ = lean_ctor_get(v_val_4294_, 0);
lean_inc(v_v_4295_);
lean_dec_ref_known(v_val_4294_, 1);
return v_v_4295_;
}
else
{
lean_dec(v_val_4294_);
lean_inc(v_defValue_4291_);
return v_defValue_4291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4___boxed(lean_object* v_opts_4296_, lean_object* v_opt_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_opts_4296_, v_opt_4297_);
lean_dec_ref(v_opt_4297_);
lean_dec_ref(v_opts_4296_);
return v_res_4298_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4299_; double v___x_4300_; 
v___x_4299_ = lean_unsigned_to_nat(0u);
v___x_4300_ = lean_float_of_nat(v___x_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(lean_object* v_cls_4304_, lean_object* v_msg_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v_ref_4311_; lean_object* v___x_4312_; lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4357_; 
v_ref_4311_ = lean_ctor_get(v___y_4308_, 2);
v___x_4312_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4315_ = v___x_4312_;
v_isShared_4316_ = v_isSharedCheck_4357_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4312_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4357_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4317_; lean_object* v_traceState_4318_; lean_object* v_env_4319_; lean_object* v_nextMacroScope_4320_; lean_object* v_ngen_4321_; lean_object* v_auxDeclNGen_4322_; lean_object* v_cache_4323_; lean_object* v_messages_4324_; lean_object* v_infoState_4325_; lean_object* v_snapshotTasks_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4356_; 
v___x_4317_ = lean_st_ref_take(v___y_4309_);
v_traceState_4318_ = lean_ctor_get(v___x_4317_, 4);
v_env_4319_ = lean_ctor_get(v___x_4317_, 0);
v_nextMacroScope_4320_ = lean_ctor_get(v___x_4317_, 1);
v_ngen_4321_ = lean_ctor_get(v___x_4317_, 2);
v_auxDeclNGen_4322_ = lean_ctor_get(v___x_4317_, 3);
v_cache_4323_ = lean_ctor_get(v___x_4317_, 5);
v_messages_4324_ = lean_ctor_get(v___x_4317_, 6);
v_infoState_4325_ = lean_ctor_get(v___x_4317_, 7);
v_snapshotTasks_4326_ = lean_ctor_get(v___x_4317_, 8);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4328_ = v___x_4317_;
v_isShared_4329_ = v_isSharedCheck_4356_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_snapshotTasks_4326_);
lean_inc(v_infoState_4325_);
lean_inc(v_messages_4324_);
lean_inc(v_cache_4323_);
lean_inc(v_traceState_4318_);
lean_inc(v_auxDeclNGen_4322_);
lean_inc(v_ngen_4321_);
lean_inc(v_nextMacroScope_4320_);
lean_inc(v_env_4319_);
lean_dec(v___x_4317_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4356_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
uint64_t v_tid_4330_; lean_object* v_traces_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4355_; 
v_tid_4330_ = lean_ctor_get_uint64(v_traceState_4318_, sizeof(void*)*1);
v_traces_4331_ = lean_ctor_get(v_traceState_4318_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v_traceState_4318_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4333_ = v_traceState_4318_;
v_isShared_4334_ = v_isSharedCheck_4355_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_traces_4331_);
lean_dec(v_traceState_4318_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4355_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4335_; double v___x_4336_; uint8_t v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4345_; 
v___x_4335_ = lean_box(0);
v___x_4336_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0);
v___x_4337_ = 0;
v___x_4338_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__1));
v___x_4339_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4339_, 0, v_cls_4304_);
lean_ctor_set(v___x_4339_, 1, v___x_4335_);
lean_ctor_set(v___x_4339_, 2, v___x_4338_);
lean_ctor_set_float(v___x_4339_, sizeof(void*)*3, v___x_4336_);
lean_ctor_set_float(v___x_4339_, sizeof(void*)*3 + 8, v___x_4336_);
lean_ctor_set_uint8(v___x_4339_, sizeof(void*)*3 + 16, v___x_4337_);
v___x_4340_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__2));
v___x_4341_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4339_);
lean_ctor_set(v___x_4341_, 1, v_a_4313_);
lean_ctor_set(v___x_4341_, 2, v___x_4340_);
lean_inc(v_ref_4311_);
v___x_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4342_, 0, v_ref_4311_);
lean_ctor_set(v___x_4342_, 1, v___x_4341_);
v___x_4343_ = l_Lean_PersistentArray_push___redArg(v_traces_4331_, v___x_4342_);
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 0, v___x_4343_);
v___x_4345_ = v___x_4333_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4343_);
lean_ctor_set_uint64(v_reuseFailAlloc_4354_, sizeof(void*)*1, v_tid_4330_);
v___x_4345_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
lean_object* v___x_4347_; 
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 4, v___x_4345_);
v___x_4347_ = v___x_4328_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_env_4319_);
lean_ctor_set(v_reuseFailAlloc_4353_, 1, v_nextMacroScope_4320_);
lean_ctor_set(v_reuseFailAlloc_4353_, 2, v_ngen_4321_);
lean_ctor_set(v_reuseFailAlloc_4353_, 3, v_auxDeclNGen_4322_);
lean_ctor_set(v_reuseFailAlloc_4353_, 4, v___x_4345_);
lean_ctor_set(v_reuseFailAlloc_4353_, 5, v_cache_4323_);
lean_ctor_set(v_reuseFailAlloc_4353_, 6, v_messages_4324_);
lean_ctor_set(v_reuseFailAlloc_4353_, 7, v_infoState_4325_);
lean_ctor_set(v_reuseFailAlloc_4353_, 8, v_snapshotTasks_4326_);
v___x_4347_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4351_; 
v___x_4348_ = lean_st_ref_put(v___y_4309_, v___x_4347_);
v___x_4349_ = lean_box(0);
if (v_isShared_4316_ == 0)
{
lean_ctor_set(v___x_4315_, 0, v___x_4349_);
v___x_4351_ = v___x_4315_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4349_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___boxed(lean_object* v_cls_4358_, lean_object* v_msg_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v_cls_4358_, v_msg_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
return v_res_4365_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4375_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4376_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4377_ = l_Lean_Name_append(v___x_4376_, v___x_4375_);
return v___x_4377_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__6));
v___x_4380_ = l_Lean_stringToMessageData(v___x_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object* v_levelParams_4381_, lean_object* v_declName_4382_, lean_object* v_wfPreprocessProof_4383_, lean_object* v___x_4384_, lean_object* v_unaryPreDefName_4385_, lean_object* v_xs_4386_, lean_object* v_body_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4396_ = lean_box(0);
lean_inc(v_levelParams_4381_);
v___x_4397_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4381_, v___x_4396_);
lean_inc(v_declName_4382_);
v___x_4398_ = l_Lean_mkConst(v_declName_4382_, v___x_4397_);
v___x_4399_ = l_Lean_mkAppN(v___x_4398_, v_xs_4386_);
v___x_4400_ = l_Lean_Meta_mkEq(v___x_4399_, v_body_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc_n(v_a_4401_, 2);
lean_dec_ref_known(v___x_4400_, 1);
v___x_4402_ = lean_box(0);
v___x_4403_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4401_, v___x_4402_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4405_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v___x_4405_ = l_Lean_Meta_Simp_Result_addExtraArgs(v_wfPreprocessProof_4383_, v_xs_4386_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; uint8_t v___x_4409_; lean_object* v_mvarId_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref_known(v___x_4405_, 1);
v___x_4407_ = l_Lean_Expr_appFn_x21(v_a_4401_);
v___x_4408_ = lean_box(0);
v___x_4409_ = 1;
v___x_4484_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4484_, 0, v___x_4407_);
lean_ctor_set(v___x_4484_, 1, v___x_4408_);
lean_ctor_set_uint8(v___x_4484_, sizeof(void*)*2, v___x_4409_);
v___x_4485_ = l_Lean_Meta_Simp_mkCongr(v___x_4484_, v_a_4406_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4485_, 1);
v___x_4487_ = l_Lean_Expr_mvarId_x21(v_a_4404_);
v___x_4488_ = l_Lean_Meta_applySimpResultToTarget(v___x_4487_, v_a_4401_, v_a_4486_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; uint8_t v___x_4490_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4488_, 1);
v___x_4490_ = lean_name_eq(v_declName_4382_, v_unaryPreDefName_4385_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; 
v___x_4491_ = l_Lean_Elab_Eqns_deltaLHS(v_a_4489_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v___x_4491_, 1);
v_mvarId_4411_ = v_a_4492_;
v___y_4412_ = v___y_4388_;
v___y_4413_ = v___y_4389_;
v___y_4414_ = v___y_4390_;
v___y_4415_ = v___y_4391_;
goto v___jp_4410_;
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
lean_dec(v_a_4404_);
lean_dec(v_a_4401_);
lean_dec(v___x_4384_);
lean_dec(v_declName_4382_);
lean_dec(v_levelParams_4381_);
v_a_4493_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4495_ = v___x_4491_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4491_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_a_4493_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
}
else
{
v_mvarId_4411_ = v_a_4489_;
v___y_4412_ = v___y_4388_;
v___y_4413_ = v___y_4389_;
v___y_4414_ = v___y_4390_;
v___y_4415_ = v___y_4391_;
goto v___jp_4410_;
}
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_dec(v_a_4404_);
lean_dec(v_a_4401_);
lean_dec(v___x_4384_);
lean_dec(v_declName_4382_);
lean_dec(v_levelParams_4381_);
v_a_4501_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4488_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4488_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
lean_dec(v_a_4404_);
lean_dec(v_a_4401_);
lean_dec(v___x_4384_);
lean_dec(v_declName_4382_);
lean_dec(v_levelParams_4381_);
v_a_4509_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4485_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4485_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
v___jp_4410_:
{
lean_object* v___x_4416_; 
v___x_4416_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; lean_object* v___x_4418_; 
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4417_);
lean_dec_ref_known(v___x_4416_, 1);
v___x_4418_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4382_, v_a_4417_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v___x_4419_; lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4475_; 
lean_dec_ref_known(v___x_4418_, 1);
v___x_4419_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4404_, v___y_4413_);
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4422_ = v___x_4419_;
v_isShared_4423_ = v_isSharedCheck_4475_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4419_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4475_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
uint8_t v___x_4424_; uint8_t v___x_4425_; lean_object* v___x_4426_; 
v___x_4424_ = 0;
v___x_4425_ = 1;
v___x_4426_ = l_Lean_Meta_mkForallFVars(v_xs_4386_, v_a_4401_, v___x_4424_, v___x_4409_, v___x_4409_, v___x_4425_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4428_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
lean_dec_ref_known(v___x_4426_, 1);
v___x_4428_ = l_Lean_Meta_letToHave(v_a_4427_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v_a_4429_; lean_object* v___x_4430_; 
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
lean_inc(v_a_4429_);
lean_dec_ref_known(v___x_4428_, 1);
v___x_4430_ = l_Lean_Meta_mkLambdaFVars(v_xs_4386_, v_a_4420_, v___x_4424_, v___x_4409_, v___x_4424_, v___x_4409_, v___x_4425_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4436_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc(v_a_4431_);
lean_dec_ref_known(v___x_4430_, 1);
lean_inc_n(v___x_4384_, 2);
v___x_4432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4384_);
lean_ctor_set(v___x_4432_, 1, v_levelParams_4381_);
lean_ctor_set(v___x_4432_, 2, v_a_4429_);
v___x_4433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4384_);
lean_ctor_set(v___x_4433_, 1, v___x_4396_);
v___x_4434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4432_);
lean_ctor_set(v___x_4434_, 1, v_a_4431_);
lean_ctor_set(v___x_4434_, 2, v___x_4433_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set_tag(v___x_4422_, 2);
lean_ctor_set(v___x_4422_, 0, v___x_4434_);
v___x_4436_ = v___x_4422_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4434_);
v___x_4436_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4437_; 
v___x_4437_ = l_Lean_addDecl(v___x_4436_, v___x_4424_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v___x_4438_; 
lean_dec_ref_known(v___x_4437_, 1);
lean_inc(v___x_4384_);
v___x_4438_ = l_Lean_inferDefEqAttr(v___x_4384_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_toCold_4439_; lean_object* v_options_4440_; uint8_t v_hasTrace_4441_; 
lean_dec_ref_known(v___x_4438_, 1);
v_toCold_4439_ = lean_ctor_get(v___y_4414_, 0);
v_options_4440_ = lean_ctor_get(v_toCold_4439_, 2);
v_hasTrace_4441_ = lean_ctor_get_uint8(v_options_4440_, sizeof(void*)*1);
if (v_hasTrace_4441_ == 0)
{
lean_dec(v___x_4384_);
goto v___jp_4393_;
}
else
{
lean_object* v_inheritedTraceOptions_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; uint8_t v___x_4445_; 
v_inheritedTraceOptions_4442_ = lean_ctor_get(v_toCold_4439_, 11);
v___x_4443_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4444_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_4445_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4442_, v_options_4440_, v___x_4444_);
if (v___x_4445_ == 0)
{
lean_dec(v___x_4384_);
goto v___jp_4393_;
}
else
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4446_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7);
v___x_4447_ = l_Lean_MessageData_ofConstName(v___x_4384_, v___x_4424_);
v___x_4448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4446_);
lean_ctor_set(v___x_4448_, 1, v___x_4447_);
v___x_4449_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_4443_, v___x_4448_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
return v___x_4449_;
}
}
}
else
{
lean_dec(v___x_4384_);
return v___x_4438_;
}
}
else
{
lean_dec(v___x_4384_);
return v___x_4437_;
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec(v_a_4429_);
lean_del_object(v___x_4422_);
lean_dec(v___x_4384_);
lean_dec(v_levelParams_4381_);
v_a_4451_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4430_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4430_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_del_object(v___x_4422_);
lean_dec(v_a_4420_);
lean_dec(v___x_4384_);
lean_dec(v_levelParams_4381_);
v_a_4459_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4428_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4428_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_del_object(v___x_4422_);
lean_dec(v_a_4420_);
lean_dec(v___x_4384_);
lean_dec(v_levelParams_4381_);
v_a_4467_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4426_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4426_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
}
else
{
lean_dec(v_a_4404_);
lean_dec(v_a_4401_);
lean_dec(v___x_4384_);
lean_dec(v_levelParams_4381_);
return v___x_4418_;
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec(v_a_4404_);
lean_dec(v_a_4401_);
lean_dec(v___x_4384_);
lean_dec(v_declName_4382_);
lean_dec(v_levelParams_4381_);
v_a_4476_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4416_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4416_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4524_; 
lean_dec(v_a_4404_);
lean_dec(v_a_4401_);
lean_dec(v___x_4384_);
lean_dec(v_declName_4382_);
lean_dec(v_levelParams_4381_);
v_a_4517_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4519_ = v___x_4405_;
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4405_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
if (v_isShared_4520_ == 0)
{
v___x_4522_ = v___x_4519_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
else
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4532_; 
lean_dec(v_a_4401_);
lean_dec(v___x_4384_);
lean_dec_ref(v_wfPreprocessProof_4383_);
lean_dec(v_declName_4382_);
lean_dec(v_levelParams_4381_);
v_a_4525_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4527_ = v___x_4403_;
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v___x_4403_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4528_ == 0)
{
v___x_4530_ = v___x_4527_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_a_4525_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
}
}
else
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
lean_dec(v___x_4384_);
lean_dec_ref(v_wfPreprocessProof_4383_);
lean_dec(v_declName_4382_);
lean_dec(v_levelParams_4381_);
v_a_4533_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4400_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4400_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4533_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
v___jp_4393_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4394_ = lean_box(0);
v___x_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
return v___x_4395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object* v_levelParams_4541_, lean_object* v_declName_4542_, lean_object* v_wfPreprocessProof_4543_, lean_object* v___x_4544_, lean_object* v_unaryPreDefName_4545_, lean_object* v_xs_4546_, lean_object* v_body_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l_Lean_Elab_WF_mkUnfoldEq___lam__0(v_levelParams_4541_, v_declName_4542_, v_wfPreprocessProof_4543_, v___x_4544_, v_unaryPreDefName_4545_, v_xs_4546_, v_body_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec_ref(v_xs_4546_);
lean_dec(v_unaryPreDefName_4545_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(lean_object* v___y_4554_, uint8_t v_isExporting_4555_, lean_object* v___x_4556_, lean_object* v___y_4557_, lean_object* v___x_4558_, lean_object* v_a_x3f_4559_){
_start:
{
lean_object* v___x_4561_; lean_object* v_env_4562_; lean_object* v_nextMacroScope_4563_; lean_object* v_ngen_4564_; lean_object* v_auxDeclNGen_4565_; lean_object* v_traceState_4566_; lean_object* v_messages_4567_; lean_object* v_infoState_4568_; lean_object* v_snapshotTasks_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4594_; 
v___x_4561_ = lean_st_ref_take(v___y_4554_);
v_env_4562_ = lean_ctor_get(v___x_4561_, 0);
v_nextMacroScope_4563_ = lean_ctor_get(v___x_4561_, 1);
v_ngen_4564_ = lean_ctor_get(v___x_4561_, 2);
v_auxDeclNGen_4565_ = lean_ctor_get(v___x_4561_, 3);
v_traceState_4566_ = lean_ctor_get(v___x_4561_, 4);
v_messages_4567_ = lean_ctor_get(v___x_4561_, 6);
v_infoState_4568_ = lean_ctor_get(v___x_4561_, 7);
v_snapshotTasks_4569_ = lean_ctor_get(v___x_4561_, 8);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4594_ == 0)
{
lean_object* v_unused_4595_; 
v_unused_4595_ = lean_ctor_get(v___x_4561_, 5);
lean_dec(v_unused_4595_);
v___x_4571_ = v___x_4561_;
v_isShared_4572_ = v_isSharedCheck_4594_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_snapshotTasks_4569_);
lean_inc(v_infoState_4568_);
lean_inc(v_messages_4567_);
lean_inc(v_traceState_4566_);
lean_inc(v_auxDeclNGen_4565_);
lean_inc(v_ngen_4564_);
lean_inc(v_nextMacroScope_4563_);
lean_inc(v_env_4562_);
lean_dec(v___x_4561_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4594_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4573_; lean_object* v___x_4575_; 
v___x_4573_ = l_Lean_Environment_setExporting(v_env_4562_, v_isExporting_4555_);
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 5, v___x_4556_);
lean_ctor_set(v___x_4571_, 0, v___x_4573_);
v___x_4575_ = v___x_4571_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4573_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v_nextMacroScope_4563_);
lean_ctor_set(v_reuseFailAlloc_4593_, 2, v_ngen_4564_);
lean_ctor_set(v_reuseFailAlloc_4593_, 3, v_auxDeclNGen_4565_);
lean_ctor_set(v_reuseFailAlloc_4593_, 4, v_traceState_4566_);
lean_ctor_set(v_reuseFailAlloc_4593_, 5, v___x_4556_);
lean_ctor_set(v_reuseFailAlloc_4593_, 6, v_messages_4567_);
lean_ctor_set(v_reuseFailAlloc_4593_, 7, v_infoState_4568_);
lean_ctor_set(v_reuseFailAlloc_4593_, 8, v_snapshotTasks_4569_);
v___x_4575_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v_mctx_4578_; lean_object* v_zetaDeltaFVarIds_4579_; lean_object* v_postponed_4580_; lean_object* v_diag_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4591_; 
v___x_4576_ = lean_st_ref_put(v___y_4554_, v___x_4575_);
v___x_4577_ = lean_st_ref_take(v___y_4557_);
v_mctx_4578_ = lean_ctor_get(v___x_4577_, 0);
v_zetaDeltaFVarIds_4579_ = lean_ctor_get(v___x_4577_, 2);
v_postponed_4580_ = lean_ctor_get(v___x_4577_, 3);
v_diag_4581_ = lean_ctor_get(v___x_4577_, 4);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4591_ == 0)
{
lean_object* v_unused_4592_; 
v_unused_4592_ = lean_ctor_get(v___x_4577_, 1);
lean_dec(v_unused_4592_);
v___x_4583_ = v___x_4577_;
v_isShared_4584_ = v_isSharedCheck_4591_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_diag_4581_);
lean_inc(v_postponed_4580_);
lean_inc(v_zetaDeltaFVarIds_4579_);
lean_inc(v_mctx_4578_);
lean_dec(v___x_4577_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4591_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4586_; 
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 1, v___x_4558_);
v___x_4586_ = v___x_4583_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_mctx_4578_);
lean_ctor_set(v_reuseFailAlloc_4590_, 1, v___x_4558_);
lean_ctor_set(v_reuseFailAlloc_4590_, 2, v_zetaDeltaFVarIds_4579_);
lean_ctor_set(v_reuseFailAlloc_4590_, 3, v_postponed_4580_);
lean_ctor_set(v_reuseFailAlloc_4590_, 4, v_diag_4581_);
v___x_4586_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4587_ = lean_st_ref_put(v___y_4557_, v___x_4586_);
v___x_4588_ = lean_box(0);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
return v___x_4589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v___y_4596_, lean_object* v_isExporting_4597_, lean_object* v___x_4598_, lean_object* v___y_4599_, lean_object* v___x_4600_, lean_object* v_a_x3f_4601_, lean_object* v___y_4602_){
_start:
{
uint8_t v_isExporting_boxed_4603_; lean_object* v_res_4604_; 
v_isExporting_boxed_4603_ = lean_unbox(v_isExporting_4597_);
v_res_4604_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4596_, v_isExporting_boxed_4603_, v___x_4598_, v___y_4599_, v___x_4600_, v_a_x3f_4601_);
lean_dec(v_a_x3f_4601_);
lean_dec(v___y_4599_);
lean_dec(v___y_4596_);
return v_res_4604_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4605_; 
v___x_4605_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4605_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4606_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0);
v___x_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
return v___x_4607_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4608_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1);
v___x_4609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
lean_ctor_set(v___x_4609_, 1, v___x_4608_);
return v___x_4609_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4610_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1);
v___x_4611_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4610_);
lean_ctor_set(v___x_4611_, 1, v___x_4610_);
lean_ctor_set(v___x_4611_, 2, v___x_4610_);
lean_ctor_set(v___x_4611_, 3, v___x_4610_);
lean_ctor_set(v___x_4611_, 4, v___x_4610_);
lean_ctor_set(v___x_4611_, 5, v___x_4610_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(lean_object* v_x_4612_, uint8_t v_isExporting_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v___x_4619_; lean_object* v_env_4620_; lean_object* v___x_4621_; uint8_t v_isModule_4622_; 
v___x_4619_ = lean_st_ref_get(v___y_4617_);
v_env_4620_ = lean_ctor_get(v___x_4619_, 0);
lean_inc_ref(v_env_4620_);
lean_dec(v___x_4619_);
v___x_4621_ = l_Lean_Environment_header(v_env_4620_);
v_isModule_4622_ = lean_ctor_get_uint8(v___x_4621_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4621_);
if (v_isModule_4622_ == 0)
{
lean_object* v___x_4623_; 
lean_dec_ref(v_env_4620_);
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
lean_inc(v___y_4615_);
lean_inc_ref(v___y_4614_);
v___x_4623_ = lean_apply_5(v_x_4612_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, lean_box(0));
return v___x_4623_;
}
else
{
uint8_t v_isExporting_4624_; 
v_isExporting_4624_ = lean_ctor_get_uint8(v_env_4620_, sizeof(void*)*8);
lean_dec_ref(v_env_4620_);
if (v_isExporting_4613_ == 0)
{
if (v_isExporting_4624_ == 0)
{
lean_object* v___x_4690_; 
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
lean_inc(v___y_4615_);
lean_inc_ref(v___y_4614_);
v___x_4690_ = lean_apply_5(v_x_4612_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, lean_box(0));
return v___x_4690_;
}
else
{
goto v___jp_4625_;
}
}
else
{
if (v_isExporting_4624_ == 0)
{
goto v___jp_4625_;
}
else
{
lean_object* v___x_4691_; 
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
lean_inc(v___y_4615_);
lean_inc_ref(v___y_4614_);
v___x_4691_ = lean_apply_5(v_x_4612_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, lean_box(0));
return v___x_4691_;
}
}
v___jp_4625_:
{
lean_object* v___x_4626_; lean_object* v_env_4627_; lean_object* v_nextMacroScope_4628_; lean_object* v_ngen_4629_; lean_object* v_auxDeclNGen_4630_; lean_object* v_traceState_4631_; lean_object* v_messages_4632_; lean_object* v_infoState_4633_; lean_object* v_snapshotTasks_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4688_; 
v___x_4626_ = lean_st_ref_take(v___y_4617_);
v_env_4627_ = lean_ctor_get(v___x_4626_, 0);
v_nextMacroScope_4628_ = lean_ctor_get(v___x_4626_, 1);
v_ngen_4629_ = lean_ctor_get(v___x_4626_, 2);
v_auxDeclNGen_4630_ = lean_ctor_get(v___x_4626_, 3);
v_traceState_4631_ = lean_ctor_get(v___x_4626_, 4);
v_messages_4632_ = lean_ctor_get(v___x_4626_, 6);
v_infoState_4633_ = lean_ctor_get(v___x_4626_, 7);
v_snapshotTasks_4634_ = lean_ctor_get(v___x_4626_, 8);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4688_ == 0)
{
lean_object* v_unused_4689_; 
v_unused_4689_ = lean_ctor_get(v___x_4626_, 5);
lean_dec(v_unused_4689_);
v___x_4636_ = v___x_4626_;
v_isShared_4637_ = v_isSharedCheck_4688_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_snapshotTasks_4634_);
lean_inc(v_infoState_4633_);
lean_inc(v_messages_4632_);
lean_inc(v_traceState_4631_);
lean_inc(v_auxDeclNGen_4630_);
lean_inc(v_ngen_4629_);
lean_inc(v_nextMacroScope_4628_);
lean_inc(v_env_4627_);
lean_dec(v___x_4626_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4688_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4641_; 
v___x_4638_ = l_Lean_Environment_setExporting(v_env_4627_, v_isExporting_4613_);
v___x_4639_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 5, v___x_4639_);
lean_ctor_set(v___x_4636_, 0, v___x_4638_);
v___x_4641_ = v___x_4636_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4638_);
lean_ctor_set(v_reuseFailAlloc_4687_, 1, v_nextMacroScope_4628_);
lean_ctor_set(v_reuseFailAlloc_4687_, 2, v_ngen_4629_);
lean_ctor_set(v_reuseFailAlloc_4687_, 3, v_auxDeclNGen_4630_);
lean_ctor_set(v_reuseFailAlloc_4687_, 4, v_traceState_4631_);
lean_ctor_set(v_reuseFailAlloc_4687_, 5, v___x_4639_);
lean_ctor_set(v_reuseFailAlloc_4687_, 6, v_messages_4632_);
lean_ctor_set(v_reuseFailAlloc_4687_, 7, v_infoState_4633_);
lean_ctor_set(v_reuseFailAlloc_4687_, 8, v_snapshotTasks_4634_);
v___x_4641_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v_mctx_4644_; lean_object* v_zetaDeltaFVarIds_4645_; lean_object* v_postponed_4646_; lean_object* v_diag_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4685_; 
v___x_4642_ = lean_st_ref_put(v___y_4617_, v___x_4641_);
v___x_4643_ = lean_st_ref_take(v___y_4615_);
v_mctx_4644_ = lean_ctor_get(v___x_4643_, 0);
v_zetaDeltaFVarIds_4645_ = lean_ctor_get(v___x_4643_, 2);
v_postponed_4646_ = lean_ctor_get(v___x_4643_, 3);
v_diag_4647_ = lean_ctor_get(v___x_4643_, 4);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4685_ == 0)
{
lean_object* v_unused_4686_; 
v_unused_4686_ = lean_ctor_get(v___x_4643_, 1);
lean_dec(v_unused_4686_);
v___x_4649_ = v___x_4643_;
v_isShared_4650_ = v_isSharedCheck_4685_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_diag_4647_);
lean_inc(v_postponed_4646_);
lean_inc(v_zetaDeltaFVarIds_4645_);
lean_inc(v_mctx_4644_);
lean_dec(v___x_4643_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4685_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4651_; lean_object* v___x_4653_; 
v___x_4651_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3);
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 1, v___x_4651_);
v___x_4653_ = v___x_4649_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_mctx_4644_);
lean_ctor_set(v_reuseFailAlloc_4684_, 1, v___x_4651_);
lean_ctor_set(v_reuseFailAlloc_4684_, 2, v_zetaDeltaFVarIds_4645_);
lean_ctor_set(v_reuseFailAlloc_4684_, 3, v_postponed_4646_);
lean_ctor_set(v_reuseFailAlloc_4684_, 4, v_diag_4647_);
v___x_4653_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
lean_object* v___x_4654_; lean_object* v_r_4655_; 
v___x_4654_ = lean_st_ref_put(v___y_4615_, v___x_4653_);
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
lean_inc(v___y_4615_);
lean_inc_ref(v___y_4614_);
v_r_4655_ = lean_apply_5(v_x_4612_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, lean_box(0));
if (lean_obj_tag(v_r_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4672_; 
v_a_4656_ = lean_ctor_get(v_r_4655_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v_r_4655_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4658_ = v_r_4655_;
v_isShared_4659_ = v_isSharedCheck_4672_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v_r_4655_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4672_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v___x_4661_; 
lean_inc(v_a_4656_);
if (v_isShared_4659_ == 0)
{
lean_ctor_set_tag(v___x_4658_, 1);
v___x_4661_ = v___x_4658_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4656_);
v___x_4661_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
lean_object* v___x_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
v___x_4662_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4617_, v_isExporting_4624_, v___x_4639_, v___y_4615_, v___x_4651_, v___x_4661_);
lean_dec_ref(v___x_4661_);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4669_ == 0)
{
lean_object* v_unused_4670_; 
v_unused_4670_ = lean_ctor_get(v___x_4662_, 0);
lean_dec(v_unused_4670_);
v___x_4664_ = v___x_4662_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_dec(v___x_4662_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
lean_ctor_set(v___x_4664_, 0, v_a_4656_);
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4656_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4682_; 
v_a_4673_ = lean_ctor_get(v_r_4655_, 0);
lean_inc(v_a_4673_);
lean_dec_ref_known(v_r_4655_, 1);
v___x_4674_ = lean_box(0);
v___x_4675_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4617_, v_isExporting_4624_, v___x_4639_, v___y_4615_, v___x_4651_, v___x_4674_);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4682_ == 0)
{
lean_object* v_unused_4683_; 
v_unused_4683_ = lean_ctor_get(v___x_4675_, 0);
lean_dec(v_unused_4683_);
v___x_4677_ = v___x_4675_;
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
else
{
lean_dec(v___x_4675_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4680_; 
if (v_isShared_4678_ == 0)
{
lean_ctor_set_tag(v___x_4677_, 1);
lean_ctor_set(v___x_4677_, 0, v_a_4673_);
v___x_4680_ = v___x_4677_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4673_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___boxed(lean_object* v_x_4692_, lean_object* v_isExporting_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
uint8_t v_isExporting_boxed_4699_; lean_object* v_res_4700_; 
v_isExporting_boxed_4699_ = lean_unbox(v_isExporting_4693_);
v_res_4700_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4692_, v_isExporting_boxed_4699_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(lean_object* v_x_4701_, uint8_t v_when_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
if (v_when_4702_ == 0)
{
lean_object* v___x_4708_; 
lean_inc(v___y_4706_);
lean_inc_ref(v___y_4705_);
lean_inc(v___y_4704_);
lean_inc_ref(v___y_4703_);
v___x_4708_ = lean_apply_5(v_x_4701_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, lean_box(0));
return v___x_4708_;
}
else
{
uint8_t v___x_4709_; lean_object* v___x_4710_; 
v___x_4709_ = 0;
v___x_4710_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4701_, v___x_4709_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
return v___x_4710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg___boxed(lean_object* v_x_4711_, lean_object* v_when_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
uint8_t v_when_boxed_4718_; lean_object* v_res_4719_; 
v_when_boxed_4718_ = lean_unbox(v_when_4712_);
v_res_4719_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v_x_4711_, v_when_boxed_4718_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(lean_object* v_o_4720_, lean_object* v_k_4721_, uint8_t v_v_4722_){
_start:
{
lean_object* v_map_4723_; uint8_t v_hasTrace_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4738_; 
v_map_4723_ = lean_ctor_get(v_o_4720_, 0);
v_hasTrace_4724_ = lean_ctor_get_uint8(v_o_4720_, sizeof(void*)*1);
v_isSharedCheck_4738_ = !lean_is_exclusive(v_o_4720_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4726_ = v_o_4720_;
v_isShared_4727_ = v_isSharedCheck_4738_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_map_4723_);
lean_dec(v_o_4720_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4738_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4728_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4728_, 0, v_v_4722_);
lean_inc(v_k_4721_);
v___x_4729_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4721_, v___x_4728_, v_map_4723_);
if (v_hasTrace_4724_ == 0)
{
lean_object* v___x_4730_; uint8_t v___x_4731_; lean_object* v___x_4733_; 
v___x_4730_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4731_ = l_Lean_Name_isPrefixOf(v___x_4730_, v_k_4721_);
lean_dec(v_k_4721_);
if (v_isShared_4727_ == 0)
{
lean_ctor_set(v___x_4726_, 0, v___x_4729_);
v___x_4733_ = v___x_4726_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4729_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_ctor_set_uint8(v___x_4733_, sizeof(void*)*1, v___x_4731_);
return v___x_4733_;
}
}
else
{
lean_object* v___x_4736_; 
lean_dec(v_k_4721_);
if (v_isShared_4727_ == 0)
{
lean_ctor_set(v___x_4726_, 0, v___x_4729_);
v___x_4736_ = v___x_4726_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v___x_4729_);
lean_ctor_set_uint8(v_reuseFailAlloc_4737_, sizeof(void*)*1, v_hasTrace_4724_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2___boxed(lean_object* v_o_4739_, lean_object* v_k_4740_, lean_object* v_v_4741_){
_start:
{
uint8_t v_v_boxed_4742_; lean_object* v_res_4743_; 
v_v_boxed_4742_ = lean_unbox(v_v_4741_);
v_res_4743_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(v_o_4739_, v_k_4740_, v_v_boxed_4742_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(lean_object* v_opts_4744_, lean_object* v_opt_4745_, uint8_t v_val_4746_){
_start:
{
lean_object* v_name_4747_; lean_object* v___x_4748_; 
v_name_4747_ = lean_ctor_get(v_opt_4745_, 0);
lean_inc(v_name_4747_);
lean_dec_ref(v_opt_4745_);
v___x_4748_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(v_opts_4744_, v_name_4747_, v_val_4746_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed(lean_object* v_opts_4749_, lean_object* v_opt_4750_, lean_object* v_val_4751_){
_start:
{
uint8_t v_val_boxed_4752_; lean_object* v_res_4753_; 
v_val_boxed_4752_ = lean_unbox(v_val_4751_);
v_res_4753_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_opts_4749_, v_opt_4750_, v_val_boxed_4752_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t v___x_4754_, lean_object* v___x_4755_, uint8_t v___x_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v___x_4762_; lean_object* v_toCold_4763_; lean_object* v_currRecDepth_4764_; lean_object* v_ref_4765_; uint8_t v_suppressElabErrors_4766_; lean_object* v_fileName_4767_; lean_object* v_fileMap_4768_; lean_object* v_options_4769_; lean_object* v_currNamespace_4770_; lean_object* v_openDecls_4771_; lean_object* v_initHeartbeats_4772_; lean_object* v_maxHeartbeats_4773_; lean_object* v_quotContext_4774_; lean_object* v_currMacroScope_4775_; lean_object* v_cancelTk_x3f_4776_; lean_object* v_inheritedTraceOptions_4777_; lean_object* v_env_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; lean_object* v_fileName_4784_; lean_object* v_fileMap_4785_; lean_object* v_currNamespace_4786_; lean_object* v_openDecls_4787_; lean_object* v_initHeartbeats_4788_; lean_object* v_maxHeartbeats_4789_; lean_object* v_quotContext_4790_; lean_object* v_currMacroScope_4791_; lean_object* v_cancelTk_x3f_4792_; lean_object* v_inheritedTraceOptions_4793_; lean_object* v_currRecDepth_4794_; lean_object* v_ref_4795_; uint8_t v_suppressElabErrors_4796_; lean_object* v___y_4797_; uint8_t v___y_4804_; uint8_t v___x_4825_; 
v___x_4762_ = lean_st_ref_get(v___y_4760_);
v_toCold_4763_ = lean_ctor_get(v___y_4759_, 0);
v_currRecDepth_4764_ = lean_ctor_get(v___y_4759_, 1);
v_ref_4765_ = lean_ctor_get(v___y_4759_, 2);
v_suppressElabErrors_4766_ = lean_ctor_get_uint8(v___y_4759_, sizeof(void*)*3 + 1);
v_fileName_4767_ = lean_ctor_get(v_toCold_4763_, 0);
v_fileMap_4768_ = lean_ctor_get(v_toCold_4763_, 1);
v_options_4769_ = lean_ctor_get(v_toCold_4763_, 2);
v_currNamespace_4770_ = lean_ctor_get(v_toCold_4763_, 4);
v_openDecls_4771_ = lean_ctor_get(v_toCold_4763_, 5);
v_initHeartbeats_4772_ = lean_ctor_get(v_toCold_4763_, 6);
v_maxHeartbeats_4773_ = lean_ctor_get(v_toCold_4763_, 7);
v_quotContext_4774_ = lean_ctor_get(v_toCold_4763_, 8);
v_currMacroScope_4775_ = lean_ctor_get(v_toCold_4763_, 9);
v_cancelTk_x3f_4776_ = lean_ctor_get(v_toCold_4763_, 10);
v_inheritedTraceOptions_4777_ = lean_ctor_get(v_toCold_4763_, 11);
v_env_4778_ = lean_ctor_get(v___x_4762_, 0);
lean_inc_ref(v_env_4778_);
lean_dec(v___x_4762_);
v___x_4779_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_4769_);
v___x_4780_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_options_4769_, v___x_4779_, v___x_4754_);
v___x_4781_ = l_Lean_diagnostics;
v___x_4782_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v___x_4780_, v___x_4781_);
v___x_4825_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4778_);
lean_dec_ref(v_env_4778_);
if (v___x_4782_ == 0)
{
if (v___x_4825_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_4777_);
lean_inc(v_cancelTk_x3f_4776_);
lean_inc(v_currMacroScope_4775_);
lean_inc(v_quotContext_4774_);
lean_inc(v_maxHeartbeats_4773_);
lean_inc(v_initHeartbeats_4772_);
lean_inc(v_openDecls_4771_);
lean_inc(v_currNamespace_4770_);
lean_inc_ref(v_fileMap_4768_);
lean_inc_ref(v_fileName_4767_);
v_fileName_4784_ = v_fileName_4767_;
v_fileMap_4785_ = v_fileMap_4768_;
v_currNamespace_4786_ = v_currNamespace_4770_;
v_openDecls_4787_ = v_openDecls_4771_;
v_initHeartbeats_4788_ = v_initHeartbeats_4772_;
v_maxHeartbeats_4789_ = v_maxHeartbeats_4773_;
v_quotContext_4790_ = v_quotContext_4774_;
v_currMacroScope_4791_ = v_currMacroScope_4775_;
v_cancelTk_x3f_4792_ = v_cancelTk_x3f_4776_;
v_inheritedTraceOptions_4793_ = v_inheritedTraceOptions_4777_;
v_currRecDepth_4794_ = v_currRecDepth_4764_;
v_ref_4795_ = v_ref_4765_;
v_suppressElabErrors_4796_ = v_suppressElabErrors_4766_;
v___y_4797_ = v___y_4760_;
goto v___jp_4783_;
}
else
{
v___y_4804_ = v___x_4782_;
goto v___jp_4803_;
}
}
else
{
v___y_4804_ = v___x_4825_;
goto v___jp_4803_;
}
v___jp_4783_:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4798_ = l_Lean_maxRecDepth;
v___x_4799_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v___x_4780_, v___x_4798_);
v___x_4800_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4800_, 0, v_fileName_4784_);
lean_ctor_set(v___x_4800_, 1, v_fileMap_4785_);
lean_ctor_set(v___x_4800_, 2, v___x_4780_);
lean_ctor_set(v___x_4800_, 3, v___x_4799_);
lean_ctor_set(v___x_4800_, 4, v_currNamespace_4786_);
lean_ctor_set(v___x_4800_, 5, v_openDecls_4787_);
lean_ctor_set(v___x_4800_, 6, v_initHeartbeats_4788_);
lean_ctor_set(v___x_4800_, 7, v_maxHeartbeats_4789_);
lean_ctor_set(v___x_4800_, 8, v_quotContext_4790_);
lean_ctor_set(v___x_4800_, 9, v_currMacroScope_4791_);
lean_ctor_set(v___x_4800_, 10, v_cancelTk_x3f_4792_);
lean_ctor_set(v___x_4800_, 11, v_inheritedTraceOptions_4793_);
lean_inc(v_ref_4795_);
lean_inc(v_currRecDepth_4794_);
v___x_4801_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4801_, 0, v___x_4800_);
lean_ctor_set(v___x_4801_, 1, v_currRecDepth_4794_);
lean_ctor_set(v___x_4801_, 2, v_ref_4795_);
lean_ctor_set_uint8(v___x_4801_, sizeof(void*)*3, v___x_4782_);
lean_ctor_set_uint8(v___x_4801_, sizeof(void*)*3 + 1, v_suppressElabErrors_4796_);
v___x_4802_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v___x_4755_, v___x_4756_, v___y_4757_, v___y_4758_, v___x_4801_, v___y_4797_);
lean_dec_ref_known(v___x_4801_, 3);
return v___x_4802_;
}
v___jp_4803_:
{
if (v___y_4804_ == 0)
{
lean_object* v___x_4805_; lean_object* v_env_4806_; lean_object* v_nextMacroScope_4807_; lean_object* v_ngen_4808_; lean_object* v_auxDeclNGen_4809_; lean_object* v_traceState_4810_; lean_object* v_messages_4811_; lean_object* v_infoState_4812_; lean_object* v_snapshotTasks_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4823_; 
v___x_4805_ = lean_st_ref_take(v___y_4760_);
v_env_4806_ = lean_ctor_get(v___x_4805_, 0);
v_nextMacroScope_4807_ = lean_ctor_get(v___x_4805_, 1);
v_ngen_4808_ = lean_ctor_get(v___x_4805_, 2);
v_auxDeclNGen_4809_ = lean_ctor_get(v___x_4805_, 3);
v_traceState_4810_ = lean_ctor_get(v___x_4805_, 4);
v_messages_4811_ = lean_ctor_get(v___x_4805_, 6);
v_infoState_4812_ = lean_ctor_get(v___x_4805_, 7);
v_snapshotTasks_4813_ = lean_ctor_get(v___x_4805_, 8);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4823_ == 0)
{
lean_object* v_unused_4824_; 
v_unused_4824_ = lean_ctor_get(v___x_4805_, 5);
lean_dec(v_unused_4824_);
v___x_4815_ = v___x_4805_;
v_isShared_4816_ = v_isSharedCheck_4823_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_snapshotTasks_4813_);
lean_inc(v_infoState_4812_);
lean_inc(v_messages_4811_);
lean_inc(v_traceState_4810_);
lean_inc(v_auxDeclNGen_4809_);
lean_inc(v_ngen_4808_);
lean_inc(v_nextMacroScope_4807_);
lean_inc(v_env_4806_);
lean_dec(v___x_4805_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4823_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4820_; 
v___x_4817_ = l_Lean_Kernel_enableDiag(v_env_4806_, v___x_4782_);
v___x_4818_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 5, v___x_4818_);
lean_ctor_set(v___x_4815_, 0, v___x_4817_);
v___x_4820_ = v___x_4815_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4817_);
lean_ctor_set(v_reuseFailAlloc_4822_, 1, v_nextMacroScope_4807_);
lean_ctor_set(v_reuseFailAlloc_4822_, 2, v_ngen_4808_);
lean_ctor_set(v_reuseFailAlloc_4822_, 3, v_auxDeclNGen_4809_);
lean_ctor_set(v_reuseFailAlloc_4822_, 4, v_traceState_4810_);
lean_ctor_set(v_reuseFailAlloc_4822_, 5, v___x_4818_);
lean_ctor_set(v_reuseFailAlloc_4822_, 6, v_messages_4811_);
lean_ctor_set(v_reuseFailAlloc_4822_, 7, v_infoState_4812_);
lean_ctor_set(v_reuseFailAlloc_4822_, 8, v_snapshotTasks_4813_);
v___x_4820_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
lean_object* v___x_4821_; 
v___x_4821_ = lean_st_ref_put(v___y_4760_, v___x_4820_);
lean_inc_ref(v_inheritedTraceOptions_4777_);
lean_inc(v_cancelTk_x3f_4776_);
lean_inc(v_currMacroScope_4775_);
lean_inc(v_quotContext_4774_);
lean_inc(v_maxHeartbeats_4773_);
lean_inc(v_initHeartbeats_4772_);
lean_inc(v_openDecls_4771_);
lean_inc(v_currNamespace_4770_);
lean_inc_ref(v_fileMap_4768_);
lean_inc_ref(v_fileName_4767_);
v_fileName_4784_ = v_fileName_4767_;
v_fileMap_4785_ = v_fileMap_4768_;
v_currNamespace_4786_ = v_currNamespace_4770_;
v_openDecls_4787_ = v_openDecls_4771_;
v_initHeartbeats_4788_ = v_initHeartbeats_4772_;
v_maxHeartbeats_4789_ = v_maxHeartbeats_4773_;
v_quotContext_4790_ = v_quotContext_4774_;
v_currMacroScope_4791_ = v_currMacroScope_4775_;
v_cancelTk_x3f_4792_ = v_cancelTk_x3f_4776_;
v_inheritedTraceOptions_4793_ = v_inheritedTraceOptions_4777_;
v_currRecDepth_4794_ = v_currRecDepth_4764_;
v_ref_4795_ = v_ref_4765_;
v_suppressElabErrors_4796_ = v_suppressElabErrors_4766_;
v___y_4797_ = v___y_4760_;
goto v___jp_4783_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_4777_);
lean_inc(v_cancelTk_x3f_4776_);
lean_inc(v_currMacroScope_4775_);
lean_inc(v_quotContext_4774_);
lean_inc(v_maxHeartbeats_4773_);
lean_inc(v_initHeartbeats_4772_);
lean_inc(v_openDecls_4771_);
lean_inc(v_currNamespace_4770_);
lean_inc_ref(v_fileMap_4768_);
lean_inc_ref(v_fileName_4767_);
v_fileName_4784_ = v_fileName_4767_;
v_fileMap_4785_ = v_fileMap_4768_;
v_currNamespace_4786_ = v_currNamespace_4770_;
v_openDecls_4787_ = v_openDecls_4771_;
v_initHeartbeats_4788_ = v_initHeartbeats_4772_;
v_maxHeartbeats_4789_ = v_maxHeartbeats_4773_;
v_quotContext_4790_ = v_quotContext_4774_;
v_currMacroScope_4791_ = v_currMacroScope_4775_;
v_cancelTk_x3f_4792_ = v_cancelTk_x3f_4776_;
v_inheritedTraceOptions_4793_ = v_inheritedTraceOptions_4777_;
v_currRecDepth_4794_ = v_currRecDepth_4764_;
v_ref_4795_ = v_ref_4765_;
v_suppressElabErrors_4796_ = v_suppressElabErrors_4766_;
v___y_4797_ = v___y_4760_;
goto v___jp_4783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object* v___x_4826_, lean_object* v___x_4827_, lean_object* v___x_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_){
_start:
{
uint8_t v___x_9586__boxed_4834_; uint8_t v___x_9588__boxed_4835_; lean_object* v_res_4836_; 
v___x_9586__boxed_4834_ = lean_unbox(v___x_4826_);
v___x_9588__boxed_4835_ = lean_unbox(v___x_4828_);
v_res_4836_ = l_Lean_Elab_WF_mkUnfoldEq___lam__2(v___x_9586__boxed_4834_, v___x_4827_, v___x_9588__boxed_4835_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_);
lean_dec(v___y_4832_);
lean_dec_ref(v___y_4831_);
lean_dec(v___y_4830_);
lean_dec_ref(v___y_4829_);
return v_res_4836_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4838_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___closed__0));
v___x_4839_ = l_Lean_stringToMessageData(v___x_4838_);
return v___x_4839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object* v_preDef_4840_, lean_object* v_unaryPreDefName_4841_, lean_object* v_wfPreprocessProof_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_){
_start:
{
lean_object* v___x_4848_; lean_object* v_env_4849_; lean_object* v_levelParams_4850_; lean_object* v_declName_4851_; lean_object* v_value_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___f_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___f_4859_; uint8_t v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___f_4866_; lean_object* v___x_4867_; 
v___x_4848_ = lean_st_ref_get(v_a_4846_);
v_env_4849_ = lean_ctor_get(v___x_4848_, 0);
lean_inc_ref(v_env_4849_);
lean_dec(v___x_4848_);
v_levelParams_4850_ = lean_ctor_get(v_preDef_4840_, 1);
lean_inc(v_levelParams_4850_);
v_declName_4851_ = lean_ctor_get(v_preDef_4840_, 3);
lean_inc_n(v_declName_4851_, 2);
v_value_4852_ = lean_ctor_get(v_preDef_4840_, 7);
lean_inc_ref(v_value_4852_);
lean_dec_ref(v_preDef_4840_);
v___x_4853_ = l_Lean_Meta_unfoldThmSuffix;
v___x_4854_ = l_Lean_Meta_mkEqLikeNameFor(v_env_4849_, v_declName_4851_, v___x_4853_);
lean_inc(v___x_4854_);
v___f_4855_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4855_, 0, v_levelParams_4850_);
lean_closure_set(v___f_4855_, 1, v_declName_4851_);
lean_closure_set(v___f_4855_, 2, v_wfPreprocessProof_4842_);
lean_closure_set(v___f_4855_, 3, v___x_4854_);
lean_closure_set(v___f_4855_, 4, v_unaryPreDefName_4841_);
v___x_4856_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___closed__1, &l_Lean_Elab_WF_mkUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1);
v___x_4857_ = l_Lean_MessageData_ofName(v___x_4854_);
v___x_4858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4856_);
lean_ctor_set(v___x_4858_, 1, v___x_4857_);
v___f_4859_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4859_, 0, v___x_4858_);
v___x_4860_ = 0;
v___x_4861_ = lean_box(v___x_4860_);
v___x_4862_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed), 9, 4);
lean_closure_set(v___x_4862_, 0, lean_box(0));
lean_closure_set(v___x_4862_, 1, v_value_4852_);
lean_closure_set(v___x_4862_, 2, v___f_4855_);
lean_closure_set(v___x_4862_, 3, v___x_4861_);
v___x_4863_ = 1;
v___x_4864_ = lean_box(v___x_4860_);
v___x_4865_ = lean_box(v___x_4863_);
v___f_4866_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_4866_, 0, v___x_4864_);
lean_closure_set(v___f_4866_, 1, v___x_4862_);
lean_closure_set(v___f_4866_, 2, v___x_4865_);
v___x_4867_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4866_, v___f_4859_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4867_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4867_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
v_a_4876_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4867_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4867_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4881_; 
if (v_isShared_4879_ == 0)
{
v___x_4881_ = v___x_4878_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4876_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___boxed(lean_object* v_preDef_4884_, lean_object* v_unaryPreDefName_4885_, lean_object* v_wfPreprocessProof_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l_Lean_Elab_WF_mkUnfoldEq(v_preDef_4884_, v_unaryPreDefName_4885_, v_wfPreprocessProof_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_);
lean_dec(v_a_4890_);
lean_dec_ref(v_a_4889_);
lean_dec(v_a_4888_);
lean_dec_ref(v_a_4887_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6(lean_object* v_00_u03b1_4893_, lean_object* v_x_4894_, uint8_t v_isExporting_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_){
_start:
{
lean_object* v___x_4901_; 
v___x_4901_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4894_, v_isExporting_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_);
return v___x_4901_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4902_, lean_object* v_x_4903_, lean_object* v_isExporting_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_){
_start:
{
uint8_t v_isExporting_boxed_4910_; lean_object* v_res_4911_; 
v_isExporting_boxed_4910_ = lean_unbox(v_isExporting_4904_);
v_res_4911_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6(v_00_u03b1_4902_, v_x_4903_, v_isExporting_boxed_4910_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
lean_dec(v___y_4908_);
lean_dec_ref(v___y_4907_);
lean_dec(v___y_4906_);
lean_dec_ref(v___y_4905_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(lean_object* v_00_u03b1_4912_, lean_object* v_x_4913_, uint8_t v_when_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
lean_object* v___x_4920_; 
v___x_4920_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v_x_4913_, v_when_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___boxed(lean_object* v_00_u03b1_4921_, lean_object* v_x_4922_, lean_object* v_when_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_){
_start:
{
uint8_t v_when_boxed_4929_; lean_object* v_res_4930_; 
v_when_boxed_4929_ = lean_unbox(v_when_4923_);
v_res_4930_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(v_00_u03b1_4921_, v_x_4922_, v_when_boxed_4929_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_);
lean_dec(v___y_4927_);
lean_dec_ref(v___y_4926_);
lean_dec(v___y_4925_);
lean_dec_ref(v___y_4924_);
return v_res_4930_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4932_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0));
v___x_4933_ = l_Lean_stringToMessageData(v___x_4932_);
return v___x_4933_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4939_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3));
v___x_4940_ = l_Lean_stringToMessageData(v___x_4939_);
return v___x_4940_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4942_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5));
v___x_4943_ = l_Lean_stringToMessageData(v___x_4942_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object* v_levelParams_4944_, lean_object* v_declName_4945_, lean_object* v___x_4946_, lean_object* v___x_4947_, lean_object* v___x_4948_, lean_object* v_xs_4949_, lean_object* v_body_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4959_ = lean_box(0);
lean_inc(v_levelParams_4944_);
v___x_4960_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4944_, v___x_4959_);
v___x_4961_ = l_Lean_mkConst(v_declName_4945_, v___x_4960_);
v___x_4962_ = l_Lean_mkAppN(v___x_4961_, v_xs_4949_);
v___x_4963_ = l_Lean_Meta_mkEq(v___x_4962_, v_body_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc_n(v_a_4964_, 2);
lean_dec_ref_known(v___x_4963_, 1);
v___x_4965_ = lean_box(0);
v___x_4966_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4964_, v___x_4965_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_object* v_a_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc(v_a_4967_);
lean_dec_ref_known(v___x_4966_, 1);
v___x_4968_ = l_Lean_Expr_mvarId_x21(v_a_4967_);
v___x_4969_ = l_Lean_Elab_Eqns_deltaLHS(v___x_4968_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v_a_4970_; uint8_t v___x_4971_; uint8_t v___x_4972_; lean_object* v___y_4974_; lean_object* v___y_4975_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc_n(v_a_4970_, 2);
lean_dec_ref_known(v___x_4969_, 1);
v___x_4971_ = 1;
v___x_4972_ = 0;
v___x_5034_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2));
v___x_5035_ = l_Lean_MVarId_applyConst(v_a_4970_, v___x_4946_, v___x_5034_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
if (lean_obj_tag(v___x_5035_) == 0)
{
lean_object* v_a_5036_; uint8_t v___x_5037_; 
v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
lean_inc(v_a_5036_);
lean_dec_ref_known(v___x_5035_, 1);
v___x_5037_ = l_List_isEmpty___redArg(v_a_5036_);
lean_dec(v_a_5036_);
if (v___x_5037_ == 0)
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
lean_dec(v_a_4967_);
lean_dec(v_a_4964_);
lean_dec(v___x_4947_);
lean_dec(v_levelParams_4944_);
v___x_5038_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4);
v___x_5039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5039_, 0, v___x_5038_);
lean_ctor_set(v___x_5039_, 1, v___x_4948_);
v___x_5040_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6);
v___x_5041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5041_, 0, v___x_5039_);
lean_ctor_set(v___x_5041_, 1, v___x_5040_);
v___x_5042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5042_, 0, v_a_4970_);
v___x_5043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5041_);
lean_ctor_set(v___x_5043_, 1, v___x_5042_);
v___x_5044_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5043_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
v___x_5046_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_5045_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
return v___x_5046_;
}
else
{
lean_dec(v_a_4970_);
lean_dec_ref(v___x_4948_);
v___y_4974_ = v___y_4951_;
v___y_4975_ = v___y_4952_;
v___y_4976_ = v___y_4953_;
v___y_4977_ = v___y_4954_;
goto v___jp_4973_;
}
}
else
{
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
lean_dec(v_a_4970_);
lean_dec(v_a_4967_);
lean_dec(v_a_4964_);
lean_dec_ref(v___x_4948_);
lean_dec(v___x_4947_);
lean_dec(v_levelParams_4944_);
v_a_5047_ = lean_ctor_get(v___x_5035_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v___x_5035_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5035_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
v___jp_4973_:
{
lean_object* v___x_4978_; lean_object* v_a_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_5033_; 
v___x_4978_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4967_, v___y_4975_);
v_a_4979_ = lean_ctor_get(v___x_4978_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_4978_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_4981_ = v___x_4978_;
v_isShared_4982_ = v_isSharedCheck_5033_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_a_4979_);
lean_dec(v___x_4978_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_5033_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
uint8_t v___x_4983_; lean_object* v___x_4984_; 
v___x_4983_ = 1;
v___x_4984_ = l_Lean_Meta_mkForallFVars(v_xs_4949_, v_a_4964_, v___x_4972_, v___x_4971_, v___x_4971_, v___x_4983_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v_a_4985_; lean_object* v___x_4986_; 
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc(v_a_4985_);
lean_dec_ref_known(v___x_4984_, 1);
v___x_4986_ = l_Lean_Meta_letToHave(v_a_4985_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4988_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4986_, 1);
v___x_4988_ = l_Lean_Meta_mkLambdaFVars(v_xs_4949_, v_a_4979_, v___x_4972_, v___x_4971_, v___x_4972_, v___x_4971_, v___x_4983_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v_a_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4994_; 
v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
lean_inc(v_a_4989_);
lean_dec_ref_known(v___x_4988_, 1);
lean_inc_n(v___x_4947_, 2);
v___x_4990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4947_);
lean_ctor_set(v___x_4990_, 1, v_levelParams_4944_);
lean_ctor_set(v___x_4990_, 2, v_a_4987_);
v___x_4991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4947_);
lean_ctor_set(v___x_4991_, 1, v___x_4959_);
v___x_4992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v_a_4989_);
lean_ctor_set(v___x_4992_, 2, v___x_4991_);
if (v_isShared_4982_ == 0)
{
lean_ctor_set_tag(v___x_4981_, 2);
lean_ctor_set(v___x_4981_, 0, v___x_4992_);
v___x_4994_ = v___x_4981_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v___x_4992_);
v___x_4994_ = v_reuseFailAlloc_5008_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4995_; 
v___x_4995_ = l_Lean_addDecl(v___x_4994_, v___x_4972_, v___y_4976_, v___y_4977_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v___x_4996_; 
lean_dec_ref_known(v___x_4995_, 1);
lean_inc(v___x_4947_);
v___x_4996_ = l_Lean_inferDefEqAttr(v___x_4947_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
if (lean_obj_tag(v___x_4996_) == 0)
{
lean_object* v_toCold_4997_; lean_object* v_options_4998_; uint8_t v_hasTrace_4999_; 
lean_dec_ref_known(v___x_4996_, 1);
v_toCold_4997_ = lean_ctor_get(v___y_4976_, 0);
v_options_4998_ = lean_ctor_get(v_toCold_4997_, 2);
v_hasTrace_4999_ = lean_ctor_get_uint8(v_options_4998_, sizeof(void*)*1);
if (v_hasTrace_4999_ == 0)
{
lean_dec(v___x_4947_);
goto v___jp_4956_;
}
else
{
lean_object* v_inheritedTraceOptions_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; uint8_t v___x_5003_; 
v_inheritedTraceOptions_5000_ = lean_ctor_get(v_toCold_4997_, 11);
v___x_5001_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_5002_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_5003_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5000_, v_options_4998_, v___x_5002_);
if (v___x_5003_ == 0)
{
lean_dec(v___x_4947_);
goto v___jp_4956_;
}
else
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5004_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1);
v___x_5005_ = l_Lean_MessageData_ofConstName(v___x_4947_, v___x_4972_);
v___x_5006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5004_);
lean_ctor_set(v___x_5006_, 1, v___x_5005_);
v___x_5007_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_5001_, v___x_5006_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
return v___x_5007_;
}
}
}
else
{
lean_dec(v___x_4947_);
return v___x_4996_;
}
}
else
{
lean_dec(v___x_4947_);
return v___x_4995_;
}
}
}
else
{
lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5016_; 
lean_dec(v_a_4987_);
lean_del_object(v___x_4981_);
lean_dec(v___x_4947_);
lean_dec(v_levelParams_4944_);
v_a_5009_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5011_ = v___x_4988_;
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v___x_4988_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5014_; 
if (v_isShared_5012_ == 0)
{
v___x_5014_ = v___x_5011_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
}
else
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5024_; 
lean_del_object(v___x_4981_);
lean_dec(v_a_4979_);
lean_dec(v___x_4947_);
lean_dec(v_levelParams_4944_);
v_a_5017_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5019_ = v___x_4986_;
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_4986_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5022_; 
if (v_isShared_5020_ == 0)
{
v___x_5022_ = v___x_5019_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5017_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
}
}
else
{
lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5032_; 
lean_del_object(v___x_4981_);
lean_dec(v_a_4979_);
lean_dec(v___x_4947_);
lean_dec(v_levelParams_4944_);
v_a_5025_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5027_ = v___x_4984_;
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_4984_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5030_; 
if (v_isShared_5028_ == 0)
{
v___x_5030_ = v___x_5027_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_a_5025_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
}
}
else
{
lean_object* v_a_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5062_; 
lean_dec(v_a_4967_);
lean_dec(v_a_4964_);
lean_dec_ref(v___x_4948_);
lean_dec(v___x_4947_);
lean_dec(v___x_4946_);
lean_dec(v_levelParams_4944_);
v_a_5055_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5057_ = v___x_4969_;
v_isShared_5058_ = v_isSharedCheck_5062_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_a_5055_);
lean_dec(v___x_4969_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5062_;
goto v_resetjp_5056_;
}
v_resetjp_5056_:
{
lean_object* v___x_5060_; 
if (v_isShared_5058_ == 0)
{
v___x_5060_ = v___x_5057_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_a_5055_);
v___x_5060_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
return v___x_5060_;
}
}
}
}
else
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5070_; 
lean_dec(v_a_4964_);
lean_dec_ref(v___x_4948_);
lean_dec(v___x_4947_);
lean_dec(v___x_4946_);
lean_dec(v_levelParams_4944_);
v_a_5063_ = lean_ctor_get(v___x_4966_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5065_ = v___x_4966_;
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_4966_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5068_; 
if (v_isShared_5066_ == 0)
{
v___x_5068_ = v___x_5065_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_5063_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
}
else
{
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5078_; 
lean_dec_ref(v___x_4948_);
lean_dec(v___x_4947_);
lean_dec(v___x_4946_);
lean_dec(v_levelParams_4944_);
v_a_5071_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5073_ = v___x_4963_;
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v___x_4963_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5071_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
v___jp_4956_:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4957_ = lean_box(0);
v___x_4958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4957_);
return v___x_4958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed(lean_object* v_levelParams_5079_, lean_object* v_declName_5080_, lean_object* v___x_5081_, lean_object* v___x_5082_, lean_object* v___x_5083_, lean_object* v_xs_5084_, lean_object* v_body_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(v_levelParams_5079_, v_declName_5080_, v___x_5081_, v___x_5082_, v___x_5083_, v_xs_5084_, v_body_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_);
lean_dec(v___y_5089_);
lean_dec_ref(v___y_5088_);
lean_dec(v___y_5087_);
lean_dec_ref(v___y_5086_);
lean_dec_ref(v_xs_5084_);
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(uint8_t v___x_5092_, lean_object* v_value_5093_, lean_object* v___f_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v___x_5100_; lean_object* v_toCold_5101_; lean_object* v_currRecDepth_5102_; lean_object* v_ref_5103_; uint8_t v_suppressElabErrors_5104_; lean_object* v_fileName_5105_; lean_object* v_fileMap_5106_; lean_object* v_options_5107_; lean_object* v_currNamespace_5108_; lean_object* v_openDecls_5109_; lean_object* v_initHeartbeats_5110_; lean_object* v_maxHeartbeats_5111_; lean_object* v_quotContext_5112_; lean_object* v_currMacroScope_5113_; lean_object* v_cancelTk_x3f_5114_; lean_object* v_inheritedTraceOptions_5115_; lean_object* v_env_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; uint8_t v___x_5120_; lean_object* v_fileName_5122_; lean_object* v_fileMap_5123_; lean_object* v_currNamespace_5124_; lean_object* v_openDecls_5125_; lean_object* v_initHeartbeats_5126_; lean_object* v_maxHeartbeats_5127_; lean_object* v_quotContext_5128_; lean_object* v_currMacroScope_5129_; lean_object* v_cancelTk_x3f_5130_; lean_object* v_inheritedTraceOptions_5131_; lean_object* v_currRecDepth_5132_; lean_object* v_ref_5133_; uint8_t v_suppressElabErrors_5134_; lean_object* v___y_5135_; uint8_t v___y_5142_; uint8_t v___x_5163_; 
v___x_5100_ = lean_st_ref_get(v___y_5098_);
v_toCold_5101_ = lean_ctor_get(v___y_5097_, 0);
v_currRecDepth_5102_ = lean_ctor_get(v___y_5097_, 1);
v_ref_5103_ = lean_ctor_get(v___y_5097_, 2);
v_suppressElabErrors_5104_ = lean_ctor_get_uint8(v___y_5097_, sizeof(void*)*3 + 1);
v_fileName_5105_ = lean_ctor_get(v_toCold_5101_, 0);
v_fileMap_5106_ = lean_ctor_get(v_toCold_5101_, 1);
v_options_5107_ = lean_ctor_get(v_toCold_5101_, 2);
v_currNamespace_5108_ = lean_ctor_get(v_toCold_5101_, 4);
v_openDecls_5109_ = lean_ctor_get(v_toCold_5101_, 5);
v_initHeartbeats_5110_ = lean_ctor_get(v_toCold_5101_, 6);
v_maxHeartbeats_5111_ = lean_ctor_get(v_toCold_5101_, 7);
v_quotContext_5112_ = lean_ctor_get(v_toCold_5101_, 8);
v_currMacroScope_5113_ = lean_ctor_get(v_toCold_5101_, 9);
v_cancelTk_x3f_5114_ = lean_ctor_get(v_toCold_5101_, 10);
v_inheritedTraceOptions_5115_ = lean_ctor_get(v_toCold_5101_, 11);
v_env_5116_ = lean_ctor_get(v___x_5100_, 0);
lean_inc_ref(v_env_5116_);
lean_dec(v___x_5100_);
v___x_5117_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_5107_);
v___x_5118_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_options_5107_, v___x_5117_, v___x_5092_);
v___x_5119_ = l_Lean_diagnostics;
v___x_5120_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v___x_5118_, v___x_5119_);
v___x_5163_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5116_);
lean_dec_ref(v_env_5116_);
if (v___x_5120_ == 0)
{
if (v___x_5163_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_5115_);
lean_inc(v_cancelTk_x3f_5114_);
lean_inc(v_currMacroScope_5113_);
lean_inc(v_quotContext_5112_);
lean_inc(v_maxHeartbeats_5111_);
lean_inc(v_initHeartbeats_5110_);
lean_inc(v_openDecls_5109_);
lean_inc(v_currNamespace_5108_);
lean_inc_ref(v_fileMap_5106_);
lean_inc_ref(v_fileName_5105_);
v_fileName_5122_ = v_fileName_5105_;
v_fileMap_5123_ = v_fileMap_5106_;
v_currNamespace_5124_ = v_currNamespace_5108_;
v_openDecls_5125_ = v_openDecls_5109_;
v_initHeartbeats_5126_ = v_initHeartbeats_5110_;
v_maxHeartbeats_5127_ = v_maxHeartbeats_5111_;
v_quotContext_5128_ = v_quotContext_5112_;
v_currMacroScope_5129_ = v_currMacroScope_5113_;
v_cancelTk_x3f_5130_ = v_cancelTk_x3f_5114_;
v_inheritedTraceOptions_5131_ = v_inheritedTraceOptions_5115_;
v_currRecDepth_5132_ = v_currRecDepth_5102_;
v_ref_5133_ = v_ref_5103_;
v_suppressElabErrors_5134_ = v_suppressElabErrors_5104_;
v___y_5135_ = v___y_5098_;
goto v___jp_5121_;
}
else
{
v___y_5142_ = v___x_5120_;
goto v___jp_5141_;
}
}
else
{
v___y_5142_ = v___x_5163_;
goto v___jp_5141_;
}
v___jp_5121_:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5136_ = l_Lean_maxRecDepth;
v___x_5137_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v___x_5118_, v___x_5136_);
v___x_5138_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_5138_, 0, v_fileName_5122_);
lean_ctor_set(v___x_5138_, 1, v_fileMap_5123_);
lean_ctor_set(v___x_5138_, 2, v___x_5118_);
lean_ctor_set(v___x_5138_, 3, v___x_5137_);
lean_ctor_set(v___x_5138_, 4, v_currNamespace_5124_);
lean_ctor_set(v___x_5138_, 5, v_openDecls_5125_);
lean_ctor_set(v___x_5138_, 6, v_initHeartbeats_5126_);
lean_ctor_set(v___x_5138_, 7, v_maxHeartbeats_5127_);
lean_ctor_set(v___x_5138_, 8, v_quotContext_5128_);
lean_ctor_set(v___x_5138_, 9, v_currMacroScope_5129_);
lean_ctor_set(v___x_5138_, 10, v_cancelTk_x3f_5130_);
lean_ctor_set(v___x_5138_, 11, v_inheritedTraceOptions_5131_);
lean_inc(v_ref_5133_);
lean_inc(v_currRecDepth_5132_);
v___x_5139_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5139_, 0, v___x_5138_);
lean_ctor_set(v___x_5139_, 1, v_currRecDepth_5132_);
lean_ctor_set(v___x_5139_, 2, v_ref_5133_);
lean_ctor_set_uint8(v___x_5139_, sizeof(void*)*3, v___x_5120_);
lean_ctor_set_uint8(v___x_5139_, sizeof(void*)*3 + 1, v_suppressElabErrors_5134_);
v___x_5140_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_value_5093_, v___f_5094_, v___x_5092_, v___y_5095_, v___y_5096_, v___x_5139_, v___y_5135_);
lean_dec_ref_known(v___x_5139_, 3);
return v___x_5140_;
}
v___jp_5141_:
{
if (v___y_5142_ == 0)
{
lean_object* v___x_5143_; lean_object* v_env_5144_; lean_object* v_nextMacroScope_5145_; lean_object* v_ngen_5146_; lean_object* v_auxDeclNGen_5147_; lean_object* v_traceState_5148_; lean_object* v_messages_5149_; lean_object* v_infoState_5150_; lean_object* v_snapshotTasks_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5161_; 
v___x_5143_ = lean_st_ref_take(v___y_5098_);
v_env_5144_ = lean_ctor_get(v___x_5143_, 0);
v_nextMacroScope_5145_ = lean_ctor_get(v___x_5143_, 1);
v_ngen_5146_ = lean_ctor_get(v___x_5143_, 2);
v_auxDeclNGen_5147_ = lean_ctor_get(v___x_5143_, 3);
v_traceState_5148_ = lean_ctor_get(v___x_5143_, 4);
v_messages_5149_ = lean_ctor_get(v___x_5143_, 6);
v_infoState_5150_ = lean_ctor_get(v___x_5143_, 7);
v_snapshotTasks_5151_ = lean_ctor_get(v___x_5143_, 8);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5161_ == 0)
{
lean_object* v_unused_5162_; 
v_unused_5162_ = lean_ctor_get(v___x_5143_, 5);
lean_dec(v_unused_5162_);
v___x_5153_ = v___x_5143_;
v_isShared_5154_ = v_isSharedCheck_5161_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_snapshotTasks_5151_);
lean_inc(v_infoState_5150_);
lean_inc(v_messages_5149_);
lean_inc(v_traceState_5148_);
lean_inc(v_auxDeclNGen_5147_);
lean_inc(v_ngen_5146_);
lean_inc(v_nextMacroScope_5145_);
lean_inc(v_env_5144_);
lean_dec(v___x_5143_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5161_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5158_; 
v___x_5155_ = l_Lean_Kernel_enableDiag(v_env_5144_, v___x_5120_);
v___x_5156_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_5154_ == 0)
{
lean_ctor_set(v___x_5153_, 5, v___x_5156_);
lean_ctor_set(v___x_5153_, 0, v___x_5155_);
v___x_5158_ = v___x_5153_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5155_);
lean_ctor_set(v_reuseFailAlloc_5160_, 1, v_nextMacroScope_5145_);
lean_ctor_set(v_reuseFailAlloc_5160_, 2, v_ngen_5146_);
lean_ctor_set(v_reuseFailAlloc_5160_, 3, v_auxDeclNGen_5147_);
lean_ctor_set(v_reuseFailAlloc_5160_, 4, v_traceState_5148_);
lean_ctor_set(v_reuseFailAlloc_5160_, 5, v___x_5156_);
lean_ctor_set(v_reuseFailAlloc_5160_, 6, v_messages_5149_);
lean_ctor_set(v_reuseFailAlloc_5160_, 7, v_infoState_5150_);
lean_ctor_set(v_reuseFailAlloc_5160_, 8, v_snapshotTasks_5151_);
v___x_5158_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
lean_object* v___x_5159_; 
v___x_5159_ = lean_st_ref_put(v___y_5098_, v___x_5158_);
lean_inc_ref(v_inheritedTraceOptions_5115_);
lean_inc(v_cancelTk_x3f_5114_);
lean_inc(v_currMacroScope_5113_);
lean_inc(v_quotContext_5112_);
lean_inc(v_maxHeartbeats_5111_);
lean_inc(v_initHeartbeats_5110_);
lean_inc(v_openDecls_5109_);
lean_inc(v_currNamespace_5108_);
lean_inc_ref(v_fileMap_5106_);
lean_inc_ref(v_fileName_5105_);
v_fileName_5122_ = v_fileName_5105_;
v_fileMap_5123_ = v_fileMap_5106_;
v_currNamespace_5124_ = v_currNamespace_5108_;
v_openDecls_5125_ = v_openDecls_5109_;
v_initHeartbeats_5126_ = v_initHeartbeats_5110_;
v_maxHeartbeats_5127_ = v_maxHeartbeats_5111_;
v_quotContext_5128_ = v_quotContext_5112_;
v_currMacroScope_5129_ = v_currMacroScope_5113_;
v_cancelTk_x3f_5130_ = v_cancelTk_x3f_5114_;
v_inheritedTraceOptions_5131_ = v_inheritedTraceOptions_5115_;
v_currRecDepth_5132_ = v_currRecDepth_5102_;
v_ref_5133_ = v_ref_5103_;
v_suppressElabErrors_5134_ = v_suppressElabErrors_5104_;
v___y_5135_ = v___y_5098_;
goto v___jp_5121_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_5115_);
lean_inc(v_cancelTk_x3f_5114_);
lean_inc(v_currMacroScope_5113_);
lean_inc(v_quotContext_5112_);
lean_inc(v_maxHeartbeats_5111_);
lean_inc(v_initHeartbeats_5110_);
lean_inc(v_openDecls_5109_);
lean_inc(v_currNamespace_5108_);
lean_inc_ref(v_fileMap_5106_);
lean_inc_ref(v_fileName_5105_);
v_fileName_5122_ = v_fileName_5105_;
v_fileMap_5123_ = v_fileMap_5106_;
v_currNamespace_5124_ = v_currNamespace_5108_;
v_openDecls_5125_ = v_openDecls_5109_;
v_initHeartbeats_5126_ = v_initHeartbeats_5110_;
v_maxHeartbeats_5127_ = v_maxHeartbeats_5111_;
v_quotContext_5128_ = v_quotContext_5112_;
v_currMacroScope_5129_ = v_currMacroScope_5113_;
v_cancelTk_x3f_5130_ = v_cancelTk_x3f_5114_;
v_inheritedTraceOptions_5131_ = v_inheritedTraceOptions_5115_;
v_currRecDepth_5132_ = v_currRecDepth_5102_;
v_ref_5133_ = v_ref_5103_;
v_suppressElabErrors_5134_ = v_suppressElabErrors_5104_;
v___y_5135_ = v___y_5098_;
goto v___jp_5121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed(lean_object* v___x_5164_, lean_object* v_value_5165_, lean_object* v___f_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_){
_start:
{
uint8_t v___x_5038__boxed_5172_; lean_object* v_res_5173_; 
v___x_5038__boxed_5172_ = lean_unbox(v___x_5164_);
v_res_5173_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(v___x_5038__boxed_5172_, v_value_5165_, v___f_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_);
lean_dec(v___y_5170_);
lean_dec_ref(v___y_5169_);
lean_dec(v___y_5168_);
lean_dec_ref(v___y_5167_);
return v_res_5173_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_5175_; lean_object* v___x_5176_; 
v___x_5175_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0));
v___x_5176_ = l_Lean_stringToMessageData(v___x_5175_);
return v___x_5176_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3(void){
_start:
{
lean_object* v___x_5178_; lean_object* v___x_5179_; 
v___x_5178_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__2));
v___x_5179_ = l_Lean_stringToMessageData(v___x_5178_);
return v___x_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object* v_preDef_5180_, lean_object* v_unaryPreDefName_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v_env_5189_; lean_object* v_levelParams_5190_; lean_object* v_declName_5191_; lean_object* v_value_5192_; lean_object* v_env_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___f_5203_; lean_object* v___x_5204_; lean_object* v___f_5205_; uint8_t v___x_5206_; lean_object* v___x_5207_; lean_object* v___f_5208_; lean_object* v___x_5209_; 
v___x_5187_ = lean_st_ref_get(v_a_5185_);
v___x_5188_ = lean_st_ref_get(v_a_5185_);
v_env_5189_ = lean_ctor_get(v___x_5187_, 0);
lean_inc_ref(v_env_5189_);
lean_dec(v___x_5187_);
v_levelParams_5190_ = lean_ctor_get(v_preDef_5180_, 1);
lean_inc(v_levelParams_5190_);
v_declName_5191_ = lean_ctor_get(v_preDef_5180_, 3);
lean_inc_n(v_declName_5191_, 2);
v_value_5192_ = lean_ctor_get(v_preDef_5180_, 7);
lean_inc_ref(v_value_5192_);
lean_dec_ref(v_preDef_5180_);
v_env_5193_ = lean_ctor_get(v___x_5188_, 0);
lean_inc_ref(v_env_5193_);
lean_dec(v___x_5188_);
v___x_5194_ = l_Lean_Meta_unfoldThmSuffix;
v___x_5195_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5189_, v_declName_5191_, v___x_5194_);
v___x_5196_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5193_, v_unaryPreDefName_5181_, v___x_5194_);
v___x_5197_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1);
lean_inc(v___x_5195_);
v___x_5198_ = l_Lean_MessageData_ofName(v___x_5195_);
v___x_5199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5197_);
lean_ctor_set(v___x_5199_, 1, v___x_5198_);
v___x_5200_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3);
v___x_5201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5199_);
lean_ctor_set(v___x_5201_, 1, v___x_5200_);
lean_inc(v___x_5196_);
v___x_5202_ = l_Lean_MessageData_ofName(v___x_5196_);
lean_inc_ref(v___x_5202_);
v___f_5203_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5203_, 0, v_levelParams_5190_);
lean_closure_set(v___f_5203_, 1, v_declName_5191_);
lean_closure_set(v___f_5203_, 2, v___x_5196_);
lean_closure_set(v___f_5203_, 3, v___x_5195_);
lean_closure_set(v___f_5203_, 4, v___x_5202_);
v___x_5204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5204_, 0, v___x_5201_);
lean_ctor_set(v___x_5204_, 1, v___x_5202_);
v___f_5205_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_5205_, 0, v___x_5204_);
v___x_5206_ = 0;
v___x_5207_ = lean_box(v___x_5206_);
v___f_5208_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_5208_, 0, v___x_5207_);
lean_closure_set(v___f_5208_, 1, v_value_5192_);
lean_closure_set(v___f_5208_, 2, v___f_5203_);
v___x_5209_ = l_Lean_Meta_mapErrorImp___redArg(v___f_5208_, v___f_5205_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5217_; 
v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5212_ = v___x_5209_;
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5209_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5215_; 
if (v_isShared_5213_ == 0)
{
v___x_5215_ = v___x_5212_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
else
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
v_a_5218_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5220_ = v___x_5209_;
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5209_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5223_; 
if (v_isShared_5221_ == 0)
{
v___x_5223_ = v___x_5220_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5218_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
return v___x_5223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___boxed(lean_object* v_preDef_5226_, lean_object* v_unaryPreDefName_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v_res_5233_; 
v_res_5233_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_preDef_5226_, v_unaryPreDefName_5227_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_);
lean_dec(v_a_5231_);
lean_dec_ref(v_a_5230_);
lean_dec(v_a_5229_);
lean_dec_ref(v_a_5228_);
return v_res_5233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5278_; uint8_t v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
v___x_5278_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5279_ = 0;
v___x_5280_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5281_ = l_Lean_registerTraceClass(v___x_5278_, v___x_5279_, v___x_5280_);
return v___x_5281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2____boxed(lean_object* v_a_5282_){
_start:
{
lean_object* v_res_5283_; 
v_res_5283_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_();
return v_res_5283_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_PreDefinition_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin);
}
#ifdef __cplusplus
}
#endif
