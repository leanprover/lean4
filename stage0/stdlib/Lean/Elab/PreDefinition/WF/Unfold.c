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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "_private.Lean.Elab.PreDefinition.WF.Unfold.0.Lean.Elab.WF.mkMatchArgPusher"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: altBodyType.isForall\n          "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "failed to finish proof for equational theorem for `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13;
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
lean_object* v___f_8_; lean_object* v___x_5021__overap_9_; lean_object* v___x_10_; 
v___f_8_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_5021__overap_9_ = lean_panic_fn_borrowed(v___f_8_, v_msg_2_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_10_ = lean_apply_5(v___x_5021__overap_9_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
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
uint8_t v___x_7431__boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v___x_7431__boxed_157_ = lean_unbox(v___x_155_);
v_res_158_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(v___x_7431__boxed_157_, v_x_156_);
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
uint8_t v___x_7439__boxed_188_; uint8_t v___x_7440__boxed_189_; lean_object* v_res_190_; 
v___x_7439__boxed_188_ = lean_unbox(v___x_179_);
v___x_7440__boxed_189_ = lean_unbox(v___x_180_);
v_res_190_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(v___x_177_, v___x_178_, v___x_7439__boxed_188_, v___x_7440__boxed_189_, v_ys_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
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
lean_object* v___x_197_; lean_object* v_env_198_; lean_object* v___x_199_; lean_object* v_mctx_200_; lean_object* v_lctx_201_; lean_object* v_options_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_197_ = lean_st_ref_get(v___y_195_);
v_env_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc_ref(v_env_198_);
lean_dec(v___x_197_);
v___x_199_ = lean_st_ref_get(v___y_193_);
v_mctx_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_ref(v_mctx_200_);
lean_dec(v___x_199_);
v_lctx_201_ = lean_ctor_get(v___y_192_, 2);
v_options_202_ = lean_ctor_get(v___y_194_, 2);
lean_inc_ref(v_options_202_);
lean_inc_ref(v_lctx_201_);
v___x_203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_203_, 0, v_env_198_);
lean_ctor_set(v___x_203_, 1, v_mctx_200_);
lean_ctor_set(v___x_203_, 2, v_lctx_201_);
lean_ctor_set(v___x_203_, 3, v_options_202_);
v___x_204_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_msgData_191_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4___boxed(lean_object* v_msgData_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msgData_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(lean_object* v_msg_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_ref_219_; lean_object* v___x_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
v_ref_219_ = lean_ctor_get(v___y_216_, 5);
v___x_220_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
lean_inc(v_ref_219_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v_ref_219_);
lean_ctor_set(v___x_225_, 1, v_a_221_);
if (v_isShared_224_ == 0)
{
lean_ctor_set_tag(v___x_223_, 1);
lean_ctor_set(v___x_223_, 0, v___x_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg___boxed(lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
lean_object* v_ks_241_; lean_object* v_vs_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_266_; 
v_ks_241_ = lean_ctor_get(v_x_237_, 0);
v_vs_242_ = lean_ctor_get(v_x_237_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_266_ == 0)
{
v___x_244_ = v_x_237_;
v_isShared_245_ = v_isSharedCheck_266_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_vs_242_);
lean_inc(v_ks_241_);
lean_dec(v_x_237_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_266_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = lean_array_get_size(v_ks_241_);
v___x_247_ = lean_nat_dec_lt(v_x_238_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
lean_dec(v_x_238_);
v___x_248_ = lean_array_push(v_ks_241_, v_x_239_);
v___x_249_ = lean_array_push(v_vs_242_, v_x_240_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_249_);
lean_ctor_set(v___x_244_, 0, v___x_248_);
v___x_251_ = v___x_244_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
else
{
lean_object* v_k_x27_253_; uint8_t v___x_254_; 
v_k_x27_253_ = lean_array_fget_borrowed(v_ks_241_, v_x_238_);
v___x_254_ = l_Lean_instBEqMVarId_beq(v_x_239_, v_k_x27_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_256_; 
if (v_isShared_245_ == 0)
{
v___x_256_ = v___x_244_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_ks_241_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_vs_242_);
v___x_256_ = v_reuseFailAlloc_260_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_x_238_, v___x_257_);
lean_dec(v_x_238_);
v_x_237_ = v___x_256_;
v_x_238_ = v___x_258_;
goto _start;
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_261_ = lean_array_fset(v_ks_241_, v_x_238_, v_x_239_);
v___x_262_ = lean_array_fset(v_vs_242_, v_x_238_, v_x_240_);
lean_dec(v_x_238_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_262_);
lean_ctor_set(v___x_244_, 0, v___x_261_);
v___x_264_ = v___x_244_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_n_267_, lean_object* v_k_268_, lean_object* v_v_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_267_, v___x_270_, v_k_268_, v_v_269_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(lean_object* v_x_273_, size_t v_x_274_, size_t v_x_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
if (lean_obj_tag(v_x_273_) == 0)
{
lean_object* v_es_278_; size_t v___x_279_; size_t v___x_280_; lean_object* v_j_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_es_278_ = lean_ctor_get(v_x_273_, 0);
v___x_279_ = ((size_t)31ULL);
v___x_280_ = lean_usize_land(v_x_274_, v___x_279_);
v_j_281_ = lean_usize_to_nat(v___x_280_);
v___x_282_ = lean_array_get_size(v_es_278_);
v___x_283_ = lean_nat_dec_lt(v_j_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_dec(v_j_281_);
lean_dec(v_x_277_);
lean_dec(v_x_276_);
return v_x_273_;
}
else
{
lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_322_; 
lean_inc_ref(v_es_278_);
v_isSharedCheck_322_ = !lean_is_exclusive(v_x_273_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; 
v_unused_323_ = lean_ctor_get(v_x_273_, 0);
lean_dec(v_unused_323_);
v___x_285_ = v_x_273_;
v_isShared_286_ = v_isSharedCheck_322_;
goto v_resetjp_284_;
}
else
{
lean_dec(v_x_273_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_322_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_v_287_; lean_object* v___x_288_; lean_object* v_xs_x27_289_; lean_object* v___y_291_; 
v_v_287_ = lean_array_fget(v_es_278_, v_j_281_);
v___x_288_ = lean_box(0);
v_xs_x27_289_ = lean_array_fset(v_es_278_, v_j_281_, v___x_288_);
switch(lean_obj_tag(v_v_287_))
{
case 0:
{
lean_object* v_key_296_; lean_object* v_val_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_307_; 
v_key_296_ = lean_ctor_get(v_v_287_, 0);
v_val_297_ = lean_ctor_get(v_v_287_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_v_287_);
if (v_isSharedCheck_307_ == 0)
{
v___x_299_ = v_v_287_;
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_val_297_);
lean_inc(v_key_296_);
lean_dec(v_v_287_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_instBEqMVarId_beq(v_x_276_, v_key_296_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_del_object(v___x_299_);
v___x_302_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_296_, v_val_297_, v_x_276_, v_x_277_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
v___y_291_ = v___x_303_;
goto v___jp_290_;
}
else
{
lean_object* v___x_305_; 
lean_dec(v_val_297_);
lean_dec(v_key_296_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_x_277_);
lean_ctor_set(v___x_299_, 0, v_x_276_);
v___x_305_ = v___x_299_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_x_276_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_x_277_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
v___y_291_ = v___x_305_;
goto v___jp_290_;
}
}
}
}
case 1:
{
lean_object* v_node_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_320_; 
v_node_308_ = lean_ctor_get(v_v_287_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_v_287_);
if (v_isSharedCheck_320_ == 0)
{
v___x_310_ = v_v_287_;
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_node_308_);
lean_dec(v_v_287_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_312_ = ((size_t)5ULL);
v___x_313_ = lean_usize_shift_right(v_x_274_, v___x_312_);
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_add(v_x_275_, v___x_314_);
v___x_316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_node_308_, v___x_313_, v___x_315_, v_x_276_, v_x_277_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_316_);
v___x_318_ = v___x_310_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
v___y_291_ = v___x_318_;
goto v___jp_290_;
}
}
}
default: 
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_x_276_);
lean_ctor_set(v___x_321_, 1, v_x_277_);
v___y_291_ = v___x_321_;
goto v___jp_290_;
}
}
v___jp_290_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_array_fset(v_xs_x27_289_, v_j_281_, v___y_291_);
lean_dec(v_j_281_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_292_);
v___x_294_ = v___x_285_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
else
{
lean_object* v_ks_324_; lean_object* v_vs_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_345_; 
v_ks_324_ = lean_ctor_get(v_x_273_, 0);
v_vs_325_ = lean_ctor_get(v_x_273_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_273_);
if (v_isSharedCheck_345_ == 0)
{
v___x_327_ = v_x_273_;
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_vs_325_);
lean_inc(v_ks_324_);
lean_dec(v_x_273_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_ks_324_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_vs_325_);
v___x_330_ = v_reuseFailAlloc_344_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v_newNode_331_; uint8_t v___y_333_; size_t v___x_339_; uint8_t v___x_340_; 
v_newNode_331_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v___x_330_, v_x_276_, v_x_277_);
v___x_339_ = ((size_t)7ULL);
v___x_340_ = lean_usize_dec_le(v___x_339_, v_x_275_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_341_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_331_);
v___x_342_ = lean_unsigned_to_nat(4u);
v___x_343_ = lean_nat_dec_lt(v___x_341_, v___x_342_);
lean_dec(v___x_341_);
v___y_333_ = v___x_343_;
goto v___jp_332_;
}
else
{
v___y_333_ = v___x_340_;
goto v___jp_332_;
}
v___jp_332_:
{
if (v___y_333_ == 0)
{
lean_object* v_ks_334_; lean_object* v_vs_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_ks_334_ = lean_ctor_get(v_newNode_331_, 0);
lean_inc_ref(v_ks_334_);
v_vs_335_ = lean_ctor_get(v_newNode_331_, 1);
lean_inc_ref(v_vs_335_);
lean_dec_ref(v_newNode_331_);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_x_275_, v_ks_334_, v_vs_335_, v___x_336_, v___x_337_);
lean_dec_ref(v_vs_335_);
lean_dec_ref(v_ks_334_);
return v___x_338_;
}
else
{
return v_newNode_331_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_346_, lean_object* v_keys_347_, lean_object* v_vals_348_, lean_object* v_i_349_, lean_object* v_entries_350_){
_start:
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = lean_array_get_size(v_keys_347_);
v___x_352_ = lean_nat_dec_lt(v_i_349_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec(v_i_349_);
return v_entries_350_;
}
else
{
lean_object* v_k_353_; lean_object* v_v_354_; uint64_t v___x_355_; size_t v_h_356_; size_t v___x_357_; lean_object* v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v_h_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_k_353_ = lean_array_fget_borrowed(v_keys_347_, v_i_349_);
v_v_354_ = lean_array_fget_borrowed(v_vals_348_, v_i_349_);
v___x_355_ = l_Lean_instHashableMVarId_hash(v_k_353_);
v_h_356_ = lean_uint64_to_usize(v___x_355_);
v___x_357_ = ((size_t)5ULL);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_sub(v_depth_346_, v___x_359_);
v___x_361_ = lean_usize_mul(v___x_357_, v___x_360_);
v_h_362_ = lean_usize_shift_right(v_h_356_, v___x_361_);
v___x_363_ = lean_nat_add(v_i_349_, v___x_358_);
lean_dec(v_i_349_);
lean_inc(v_v_354_);
lean_inc(v_k_353_);
v___x_364_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_entries_350_, v_h_362_, v_depth_346_, v_k_353_, v_v_354_);
v_i_349_ = v___x_363_;
v_entries_350_ = v___x_364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_366_, lean_object* v_keys_367_, lean_object* v_vals_368_, lean_object* v_i_369_, lean_object* v_entries_370_){
_start:
{
size_t v_depth_boxed_371_; lean_object* v_res_372_; 
v_depth_boxed_371_ = lean_unbox_usize(v_depth_366_);
lean_dec(v_depth_366_);
v_res_372_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_371_, v_keys_367_, v_vals_368_, v_i_369_, v_entries_370_);
lean_dec_ref(v_vals_368_);
lean_dec_ref(v_keys_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
size_t v_x_7617__boxed_378_; size_t v_x_7618__boxed_379_; lean_object* v_res_380_; 
v_x_7617__boxed_378_ = lean_unbox_usize(v_x_374_);
lean_dec(v_x_374_);
v_x_7618__boxed_379_ = lean_unbox_usize(v_x_375_);
lean_dec(v_x_375_);
v_res_380_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_373_, v_x_7617__boxed_378_, v_x_7618__boxed_379_, v_x_376_, v_x_377_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
uint64_t v___x_384_; size_t v___x_385_; size_t v___x_386_; lean_object* v___x_387_; 
v___x_384_ = l_Lean_instHashableMVarId_hash(v_x_382_);
v___x_385_ = lean_uint64_to_usize(v___x_384_);
v___x_386_ = ((size_t)1ULL);
v___x_387_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_381_, v___x_385_, v___x_386_, v_x_382_, v_x_383_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(lean_object* v_mvarId_388_, lean_object* v_val_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; lean_object* v_mctx_393_; lean_object* v_cache_394_; lean_object* v_zetaDeltaFVarIds_395_; lean_object* v_postponed_396_; lean_object* v_diag_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_426_; 
v___x_392_ = lean_st_ref_take(v___y_390_);
v_mctx_393_ = lean_ctor_get(v___x_392_, 0);
v_cache_394_ = lean_ctor_get(v___x_392_, 1);
v_zetaDeltaFVarIds_395_ = lean_ctor_get(v___x_392_, 2);
v_postponed_396_ = lean_ctor_get(v___x_392_, 3);
v_diag_397_ = lean_ctor_get(v___x_392_, 4);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_426_ == 0)
{
v___x_399_ = v___x_392_;
v_isShared_400_ = v_isSharedCheck_426_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_diag_397_);
lean_inc(v_postponed_396_);
lean_inc(v_zetaDeltaFVarIds_395_);
lean_inc(v_cache_394_);
lean_inc(v_mctx_393_);
lean_dec(v___x_392_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_426_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_depth_401_; lean_object* v_levelAssignDepth_402_; lean_object* v_lmvarCounter_403_; lean_object* v_mvarCounter_404_; lean_object* v_lDecls_405_; lean_object* v_decls_406_; lean_object* v_userNames_407_; lean_object* v_lAssignment_408_; lean_object* v_eAssignment_409_; lean_object* v_dAssignment_410_; lean_object* v_instanceTypedMVars_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_425_; 
v_depth_401_ = lean_ctor_get(v_mctx_393_, 0);
v_levelAssignDepth_402_ = lean_ctor_get(v_mctx_393_, 1);
v_lmvarCounter_403_ = lean_ctor_get(v_mctx_393_, 2);
v_mvarCounter_404_ = lean_ctor_get(v_mctx_393_, 3);
v_lDecls_405_ = lean_ctor_get(v_mctx_393_, 4);
v_decls_406_ = lean_ctor_get(v_mctx_393_, 5);
v_userNames_407_ = lean_ctor_get(v_mctx_393_, 6);
v_lAssignment_408_ = lean_ctor_get(v_mctx_393_, 7);
v_eAssignment_409_ = lean_ctor_get(v_mctx_393_, 8);
v_dAssignment_410_ = lean_ctor_get(v_mctx_393_, 9);
v_instanceTypedMVars_411_ = lean_ctor_get(v_mctx_393_, 10);
v_isSharedCheck_425_ = !lean_is_exclusive(v_mctx_393_);
if (v_isSharedCheck_425_ == 0)
{
v___x_413_ = v_mctx_393_;
v_isShared_414_ = v_isSharedCheck_425_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_instanceTypedMVars_411_);
lean_inc(v_dAssignment_410_);
lean_inc(v_eAssignment_409_);
lean_inc(v_lAssignment_408_);
lean_inc(v_userNames_407_);
lean_inc(v_decls_406_);
lean_inc(v_lDecls_405_);
lean_inc(v_mvarCounter_404_);
lean_inc(v_lmvarCounter_403_);
lean_inc(v_levelAssignDepth_402_);
lean_inc(v_depth_401_);
lean_dec(v_mctx_393_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_425_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_eAssignment_409_, v_mvarId_388_, v_val_389_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 8, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_depth_401_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_levelAssignDepth_402_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_lmvarCounter_403_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_mvarCounter_404_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_lDecls_405_);
lean_ctor_set(v_reuseFailAlloc_424_, 5, v_decls_406_);
lean_ctor_set(v_reuseFailAlloc_424_, 6, v_userNames_407_);
lean_ctor_set(v_reuseFailAlloc_424_, 7, v_lAssignment_408_);
lean_ctor_set(v_reuseFailAlloc_424_, 8, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_424_, 9, v_dAssignment_410_);
lean_ctor_set(v_reuseFailAlloc_424_, 10, v_instanceTypedMVars_411_);
v___x_417_ = v_reuseFailAlloc_424_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_419_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_417_);
v___x_419_ = v___x_399_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_cache_394_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_zetaDeltaFVarIds_395_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_postponed_396_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_diag_397_);
v___x_419_ = v_reuseFailAlloc_423_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_st_ref_put(v___y_390_, v___x_419_);
v___x_421_ = lean_box(0);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg___boxed(lean_object* v_mvarId_427_, lean_object* v_val_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_427_, v_val_428_, v___y_429_);
lean_dec(v___y_429_);
return v_res_431_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_438_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4));
v___x_439_ = lean_unsigned_to_nat(41u);
v___x_440_ = lean_unsigned_to_nat(34u);
v___x_441_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3));
v___x_442_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_443_ = l_mkPanicMessageWithDecl(v___x_442_, v___x_441_, v___x_440_, v___x_439_, v___x_438_);
return v___x_443_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9));
v___x_451_ = l_Lean_stringToMessageData(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18(void){
_start:
{
lean_object* v___x_466_; lean_object* v_dummy_467_; 
v___x_466_ = lean_box(0);
v_dummy_467_ = l_Lean_Expr_sort___override(v___x_466_);
return v_dummy_467_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object* v_mvarId_475_, lean_object* v___x_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; 
lean_inc(v_mvarId_475_);
v___x_482_ = l_Lean_MVarId_getType_x27(v_mvarId_475_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_485_ = lean_unsigned_to_nat(3u);
v___x_486_ = l_Lean_Expr_isAppOfArity(v_a_483_, v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v_a_483_);
lean_dec_ref(v___x_476_);
lean_dec(v_mvarId_475_);
v___x_487_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5);
v___x_488_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(v___x_487_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v___f_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; lean_object* v___x_494_; 
v___x_489_ = lean_box(v___x_486_);
v___f_490_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_490_, 0, v___x_489_);
v___x_491_ = l_Lean_Expr_appFn_x21(v_a_483_);
v___x_492_ = l_Lean_Expr_appArg_x21(v___x_491_);
lean_dec_ref(v___x_491_);
v___x_493_ = 0;
lean_inc_ref(v___x_492_);
v___x_494_ = l_Lean_Meta_delta_x3f(v___x_492_, v___f_490_, v___x_493_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref_known(v___x_494_, 1);
if (lean_obj_tag(v_a_495_) == 1)
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_649_; 
v_val_496_ = lean_ctor_get(v_a_495_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v_a_495_);
if (v_isSharedCheck_649_ == 0)
{
v___x_498_ = v_a_495_;
v_isShared_499_ = v_isSharedCheck_649_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_val_496_);
lean_dec(v_a_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_649_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; 
lean_inc(v_val_496_);
v___x_500_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_val_496_, v___y_478_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___f_504_; lean_object* v___x_505_; lean_object* v_h_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___x_602_; uint8_t v___x_603_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v___x_502_ = lean_box(v___x_493_);
v___x_503_ = lean_box(v___x_486_);
v___f_504_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed), 11, 4);
lean_closure_set(v___f_504_, 0, v___x_492_);
lean_closure_set(v___f_504_, 1, v___x_476_);
lean_closure_set(v___f_504_, 2, v___x_502_);
lean_closure_set(v___f_504_, 3, v___x_503_);
v___x_505_ = l_Lean_Expr_appArg_x21(v_a_483_);
lean_dec(v_a_483_);
v___x_602_ = l_Lean_Expr_cleanupAnnotations(v_a_501_);
v___x_603_ = l_Lean_Expr_isApp(v___x_602_);
if (v___x_603_ == 0)
{
lean_dec_ref(v___x_602_);
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
v___y_584_ = v___y_480_;
goto v___jp_580_;
}
else
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = l_Lean_Expr_appFnCleanup___redArg(v___x_602_);
v___x_605_ = l_Lean_Expr_isApp(v___x_604_);
if (v___x_605_ == 0)
{
lean_dec_ref(v___x_604_);
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
v___y_584_ = v___y_480_;
goto v___jp_580_;
}
else
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = l_Lean_Expr_appFnCleanup___redArg(v___x_604_);
v___x_607_ = l_Lean_Expr_isApp(v___x_606_);
if (v___x_607_ == 0)
{
lean_dec_ref(v___x_606_);
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
v___y_584_ = v___y_480_;
goto v___jp_580_;
}
else
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = l_Lean_Expr_appFnCleanup___redArg(v___x_606_);
v___x_609_ = l_Lean_Expr_isApp(v___x_608_);
if (v___x_609_ == 0)
{
lean_dec_ref(v___x_608_);
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
v___y_584_ = v___y_480_;
goto v___jp_580_;
}
else
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = l_Lean_Expr_appFnCleanup___redArg(v___x_608_);
v___x_611_ = l_Lean_Expr_isApp(v___x_610_);
if (v___x_611_ == 0)
{
lean_dec_ref(v___x_610_);
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
v___y_584_ = v___y_480_;
goto v___jp_580_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_610_);
v___x_613_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14));
v___x_614_ = l_Lean_Expr_isConstOf(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
uint8_t v___x_615_; 
v___x_615_ = l_Lean_Expr_isApp(v___x_612_);
if (v___x_615_ == 0)
{
lean_dec_ref(v___x_612_);
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
v___y_584_ = v___y_480_;
goto v___jp_580_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_616_ = l_Lean_Expr_appFnCleanup___redArg(v___x_612_);
v___x_617_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15));
v___x_618_ = l_Lean_Expr_isConstOf(v___x_616_, v___x_617_);
lean_dec_ref(v___x_616_);
if (v___x_618_ == 0)
{
v___y_581_ = v___y_477_;
v___y_582_ = v___y_478_;
v___y_583_ = v___y_479_;
v___y_584_ = v___y_480_;
goto v___jp_580_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_dummy_623_; lean_object* v_nargs_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_del_object(v___x_498_);
v___x_619_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17));
v___x_620_ = l_Lean_Expr_getAppFn(v_val_496_);
v___x_621_ = l_Lean_Expr_constLevels_x21(v___x_620_);
lean_dec_ref(v___x_620_);
v___x_622_ = l_Lean_mkConst(v___x_619_, v___x_621_);
v_dummy_623_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_624_ = l_Lean_Expr_getAppNumArgs(v_val_496_);
lean_inc(v_nargs_624_);
v___x_625_ = lean_mk_array(v_nargs_624_, v_dummy_623_);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_sub(v_nargs_624_, v___x_626_);
lean_dec(v_nargs_624_);
lean_inc(v_val_496_);
v___x_628_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_496_, v___x_625_, v___x_627_);
v___x_629_ = l_Lean_mkAppN(v___x_622_, v___x_628_);
lean_dec_ref(v___x_628_);
v_h_507_ = v___x_629_;
v___y_508_ = v___y_477_;
v___y_509_ = v___y_478_;
v___y_510_ = v___y_479_;
v___y_511_ = v___y_480_;
goto v___jp_506_;
}
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_dummy_634_; lean_object* v_nargs_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec_ref(v___x_612_);
lean_del_object(v___x_498_);
v___x_630_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19));
v___x_631_ = l_Lean_Expr_getAppFn(v_val_496_);
v___x_632_ = l_Lean_Expr_constLevels_x21(v___x_631_);
lean_dec_ref(v___x_631_);
v___x_633_ = l_Lean_mkConst(v___x_630_, v___x_632_);
v_dummy_634_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_635_ = l_Lean_Expr_getAppNumArgs(v_val_496_);
lean_inc(v_nargs_635_);
v___x_636_ = lean_mk_array(v_nargs_635_, v_dummy_634_);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_nat_sub(v_nargs_635_, v___x_637_);
lean_dec(v_nargs_635_);
lean_inc(v_val_496_);
v___x_639_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_496_, v___x_636_, v___x_638_);
v___x_640_ = l_Lean_mkAppN(v___x_633_, v___x_639_);
lean_dec_ref(v___x_639_);
v_h_507_ = v___x_640_;
v___y_508_ = v___y_477_;
v___y_509_ = v___y_478_;
v___y_510_ = v___y_479_;
v___y_511_ = v___y_480_;
goto v___jp_506_;
}
}
}
}
}
}
v___jp_506_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_512_ = l_Lean_Expr_appFn_x21(v_val_496_);
v___x_513_ = l_Lean_Expr_appArg_x21(v___x_512_);
lean_dec_ref(v___x_512_);
v___x_514_ = l_Lean_Expr_appArg_x21(v_val_496_);
lean_dec(v_val_496_);
lean_inc_ref(v___x_514_);
lean_inc_ref(v___x_513_);
v___x_515_ = l_Lean_Expr_app___override(v___x_513_, v___x_514_);
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
lean_inc(v___y_509_);
lean_inc_ref(v___y_508_);
v___x_516_ = lean_infer_type(v___x_515_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = l_Lean_Expr_bindingDomain_x21(v_a_517_);
lean_dec(v_a_517_);
v___x_519_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_520_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_518_, v___x_519_, v___f_504_, v___x_493_, v___x_493_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
v___x_522_ = l_Lean_mkAppB(v___x_513_, v___x_514_, v_a_521_);
v___x_523_ = l_Lean_Meta_mkEq(v___x_522_, v___x_505_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = lean_box(0);
v___x_526_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_524_, v___x_525_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc_n(v_a_527_, 2);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = l_Lean_Meta_mkEqTrans(v_h_507_, v_a_527_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec_ref(v___y_508_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_538_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_475_, v_a_529_, v___y_509_);
lean_dec(v___y_509_);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v___x_530_, 0);
lean_dec(v_unused_539_);
v___x_532_ = v___x_530_;
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
else
{
lean_dec(v___x_530_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = l_Lean_Expr_mvarId_x21(v_a_527_);
lean_dec(v_a_527_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_a_527_);
lean_dec(v___y_509_);
lean_dec(v_mvarId_475_);
v_a_540_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_528_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_528_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_h_507_);
lean_dec(v_mvarId_475_);
v_a_548_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_526_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_526_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_h_507_);
lean_dec(v_mvarId_475_);
v_a_556_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_523_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_523_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v___x_514_);
lean_dec_ref(v___x_513_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_h_507_);
lean_dec_ref(v___x_505_);
lean_dec(v_mvarId_475_);
v_a_564_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_520_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_520_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec_ref(v___x_514_);
lean_dec_ref(v___x_513_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_h_507_);
lean_dec_ref(v___x_505_);
lean_dec_ref(v___f_504_);
lean_dec(v_mvarId_475_);
v_a_572_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_516_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_516_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
v___jp_580_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_585_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8));
v___x_586_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10);
lean_inc(v_val_496_);
v___x_587_ = l_Lean_MessageData_ofExpr(v_val_496_);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_588_);
v___x_590_ = v___x_498_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_601_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; 
lean_inc(v_mvarId_475_);
v___x_591_ = l_Lean_Meta_throwTacticEx___redArg(v___x_585_, v_mvarId_475_, v___x_590_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v_h_507_ = v_a_592_;
v___y_508_ = v___y_581_;
v___y_509_ = v___y_582_;
v___y_510_ = v___y_583_;
v___y_511_ = v___y_584_;
goto v___jp_506_;
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec_ref(v___x_505_);
lean_dec_ref(v___f_504_);
lean_dec(v_val_496_);
lean_dec(v_mvarId_475_);
v_a_593_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_591_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_591_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_del_object(v___x_498_);
lean_dec(v_val_496_);
lean_dec_ref(v___x_492_);
lean_dec(v_a_483_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec_ref(v___x_476_);
lean_dec(v_mvarId_475_);
v_a_641_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_500_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_500_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_a_495_);
lean_dec(v_a_483_);
lean_dec_ref(v___x_476_);
lean_dec(v_mvarId_475_);
v___x_650_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21);
v___x_651_ = l_Lean_MessageData_ofExpr(v___x_492_);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_652_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v___x_653_;
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v___x_492_);
lean_dec(v_a_483_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec_ref(v___x_476_);
lean_dec(v_mvarId_475_);
v_a_654_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_494_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_494_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec_ref(v___x_476_);
lean_dec(v_mvarId_475_);
v_a_662_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_482_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_482_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed(lean_object* v_mvarId_670_, lean_object* v___x_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(v_mvarId_670_, v___x_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(lean_object* v_mvarId_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_684_; lean_object* v___f_685_; lean_object* v___x_686_; 
v___x_684_ = l_Lean_instInhabitedExpr;
lean_inc(v_mvarId_678_);
v___f_685_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed), 7, 2);
lean_closure_set(v___f_685_, 0, v_mvarId_678_);
lean_closure_set(v___f_685_, 1, v___x_684_);
v___x_686_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(v_mvarId_678_, v___f_685_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___boxed(lean_object* v_mvarId_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(lean_object* v_mvarId_694_, lean_object* v_val_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_694_, v_val_695_, v___y_697_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___boxed(lean_object* v_mvarId_702_, lean_object* v_val_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(v_mvarId_702_, v_val_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(lean_object* v_00_u03b1_710_, lean_object* v_msg_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___boxed(lean_object* v_00_u03b1_718_, lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(v_00_u03b1_718_, v_msg_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2(lean_object* v_00_u03b2_726_, lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_x_727_, v_x_728_, v_x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_731_, lean_object* v_x_732_, size_t v_x_733_, size_t v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_732_, v_x_733_, v_x_734_, v_x_735_, v_x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_738_, lean_object* v_x_739_, lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
size_t v_x_8396__boxed_744_; size_t v_x_8397__boxed_745_; lean_object* v_res_746_; 
v_x_8396__boxed_744_ = lean_unbox_usize(v_x_740_);
lean_dec(v_x_740_);
v_x_8397__boxed_745_ = lean_unbox_usize(v_x_741_);
lean_dec(v_x_741_);
v_res_746_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(v_00_u03b2_738_, v_x_739_, v_x_8396__boxed_744_, v_x_8397__boxed_745_, v_x_742_, v_x_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_747_, lean_object* v_n_748_, lean_object* v_k_749_, lean_object* v_v_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v_n_748_, v_k_749_, v_v_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_752_, size_t v_depth_753_, lean_object* v_keys_754_, lean_object* v_vals_755_, lean_object* v_heq_756_, lean_object* v_i_757_, lean_object* v_entries_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_753_, v_keys_754_, v_vals_755_, v_i_757_, v_entries_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_760_, lean_object* v_depth_761_, lean_object* v_keys_762_, lean_object* v_vals_763_, lean_object* v_heq_764_, lean_object* v_i_765_, lean_object* v_entries_766_){
_start:
{
size_t v_depth_boxed_767_; lean_object* v_res_768_; 
v_depth_boxed_767_ = lean_unbox_usize(v_depth_761_);
lean_dec(v_depth_761_);
v_res_768_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_760_, v_depth_boxed_767_, v_keys_762_, v_vals_763_, v_heq_764_, v_i_765_, v_entries_766_);
lean_dec_ref(v_vals_763_);
lean_dec_ref(v_keys_762_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_769_, lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_770_, v_x_771_, v_x_772_, v_x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(lean_object* v_e_775_, lean_object* v_maxFVars_776_, lean_object* v_k_777_, uint8_t v_cleanupAnnotations_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___f_784_; uint8_t v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___f_784_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_784_, 0, v_k_777_);
v___x_785_ = 1;
v___x_786_ = 0;
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v_maxFVars_776_);
v___x_788_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_775_, v___x_785_, v___x_786_, v___x_785_, v___x_786_, v___x_787_, v___f_784_, v_cleanupAnnotations_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec_ref_known(v___x_787_, 1);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_788_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_788_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg___boxed(lean_object* v_e_805_, lean_object* v_maxFVars_806_, lean_object* v_k_807_, lean_object* v_cleanupAnnotations_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_814_; lean_object* v_res_815_; 
v_cleanupAnnotations_boxed_814_ = lean_unbox(v_cleanupAnnotations_808_);
v_res_815_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_805_, v_maxFVars_806_, v_k_807_, v_cleanupAnnotations_boxed_814_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(lean_object* v_00_u03b1_816_, lean_object* v_e_817_, lean_object* v_maxFVars_818_, lean_object* v_k_819_, uint8_t v_cleanupAnnotations_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_817_, v_maxFVars_818_, v_k_819_, v_cleanupAnnotations_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___boxed(lean_object* v_00_u03b1_827_, lean_object* v_e_828_, lean_object* v_maxFVars_829_, lean_object* v_k_830_, lean_object* v_cleanupAnnotations_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_837_; lean_object* v_res_838_; 
v_cleanupAnnotations_boxed_837_ = lean_unbox(v_cleanupAnnotations_831_);
v_res_838_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(v_00_u03b1_827_, v_e_828_, v_maxFVars_829_, v_k_830_, v_cleanupAnnotations_boxed_837_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(lean_object* v___x_839_, lean_object* v_xs_840_, lean_object* v_t_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
uint8_t v___y_851_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_874_ = lean_array_get_size(v_xs_840_);
v___x_875_ = lean_nat_dec_eq(v___x_874_, v___x_839_);
if (v___x_875_ == 0)
{
v___y_851_ = v___x_875_;
goto v___jp_850_;
}
else
{
uint8_t v___x_876_; 
v___x_876_ = l_Lean_Expr_isForall(v_t_841_);
v___y_851_ = v___x_876_;
goto v___jp_850_;
}
v___jp_847_:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_box(0);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
v___jp_850_:
{
if (v___y_851_ == 0)
{
goto v___jp_847_;
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_852_ = l_Lean_Expr_bindingBody_x21(v_t_841_);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_expr_has_loose_bvar(v___x_852_, v___x_853_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; lean_object* v___x_856_; 
v___x_855_ = 1;
v___x_856_ = l_Lean_Meta_mkLambdaFVars(v_xs_840_, v___x_852_, v___x_854_, v___y_851_, v___x_854_, v___y_851_, v___x_855_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
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
goto v___jp_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed(lean_object* v___x_877_, lean_object* v_xs_878_, lean_object* v_t_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(v___x_877_, v_xs_878_, v_t_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec_ref(v_t_879_);
lean_dec_ref(v_xs_878_);
lean_dec(v___x_877_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(lean_object* v_matcherApp_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_motive_892_; lean_object* v_discrs_893_; lean_object* v___x_894_; lean_object* v___f_895_; uint8_t v___x_896_; lean_object* v___x_897_; 
v_motive_892_ = lean_ctor_get(v_matcherApp_886_, 4);
lean_inc_ref(v_motive_892_);
v_discrs_893_ = lean_ctor_get(v_matcherApp_886_, 5);
lean_inc_ref(v_discrs_893_);
lean_dec_ref(v_matcherApp_886_);
v___x_894_ = lean_array_get_size(v_discrs_893_);
lean_dec_ref(v_discrs_893_);
v___f_895_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed), 8, 1);
lean_closure_set(v___f_895_, 0, v___x_894_);
v___x_896_ = 0;
v___x_897_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_motive_892_, v___x_894_, v___f_895_, v___x_896_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___boxed(lean_object* v_matcherApp_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_matcherApp_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(lean_object* v_e_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v_env_909_; uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_908_ = lean_st_ref_get(v___y_906_);
v_env_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc_ref(v_env_909_);
lean_dec(v___x_908_);
v___x_910_ = l_Lean_Meta_isMatcherAppCore(v_env_909_, v_e_905_);
v___x_911_ = lean_box(v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg___boxed(lean_object* v_e_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v_e_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(lean_object* v_e_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_917_, v___y_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___boxed(lean_object* v_e_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(v_e_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_e_924_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(lean_object* v_msg_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___f_937_; lean_object* v___x_788__overap_938_; lean_object* v___x_939_; 
v___f_937_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_788__overap_938_ = lean_panic_fn_borrowed(v___f_937_, v_msg_931_);
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
lean_inc(v___y_933_);
lean_inc_ref(v___y_932_);
v___x_939_ = lean_apply_5(v___x_788__overap_938_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, lean_box(0));
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1___boxed(lean_object* v_msg_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v_msg_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(size_t v_sz_947_, size_t v_i_948_, lean_object* v_bs_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = lean_usize_dec_lt(v_i_948_, v_sz_947_);
if (v___x_950_ == 0)
{
return v_bs_949_;
}
else
{
lean_object* v_v_951_; lean_object* v_toInductionSubgoal_952_; lean_object* v_mvarId_953_; lean_object* v___x_954_; lean_object* v_bs_x27_955_; size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v_v_951_ = lean_array_uget_borrowed(v_bs_949_, v_i_948_);
v_toInductionSubgoal_952_ = lean_ctor_get(v_v_951_, 0);
v_mvarId_953_ = lean_ctor_get(v_toInductionSubgoal_952_, 0);
lean_inc(v_mvarId_953_);
v___x_954_ = lean_unsigned_to_nat(0u);
v_bs_x27_955_ = lean_array_uset(v_bs_949_, v_i_948_, v___x_954_);
v___x_956_ = ((size_t)1ULL);
v___x_957_ = lean_usize_add(v_i_948_, v___x_956_);
v___x_958_ = lean_array_uset(v_bs_x27_955_, v_i_948_, v_mvarId_953_);
v_i_948_ = v___x_957_;
v_bs_949_ = v___x_958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2___boxed(lean_object* v_sz_960_, lean_object* v_i_961_, lean_object* v_bs_962_){
_start:
{
size_t v_sz_boxed_963_; size_t v_i_boxed_964_; lean_object* v_res_965_; 
v_sz_boxed_963_ = lean_unbox_usize(v_sz_960_);
lean_dec(v_sz_960_);
v_i_boxed_964_ = lean_unbox_usize(v_i_961_);
lean_dec(v_i_961_);
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_boxed_963_, v_i_boxed_964_, v_bs_962_);
return v_res_965_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1));
v___x_969_ = lean_unsigned_to_nat(4u);
v___x_970_ = lean_unsigned_to_nat(79u);
v___x_971_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0));
v___x_972_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_973_ = l_mkPanicMessageWithDecl(v___x_972_, v___x_971_, v___x_970_, v___x_969_, v___x_968_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(lean_object* v_mvarId_976_, lean_object* v_e_977_, lean_object* v_matcherInfo_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_984_; lean_object* v_a_985_; uint8_t v___x_986_; 
v___x_984_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_977_, v_a_982_);
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_984_);
v___x_986_ = lean_unbox(v_a_985_);
if (v___x_986_ == 0)
{
lean_object* v_numParams_987_; lean_object* v_numDiscrs_988_; lean_object* v_nargs_989_; lean_object* v___x_990_; lean_object* v_dummy_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_numParams_987_ = lean_ctor_get(v_matcherInfo_978_, 0);
v_numDiscrs_988_ = lean_ctor_get(v_matcherInfo_978_, 1);
v_nargs_989_ = l_Lean_Expr_getAppNumArgs(v_e_977_);
v___x_990_ = l_Lean_instInhabitedExpr;
v_dummy_991_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_989_);
v___x_992_ = lean_mk_array(v_nargs_989_, v_dummy_991_);
v___x_993_ = lean_unsigned_to_nat(1u);
v___x_994_ = lean_nat_sub(v_nargs_989_, v___x_993_);
lean_dec(v_nargs_989_);
v___x_995_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_977_, v___x_992_, v___x_994_);
v___x_996_ = lean_nat_add(v_numParams_987_, v_numDiscrs_988_);
v___x_997_ = lean_array_get(v___x_990_, v___x_995_, v___x_996_);
lean_dec(v___x_996_);
lean_dec_ref(v___x_995_);
v___x_998_ = l_Lean_Expr_isFVar(v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec(v___x_997_);
lean_dec(v_a_985_);
lean_dec(v_mvarId_976_);
v___x_999_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2);
v___x_1000_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v___x_999_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1001_ = l_Lean_Expr_fvarId_x21(v___x_997_);
lean_dec(v___x_997_);
v___x_1002_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3));
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_unbox(v_a_985_);
lean_dec(v_a_985_);
v___x_1005_ = l_Lean_MVarId_cases(v_mvarId_976_, v___x_1001_, v___x_1002_, v___x_1004_, v___x_1003_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1017_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
size_t v_sz_1010_; size_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v_sz_1010_ = lean_array_size(v_a_1006_);
v___x_1011_ = ((size_t)0ULL);
v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_1010_, v___x_1011_, v_a_1006_);
v___x_1013_ = lean_array_to_list(v___x_1012_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1013_);
v___x_1015_ = v___x_1008_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1005_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1005_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
else
{
lean_object* v___x_1026_; 
lean_dec(v_a_985_);
v___x_1026_ = l_Lean_Meta_Split_splitMatch(v_mvarId_976_, v_e_977_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___boxed(lean_object* v_mvarId_1027_, lean_object* v_e_1028_, lean_object* v_matcherInfo_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v_mvarId_1027_, v_e_1028_, v_matcherInfo_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec_ref(v_matcherInfo_1029_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(lean_object* v_msg_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___f_1042_; lean_object* v___x_12211__overap_1043_; lean_object* v___x_1044_; 
v___f_1042_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_12211__overap_1043_ = lean_panic_fn_borrowed(v___f_1042_, v_msg_1036_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
v___x_1044_ = lean_apply_5(v___x_12211__overap_1043_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, lean_box(0));
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1___boxed(lean_object* v_msg_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v_msg_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(lean_object* v_type_1052_, lean_object* v_k_1053_, uint8_t v_cleanupAnnotations_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___f_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___f_1060_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1060_, 0, v_k_1053_);
v___x_1061_ = 0;
v___x_1062_ = lean_box(0);
v___x_1063_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1061_, v___x_1062_, v_type_1052_, v___f_1060_, v_cleanupAnnotations_1054_, v___x_1061_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_a_1072_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1063_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1063_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg___boxed(lean_object* v_type_1080_, lean_object* v_k_1081_, lean_object* v_cleanupAnnotations_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1088_; lean_object* v_res_1089_; 
v_cleanupAnnotations_boxed_1088_ = lean_unbox(v_cleanupAnnotations_1082_);
v_res_1089_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1080_, v_k_1081_, v_cleanupAnnotations_boxed_1088_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(lean_object* v_00_u03b1_1090_, lean_object* v_type_1091_, lean_object* v_k_1092_, uint8_t v_cleanupAnnotations_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1091_, v_k_1092_, v_cleanupAnnotations_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___boxed(lean_object* v_00_u03b1_1100_, lean_object* v_type_1101_, lean_object* v_k_1102_, lean_object* v_cleanupAnnotations_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1109_; lean_object* v_res_1110_; 
v_cleanupAnnotations_boxed_1109_ = lean_unbox(v_cleanupAnnotations_1103_);
v_res_1110_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(v_00_u03b1_1100_, v_type_1101_, v_k_1102_, v_cleanupAnnotations_boxed_1109_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(lean_object* v_e_1111_, lean_object* v___y_1112_){
_start:
{
uint8_t v___x_1114_; 
v___x_1114_ = l_Lean_Expr_hasMVar(v_e_1111_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v_e_1111_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; lean_object* v_mctx_1117_; lean_object* v___x_1118_; lean_object* v_fst_1119_; lean_object* v_snd_1120_; lean_object* v___x_1121_; lean_object* v_cache_1122_; lean_object* v_zetaDeltaFVarIds_1123_; lean_object* v_postponed_1124_; lean_object* v_diag_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1134_; 
v___x_1116_ = lean_st_ref_get(v___y_1112_);
v_mctx_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc_ref(v_mctx_1117_);
lean_dec(v___x_1116_);
v___x_1118_ = l_Lean_instantiateMVarsCore(v_mctx_1117_, v_e_1111_);
v_fst_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_fst_1119_);
v_snd_1120_ = lean_ctor_get(v___x_1118_, 1);
lean_inc(v_snd_1120_);
lean_dec_ref(v___x_1118_);
v___x_1121_ = lean_st_ref_take(v___y_1112_);
v_cache_1122_ = lean_ctor_get(v___x_1121_, 1);
v_zetaDeltaFVarIds_1123_ = lean_ctor_get(v___x_1121_, 2);
v_postponed_1124_ = lean_ctor_get(v___x_1121_, 3);
v_diag_1125_ = lean_ctor_get(v___x_1121_, 4);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v___x_1121_, 0);
lean_dec(v_unused_1135_);
v___x_1127_ = v___x_1121_;
v_isShared_1128_ = v_isSharedCheck_1134_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_diag_1125_);
lean_inc(v_postponed_1124_);
lean_inc(v_zetaDeltaFVarIds_1123_);
lean_inc(v_cache_1122_);
lean_dec(v___x_1121_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1134_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v_snd_1120_);
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_snd_1120_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_cache_1122_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_zetaDeltaFVarIds_1123_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_postponed_1124_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_diag_1125_);
v___x_1130_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_st_ref_put(v___y_1112_, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_fst_1119_);
return v___x_1132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg___boxed(lean_object* v_e_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1136_, v___y_1137_);
lean_dec(v___y_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(lean_object* v_e_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1140_, v___y_1142_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___boxed(lean_object* v_e_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(v_e_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(lean_object* v_x_1154_, lean_object* v_motiveBody_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_Meta_getLevel(v_motiveBody_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0___boxed(lean_object* v_x_1162_, lean_object* v_motiveBody_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(v_x_1162_, v_motiveBody_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec_ref(v_x_1162_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(lean_object* v___x_1170_, lean_object* v___x_1171_, lean_object* v_alpha_1172_, uint8_t v___x_1173_, lean_object* v_xs_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; uint8_t v___x_1185_; uint8_t v___x_1186_; lean_object* v___x_1187_; 
v___x_1181_ = l_Lean_Level_ofNat(v___x_1170_);
v___x_1182_ = l_Lean_Expr_sort___override(v___x_1181_);
v___x_1183_ = l_Lean_Expr_forallE___override(v___x_1171_, v_alpha_1172_, v___x_1182_, v___x_1173_);
v___x_1184_ = 0;
v___x_1185_ = 1;
v___x_1186_ = 1;
v___x_1187_ = l_Lean_Meta_mkForallFVars(v_xs_1174_, v___x_1183_, v___x_1184_, v___x_1185_, v___x_1185_, v___x_1186_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed(lean_object* v___x_1188_, lean_object* v___x_1189_, lean_object* v_alpha_1190_, lean_object* v___x_1191_, lean_object* v_xs_1192_, lean_object* v_x_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v___x_16373__boxed_1199_; lean_object* v_res_1200_; 
v___x_16373__boxed_1199_ = lean_unbox(v___x_1191_);
v_res_1200_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(v___x_1188_, v___x_1189_, v_alpha_1190_, v___x_16373__boxed_1199_, v_xs_1192_, v_x_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec_ref(v_x_1193_);
lean_dec_ref(v_xs_1192_);
lean_dec(v___x_1188_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(lean_object* v___x_1207_, lean_object* v___x_1208_, lean_object* v_rel_1209_, lean_object* v___x_1210_, lean_object* v_beta_1211_, uint8_t v___x_1212_, lean_object* v_alpha_1213_, uint8_t v___x_1214_, lean_object* v_xs_1215_, lean_object* v_x_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1222_ = l_Lean_mkAppN(v___x_1207_, v_xs_1215_);
v___x_1223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_xs_1215_);
v___x_1225_ = lean_array_push(v_xs_1215_, v___x_1208_);
v___x_1226_ = l_Lean_mkAppN(v_rel_1209_, v___x_1225_);
lean_dec_ref(v___x_1225_);
v___x_1227_ = l_Lean_Expr_bvar___override(v___x_1210_);
v___x_1228_ = l_Lean_Expr_app___override(v_beta_1211_, v___x_1227_);
v___x_1229_ = l_Lean_Expr_forallE___override(v___x_1224_, v___x_1226_, v___x_1228_, v___x_1212_);
v___x_1230_ = l_Lean_Expr_forallE___override(v___x_1223_, v_alpha_1213_, v___x_1229_, v___x_1212_);
v___x_1231_ = l_Lean_mkArrow(v___x_1230_, v___x_1222_, v___y_1219_, v___y_1220_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; uint8_t v___x_1233_; uint8_t v___x_1234_; lean_object* v___x_1235_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref_known(v___x_1231_, 1);
v___x_1233_ = 1;
v___x_1234_ = 1;
v___x_1235_ = l_Lean_Meta_mkLambdaFVars(v_xs_1215_, v_a_1232_, v___x_1214_, v___x_1233_, v___x_1214_, v___x_1233_, v___x_1234_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec_ref(v_xs_1215_);
return v___x_1235_;
}
else
{
lean_dec_ref(v_xs_1215_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed(lean_object* v___x_1236_, lean_object* v___x_1237_, lean_object* v_rel_1238_, lean_object* v___x_1239_, lean_object* v_beta_1240_, lean_object* v___x_1241_, lean_object* v_alpha_1242_, lean_object* v___x_1243_, lean_object* v_xs_1244_, lean_object* v_x_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
uint8_t v___x_16427__boxed_1251_; uint8_t v___x_16428__boxed_1252_; lean_object* v_res_1253_; 
v___x_16427__boxed_1251_ = lean_unbox(v___x_1241_);
v___x_16428__boxed_1252_ = lean_unbox(v___x_1243_);
v_res_1253_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(v___x_1236_, v___x_1237_, v_rel_1238_, v___x_1239_, v_beta_1240_, v___x_16427__boxed_1251_, v_alpha_1242_, v___x_16428__boxed_1252_, v_xs_1244_, v_x_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v_x_1245_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(lean_object* v___x_1254_, lean_object* v___x_1255_, lean_object* v_f_1256_, uint8_t v___x_1257_, uint8_t v___x_1258_, lean_object* v_ys_1259_, lean_object* v_x_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1266_ = lean_array_get_borrowed(v___x_1254_, v_ys_1259_, v___x_1255_);
lean_inc(v___x_1266_);
v___x_1267_ = l_Lean_Expr_app___override(v_f_1256_, v___x_1266_);
v___x_1268_ = 1;
v___x_1269_ = l_Lean_Meta_mkLambdaFVars(v_ys_1259_, v___x_1267_, v___x_1257_, v___x_1258_, v___x_1257_, v___x_1258_, v___x_1268_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed(lean_object* v___x_1270_, lean_object* v___x_1271_, lean_object* v_f_1272_, lean_object* v___x_1273_, lean_object* v___x_1274_, lean_object* v_ys_1275_, lean_object* v_x_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
uint8_t v___x_16494__boxed_1282_; uint8_t v___x_16495__boxed_1283_; lean_object* v_res_1284_; 
v___x_16494__boxed_1282_ = lean_unbox(v___x_1273_);
v___x_16495__boxed_1283_ = lean_unbox(v___x_1274_);
v_res_1284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(v___x_1270_, v___x_1271_, v_f_1272_, v___x_16494__boxed_1282_, v___x_16495__boxed_1283_, v_ys_1275_, v_x_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec_ref(v_x_1276_);
lean_dec_ref(v_ys_1275_);
lean_dec(v___x_1271_);
lean_dec_ref(v___x_1270_);
return v_res_1284_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1));
v___x_1288_ = lean_unsigned_to_nat(10u);
v___x_1289_ = lean_unsigned_to_nat(146u);
v___x_1290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0));
v___x_1291_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_1292_ = l_mkPanicMessageWithDecl(v___x_1291_, v___x_1290_, v___x_1289_, v___x_1288_, v___x_1287_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(lean_object* v___x_1293_, lean_object* v___x_1294_, lean_object* v_f_1295_, uint8_t v___x_1296_, lean_object* v_a_1297_, lean_object* v_ys_1298_, lean_object* v_altBodyType_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v___x_1305_; 
v___x_1305_ = l_Lean_Expr_isForall(v_altBodyType_1299_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec_ref(v_ys_1298_);
lean_dec_ref(v_a_1297_);
lean_dec_ref(v_f_1295_);
lean_dec(v___x_1294_);
lean_dec_ref(v___x_1293_);
v___x_1306_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2);
v___x_1307_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v___x_1306_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___f_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1308_ = lean_box(v___x_1296_);
v___x_1309_ = lean_box(v___x_1305_);
v___f_1310_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1310_, 0, v___x_1293_);
lean_closure_set(v___f_1310_, 1, v___x_1294_);
lean_closure_set(v___f_1310_, 2, v_f_1295_);
lean_closure_set(v___f_1310_, 3, v___x_1308_);
lean_closure_set(v___f_1310_, 4, v___x_1309_);
v___x_1311_ = l_Lean_Expr_bindingDomain_x21(v_altBodyType_1299_);
v___x_1312_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_1313_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_1311_, v___x_1312_, v___f_1310_, v___x_1296_, v___x_1296_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; lean_object* v___x_1318_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1313_, 1);
lean_inc_ref(v_ys_1298_);
v___x_1315_ = lean_array_push(v_ys_1298_, v_a_1314_);
v___x_1316_ = l_Lean_mkAppN(v_a_1297_, v___x_1315_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = 1;
v___x_1318_ = l_Lean_Meta_mkLambdaFVars(v_ys_1298_, v___x_1316_, v___x_1296_, v___x_1305_, v___x_1296_, v___x_1305_, v___x_1317_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec_ref(v_ys_1298_);
return v___x_1318_;
}
else
{
lean_dec_ref(v_ys_1298_);
lean_dec_ref(v_a_1297_);
return v___x_1313_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed(lean_object* v___x_1319_, lean_object* v___x_1320_, lean_object* v_f_1321_, lean_object* v___x_1322_, lean_object* v_a_1323_, lean_object* v_ys_1324_, lean_object* v_altBodyType_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v___x_16551__boxed_1331_; lean_object* v_res_1332_; 
v___x_16551__boxed_1331_ = lean_unbox(v___x_1322_);
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(v___x_1319_, v___x_1320_, v_f_1321_, v___x_16551__boxed_1331_, v_a_1323_, v_ys_1324_, v_altBodyType_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec_ref(v_altBodyType_1325_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(lean_object* v_f_1333_, lean_object* v_as_1334_, size_t v_sz_1335_, size_t v_i_1336_, lean_object* v_b_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_lt(v_i_1336_, v_sz_1335_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_dec_ref(v_f_1333_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_b_1337_);
return v___x_1344_;
}
else
{
lean_object* v_snd_1345_; lean_object* v_fst_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1405_; 
v_snd_1345_ = lean_ctor_get(v_b_1337_, 1);
v_fst_1346_ = lean_ctor_get(v_b_1337_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_b_1337_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1348_ = v_b_1337_;
v_isShared_1349_ = v_isSharedCheck_1405_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snd_1345_);
lean_inc(v_fst_1346_);
lean_dec(v_b_1337_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1405_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_array_1350_; lean_object* v_start_1351_; lean_object* v_stop_1352_; uint8_t v___x_1353_; 
v_array_1350_ = lean_ctor_get(v_snd_1345_, 0);
v_start_1351_ = lean_ctor_get(v_snd_1345_, 1);
v_stop_1352_ = lean_ctor_get(v_snd_1345_, 2);
v___x_1353_ = lean_nat_dec_lt(v_start_1351_, v_stop_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1355_; 
lean_dec_ref(v_f_1333_);
if (v_isShared_1349_ == 0)
{
v___x_1355_ = v___x_1348_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_fst_1346_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_snd_1345_);
v___x_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
else
{
lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1401_; 
lean_inc(v_stop_1352_);
lean_inc(v_start_1351_);
lean_inc_ref(v_array_1350_);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_snd_1345_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; lean_object* v_unused_1403_; lean_object* v_unused_1404_; 
v_unused_1402_ = lean_ctor_get(v_snd_1345_, 2);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_snd_1345_, 1);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_snd_1345_, 0);
lean_dec(v_unused_1404_);
v___x_1359_ = v_snd_1345_;
v_isShared_1360_ = v_isSharedCheck_1401_;
goto v_resetjp_1358_;
}
else
{
lean_dec(v_snd_1345_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1401_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v_a_1361_; lean_object* v___x_1362_; 
v_a_1361_ = lean_array_uget_borrowed(v_as_1334_, v_i_1336_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v_a_1361_);
v___x_1362_ = lean_infer_type(v_a_1361_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = l_Lean_instInhabitedExpr;
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = 0;
v___x_1367_ = lean_box(v___x_1366_);
lean_inc(v_a_1361_);
lean_inc_ref(v_f_1333_);
v___f_1368_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed), 12, 5);
lean_closure_set(v___f_1368_, 0, v___x_1364_);
lean_closure_set(v___f_1368_, 1, v___x_1365_);
lean_closure_set(v___f_1368_, 2, v_f_1333_);
lean_closure_set(v___f_1368_, 3, v___x_1367_);
lean_closure_set(v___f_1368_, 4, v_a_1361_);
v___x_1369_ = lean_array_fget_borrowed(v_array_1350_, v_start_1351_);
lean_inc(v___x_1369_);
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
v___x_1371_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1363_, v___x_1370_, v___f_1368_, v___x_1366_, v___x_1366_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_nat_add(v_start_1351_, v___x_1373_);
lean_dec(v_start_1351_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v___x_1374_);
v___x_1376_ = v___x_1359_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_array_1350_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_stop_1352_);
v___x_1376_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = l_Lean_Expr_app___override(v_fst_1346_, v_a_1372_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v___x_1376_);
lean_ctor_set(v___x_1348_, 0, v___x_1377_);
v___x_1379_ = v___x_1348_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1376_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
size_t v___x_1380_; size_t v___x_1381_; 
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1336_, v___x_1380_);
v_i_1336_ = v___x_1381_;
v_b_1337_ = v___x_1379_;
goto _start;
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_del_object(v___x_1359_);
lean_dec(v_stop_1352_);
lean_dec(v_start_1351_);
lean_dec_ref(v_array_1350_);
lean_del_object(v___x_1348_);
lean_dec(v_fst_1346_);
lean_dec_ref(v_f_1333_);
v_a_1385_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1371_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1371_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_del_object(v___x_1359_);
lean_dec(v_stop_1352_);
lean_dec(v_start_1351_);
lean_dec_ref(v_array_1350_);
lean_del_object(v___x_1348_);
lean_dec(v_fst_1346_);
lean_dec_ref(v_f_1333_);
v_a_1393_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1362_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1362_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___boxed(lean_object* v_f_1406_, lean_object* v_as_1407_, lean_object* v_sz_1408_, lean_object* v_i_1409_, lean_object* v_b_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
size_t v_sz_boxed_1416_; size_t v_i_boxed_1417_; lean_object* v_res_1418_; 
v_sz_boxed_1416_ = lean_unbox_usize(v_sz_1408_);
lean_dec(v_sz_1408_);
v_i_boxed_1417_ = lean_unbox_usize(v_i_1409_);
lean_dec(v_i_1409_);
v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1406_, v_as_1407_, v_sz_boxed_1416_, v_i_boxed_1417_, v_b_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec_ref(v_as_1407_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(lean_object* v_as_x27_1419_, lean_object* v_b_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
if (lean_obj_tag(v_as_x27_1419_) == 0)
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_b_1420_);
return v___x_1426_;
}
else
{
lean_object* v_head_1427_; lean_object* v_tail_1428_; uint8_t v___x_1429_; lean_object* v___x_1430_; 
v_head_1427_ = lean_ctor_get(v_as_x27_1419_, 0);
v_tail_1428_ = lean_ctor_get(v_as_x27_1419_, 1);
v___x_1429_ = 1;
lean_inc(v_head_1427_);
v___x_1430_ = l_Lean_MVarId_refl(v_head_1427_, v___x_1429_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v___x_1431_; 
lean_dec_ref_known(v___x_1430_, 1);
v___x_1431_ = lean_box(0);
v_as_x27_1419_ = v_tail_1428_;
v_b_1420_ = v___x_1431_;
goto _start;
}
else
{
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg___boxed(lean_object* v_as_x27_1433_, lean_object* v_b_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_1433_, v_b_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v_as_x27_1433_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(lean_object* v___x_1441_, lean_object* v_matcherInfo_1442_, lean_object* v___x_1443_, lean_object* v___x_1444_, lean_object* v_f_1445_, lean_object* v_discrs_1446_, lean_object* v___x_1447_, lean_object* v_rel_1448_, lean_object* v___x_1449_, uint8_t v___x_1450_, lean_object* v_alpha_1451_, lean_object* v___x_1452_, lean_object* v_beta_1453_, lean_object* v___x_1454_, uint8_t v___x_1455_, lean_object* v___x_1456_, lean_object* v___x_1457_, lean_object* v___x_1458_, lean_object* v_alts_1459_, lean_object* v_x_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; size_t v_sz_1471_; size_t v___x_1472_; lean_object* v___x_1473_; 
v___x_1466_ = l_Lean_mkAppN(v___x_1441_, v_alts_1459_);
lean_inc_ref(v_matcherInfo_1442_);
v___x_1467_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_matcherInfo_1442_);
v___x_1468_ = lean_array_get_size(v___x_1467_);
v___x_1469_ = l_Array_toSubarray___redArg(v___x_1467_, v___x_1443_, v___x_1468_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1444_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v_sz_1471_ = lean_array_size(v_alts_1459_);
v___x_1472_ = ((size_t)0ULL);
lean_inc_ref(v_f_1445_);
v___x_1473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1445_, v_alts_1459_, v_sz_1471_, v___x_1472_, v___x_1470_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v_fst_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1569_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v_fst_1475_ = lean_ctor_get(v_a_1474_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_a_1474_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v_a_1474_, 1);
lean_dec(v_unused_1570_);
v___x_1477_ = v_a_1474_;
v_isShared_1478_ = v_isSharedCheck_1569_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_fst_1475_);
lean_dec(v_a_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1569_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1479_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1480_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_discrs_1446_);
v___x_1481_ = lean_array_push(v_discrs_1446_, v___x_1447_);
lean_inc_ref(v_rel_1448_);
v___x_1482_ = l_Lean_mkAppN(v_rel_1448_, v___x_1481_);
lean_dec_ref(v___x_1481_);
v___x_1483_ = l_Lean_Expr_bvar___override(v___x_1449_);
lean_inc_ref(v_f_1445_);
v___x_1484_ = l_Lean_Expr_app___override(v_f_1445_, v___x_1483_);
v___x_1485_ = l_Lean_Expr_lam___override(v___x_1480_, v___x_1482_, v___x_1484_, v___x_1450_);
lean_inc_ref(v_alpha_1451_);
v___x_1486_ = l_Lean_Expr_lam___override(v___x_1479_, v_alpha_1451_, v___x_1485_, v___x_1450_);
v___x_1487_ = l_Lean_Expr_app___override(v___x_1466_, v___x_1486_);
lean_inc(v_fst_1475_);
v___x_1488_ = l_Lean_Meta_mkEq(v___x_1487_, v_fst_1475_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc_n(v_a_1489_, 2);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1490_ = lean_box(0);
v___x_1491_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1489_, v___x_1490_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1493_ = l_Lean_Expr_mvarId_x21(v_a_1492_);
v___x_1494_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v___x_1493_, v_fst_1475_, v_matcherInfo_1442_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec_ref(v_matcherInfo_1442_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
v___x_1496_ = lean_box(0);
v___x_1497_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_a_1495_, v___x_1496_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v_a_1495_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1544_; 
lean_dec_ref_known(v___x_1497_, 1);
v___x_1498_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_1492_, v___y_1462_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1544_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1544_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1503_ = lean_unsigned_to_nat(5u);
v___x_1504_ = lean_mk_empty_array_with_capacity(v___x_1503_);
v___x_1505_ = lean_array_push(v___x_1504_, v___x_1452_);
v___x_1506_ = lean_array_push(v___x_1505_, v_alpha_1451_);
v___x_1507_ = lean_array_push(v___x_1506_, v_beta_1453_);
v___x_1508_ = lean_array_push(v___x_1507_, v_f_1445_);
v___x_1509_ = lean_array_push(v___x_1508_, v_rel_1448_);
v___x_1510_ = l_Array_append___redArg(v___x_1454_, v___x_1509_);
lean_dec_ref(v___x_1509_);
v___x_1511_ = l_Array_append___redArg(v___x_1510_, v_discrs_1446_);
lean_dec_ref(v_discrs_1446_);
v___x_1512_ = l_Array_append___redArg(v___x_1511_, v_alts_1459_);
v___x_1513_ = 1;
v___x_1514_ = 1;
v___x_1515_ = l_Lean_Meta_mkForallFVars(v___x_1512_, v_a_1489_, v___x_1455_, v___x_1513_, v___x_1513_, v___x_1514_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1517_ = l_Lean_Meta_mkLambdaFVars(v___x_1512_, v_a_1499_, v___x_1455_, v___x_1513_, v___x_1455_, v___x_1513_, v___x_1514_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec_ref(v___x_1512_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
lean_inc(v___x_1456_);
v___x_1519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1456_);
lean_ctor_set(v___x_1519_, 1, v___x_1457_);
lean_ctor_set(v___x_1519_, 2, v_a_1516_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 1);
lean_ctor_set(v___x_1477_, 1, v___x_1458_);
lean_ctor_set(v___x_1477_, 0, v___x_1456_);
v___x_1521_ = v___x_1477_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1458_);
v___x_1521_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1519_);
lean_ctor_set(v___x_1522_, 1, v_a_1518_);
lean_ctor_set(v___x_1522_, 2, v___x_1521_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set_tag(v___x_1501_, 2);
lean_ctor_set(v___x_1501_, 0, v___x_1522_);
v___x_1524_ = v___x_1501_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_addDecl(v___x_1524_, v___x_1455_, v___y_1463_, v___y_1464_);
return v___x_1525_;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_a_1516_);
lean_del_object(v___x_1501_);
lean_del_object(v___x_1477_);
lean_dec(v___x_1458_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
v_a_1528_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1517_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1517_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref(v___x_1512_);
lean_del_object(v___x_1501_);
lean_dec(v_a_1499_);
lean_del_object(v___x_1477_);
lean_dec(v___x_1458_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
v_a_1536_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1515_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1515_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
else
{
lean_dec(v_a_1492_);
lean_dec(v_a_1489_);
lean_del_object(v___x_1477_);
lean_dec(v___x_1458_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_beta_1453_);
lean_dec_ref(v___x_1452_);
lean_dec_ref(v_alpha_1451_);
lean_dec_ref(v_rel_1448_);
lean_dec_ref(v_discrs_1446_);
lean_dec_ref(v_f_1445_);
return v___x_1497_;
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_a_1492_);
lean_dec(v_a_1489_);
lean_del_object(v___x_1477_);
lean_dec(v___x_1458_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_beta_1453_);
lean_dec_ref(v___x_1452_);
lean_dec_ref(v_alpha_1451_);
lean_dec_ref(v_rel_1448_);
lean_dec_ref(v_discrs_1446_);
lean_dec_ref(v_f_1445_);
v_a_1545_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1494_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1494_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1489_);
lean_del_object(v___x_1477_);
lean_dec(v_fst_1475_);
lean_dec(v___x_1458_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_beta_1453_);
lean_dec_ref(v___x_1452_);
lean_dec_ref(v_alpha_1451_);
lean_dec_ref(v_rel_1448_);
lean_dec_ref(v_discrs_1446_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_matcherInfo_1442_);
v_a_1553_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1491_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1491_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_del_object(v___x_1477_);
lean_dec(v_fst_1475_);
lean_dec(v___x_1458_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_beta_1453_);
lean_dec_ref(v___x_1452_);
lean_dec_ref(v_alpha_1451_);
lean_dec_ref(v_rel_1448_);
lean_dec_ref(v_discrs_1446_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_matcherInfo_1442_);
v_a_1561_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1488_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1488_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref(v___x_1466_);
lean_dec(v___x_1458_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_beta_1453_);
lean_dec_ref(v___x_1452_);
lean_dec_ref(v_alpha_1451_);
lean_dec(v___x_1449_);
lean_dec_ref(v_rel_1448_);
lean_dec_ref(v___x_1447_);
lean_dec_ref(v_discrs_1446_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_matcherInfo_1442_);
v_a_1571_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1473_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1473_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed(lean_object** _args){
lean_object* v___x_1579_ = _args[0];
lean_object* v_matcherInfo_1580_ = _args[1];
lean_object* v___x_1581_ = _args[2];
lean_object* v___x_1582_ = _args[3];
lean_object* v_f_1583_ = _args[4];
lean_object* v_discrs_1584_ = _args[5];
lean_object* v___x_1585_ = _args[6];
lean_object* v_rel_1586_ = _args[7];
lean_object* v___x_1587_ = _args[8];
lean_object* v___x_1588_ = _args[9];
lean_object* v_alpha_1589_ = _args[10];
lean_object* v___x_1590_ = _args[11];
lean_object* v_beta_1591_ = _args[12];
lean_object* v___x_1592_ = _args[13];
lean_object* v___x_1593_ = _args[14];
lean_object* v___x_1594_ = _args[15];
lean_object* v___x_1595_ = _args[16];
lean_object* v___x_1596_ = _args[17];
lean_object* v_alts_1597_ = _args[18];
lean_object* v_x_1598_ = _args[19];
lean_object* v___y_1599_ = _args[20];
lean_object* v___y_1600_ = _args[21];
lean_object* v___y_1601_ = _args[22];
lean_object* v___y_1602_ = _args[23];
lean_object* v___y_1603_ = _args[24];
_start:
{
uint8_t v___x_16781__boxed_1604_; uint8_t v___x_16784__boxed_1605_; lean_object* v_res_1606_; 
v___x_16781__boxed_1604_ = lean_unbox(v___x_1588_);
v___x_16784__boxed_1605_ = lean_unbox(v___x_1593_);
v_res_1606_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(v___x_1579_, v_matcherInfo_1580_, v___x_1581_, v___x_1582_, v_f_1583_, v_discrs_1584_, v___x_1585_, v_rel_1586_, v___x_1587_, v___x_16781__boxed_1604_, v_alpha_1589_, v___x_1590_, v_beta_1591_, v___x_1592_, v___x_16784__boxed_1605_, v___x_1594_, v___x_1595_, v___x_1596_, v_alts_1597_, v_x_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_x_1598_);
lean_dec_ref(v_alts_1597_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(lean_object* v___x_1607_, lean_object* v___x_1608_, lean_object* v_matcherInfo_1609_, lean_object* v___x_1610_, lean_object* v_f_1611_, lean_object* v___x_1612_, lean_object* v_rel_1613_, lean_object* v___x_1614_, uint8_t v___x_1615_, lean_object* v_alpha_1616_, lean_object* v___x_1617_, lean_object* v_beta_1618_, lean_object* v___x_1619_, uint8_t v___x_1620_, lean_object* v___x_1621_, lean_object* v___x_1622_, lean_object* v___x_1623_, lean_object* v_discrs_1624_, lean_object* v_x_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = l_Lean_mkAppN(v___x_1607_, v_discrs_1624_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc(v___y_1627_);
lean_inc_ref(v___y_1626_);
lean_inc_ref(v___x_1631_);
v___x_1632_ = lean_infer_type(v___x_1631_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___f_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1634_ = l_Lean_mkAppN(v___x_1608_, v_discrs_1624_);
v___x_1635_ = lean_box(v___x_1615_);
v___x_1636_ = lean_box(v___x_1620_);
lean_inc_ref(v_matcherInfo_1609_);
v___f_1637_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1637_, 0, v___x_1631_);
lean_closure_set(v___f_1637_, 1, v_matcherInfo_1609_);
lean_closure_set(v___f_1637_, 2, v___x_1610_);
lean_closure_set(v___f_1637_, 3, v___x_1634_);
lean_closure_set(v___f_1637_, 4, v_f_1611_);
lean_closure_set(v___f_1637_, 5, v_discrs_1624_);
lean_closure_set(v___f_1637_, 6, v___x_1612_);
lean_closure_set(v___f_1637_, 7, v_rel_1613_);
lean_closure_set(v___f_1637_, 8, v___x_1614_);
lean_closure_set(v___f_1637_, 9, v___x_1635_);
lean_closure_set(v___f_1637_, 10, v_alpha_1616_);
lean_closure_set(v___f_1637_, 11, v___x_1617_);
lean_closure_set(v___f_1637_, 12, v_beta_1618_);
lean_closure_set(v___f_1637_, 13, v___x_1619_);
lean_closure_set(v___f_1637_, 14, v___x_1636_);
lean_closure_set(v___f_1637_, 15, v___x_1621_);
lean_closure_set(v___f_1637_, 16, v___x_1622_);
lean_closure_set(v___f_1637_, 17, v___x_1623_);
v___x_1638_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_matcherInfo_1609_);
lean_dec_ref(v_matcherInfo_1609_);
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
v___x_1640_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1633_, v___x_1639_, v___f_1637_, v___x_1620_, v___x_1620_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1640_;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v___x_1631_);
lean_dec_ref(v_discrs_1624_);
lean_dec(v___x_1623_);
lean_dec(v___x_1622_);
lean_dec(v___x_1621_);
lean_dec_ref(v___x_1619_);
lean_dec_ref(v_beta_1618_);
lean_dec_ref(v___x_1617_);
lean_dec_ref(v_alpha_1616_);
lean_dec(v___x_1614_);
lean_dec_ref(v_rel_1613_);
lean_dec_ref(v___x_1612_);
lean_dec_ref(v_f_1611_);
lean_dec(v___x_1610_);
lean_dec_ref(v_matcherInfo_1609_);
lean_dec_ref(v___x_1608_);
v_a_1641_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1632_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1632_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed(lean_object** _args){
lean_object* v___x_1649_ = _args[0];
lean_object* v___x_1650_ = _args[1];
lean_object* v_matcherInfo_1651_ = _args[2];
lean_object* v___x_1652_ = _args[3];
lean_object* v_f_1653_ = _args[4];
lean_object* v___x_1654_ = _args[5];
lean_object* v_rel_1655_ = _args[6];
lean_object* v___x_1656_ = _args[7];
lean_object* v___x_1657_ = _args[8];
lean_object* v_alpha_1658_ = _args[9];
lean_object* v___x_1659_ = _args[10];
lean_object* v_beta_1660_ = _args[11];
lean_object* v___x_1661_ = _args[12];
lean_object* v___x_1662_ = _args[13];
lean_object* v___x_1663_ = _args[14];
lean_object* v___x_1664_ = _args[15];
lean_object* v___x_1665_ = _args[16];
lean_object* v_discrs_1666_ = _args[17];
lean_object* v_x_1667_ = _args[18];
lean_object* v___y_1668_ = _args[19];
lean_object* v___y_1669_ = _args[20];
lean_object* v___y_1670_ = _args[21];
lean_object* v___y_1671_ = _args[22];
lean_object* v___y_1672_ = _args[23];
_start:
{
uint8_t v___x_17062__boxed_1673_; uint8_t v___x_17065__boxed_1674_; lean_object* v_res_1675_; 
v___x_17062__boxed_1673_ = lean_unbox(v___x_1657_);
v___x_17065__boxed_1674_ = lean_unbox(v___x_1662_);
v_res_1675_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(v___x_1649_, v___x_1650_, v_matcherInfo_1651_, v___x_1652_, v_f_1653_, v___x_1654_, v_rel_1655_, v___x_1656_, v___x_17062__boxed_1673_, v_alpha_1658_, v___x_1659_, v_beta_1660_, v___x_1661_, v___x_17065__boxed_1674_, v___x_1663_, v___x_1664_, v___x_1665_, v_discrs_1666_, v_x_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec_ref(v_x_1667_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
if (lean_obj_tag(v_a_1676_) == 0)
{
lean_object* v___x_1678_; 
v___x_1678_ = l_List_reverse___redArg(v_a_1677_);
return v___x_1678_;
}
else
{
lean_object* v_head_1679_; lean_object* v_tail_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1689_; 
v_head_1679_ = lean_ctor_get(v_a_1676_, 0);
v_tail_1680_ = lean_ctor_get(v_a_1676_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_a_1676_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1682_ = v_a_1676_;
v_isShared_1683_ = v_isSharedCheck_1689_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_tail_1680_);
lean_inc(v_head_1679_);
lean_dec(v_a_1676_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1689_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = l_Lean_mkLevelParam(v_head_1679_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 1, v_a_1677_);
lean_ctor_set(v___x_1682_, 0, v___x_1684_);
v___x_1686_ = v___x_1682_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_a_1677_);
v___x_1686_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
v_a_1676_ = v_tail_1680_;
v_a_1677_ = v___x_1686_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__0));
v___x_1692_ = l_Lean_stringToMessageData(v___x_1691_);
return v___x_1692_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__2));
v___x_1695_ = l_Lean_stringToMessageData(v___x_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(lean_object* v___x_1696_, lean_object* v___x_1697_, lean_object* v___x_1698_, lean_object* v_beta_1699_, uint8_t v___x_1700_, lean_object* v_alpha_1701_, uint8_t v___x_1702_, lean_object* v_numDiscrs_1703_, lean_object* v___f_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_levelParams_1707_, lean_object* v_matcherName_1708_, lean_object* v___x_1709_, lean_object* v_matcherInfo_1710_, lean_object* v___x_1711_, lean_object* v_f_1712_, lean_object* v___x_1713_, lean_object* v_uElimPos_x3f_1714_, lean_object* v_rel_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1718_);
lean_inc(v___y_1717_);
lean_inc_ref(v___y_1716_);
lean_inc_ref(v___x_1696_);
v___x_1721_ = lean_infer_type(v___x_1696_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___f_1725_; lean_object* v___x_1726_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = lean_box(v___x_1700_);
v___x_1724_ = lean_box(v___x_1702_);
lean_inc_ref(v_alpha_1701_);
lean_inc_ref(v_beta_1699_);
lean_inc(v___x_1698_);
lean_inc_ref(v_rel_1715_);
lean_inc_ref(v___x_1697_);
lean_inc_ref(v___x_1696_);
v___f_1725_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed), 15, 8);
lean_closure_set(v___f_1725_, 0, v___x_1696_);
lean_closure_set(v___f_1725_, 1, v___x_1697_);
lean_closure_set(v___f_1725_, 2, v_rel_1715_);
lean_closure_set(v___f_1725_, 3, v___x_1698_);
lean_closure_set(v___f_1725_, 4, v_beta_1699_);
lean_closure_set(v___f_1725_, 5, v___x_1723_);
lean_closure_set(v___f_1725_, 6, v_alpha_1701_);
lean_closure_set(v___f_1725_, 7, v___x_1724_);
v___x_1726_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1722_, v___f_1725_, v___x_1702_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc_n(v_a_1727_, 2);
lean_dec_ref_known(v___x_1726_, 1);
lean_inc(v_numDiscrs_1703_);
v___x_1728_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_a_1727_, v_numDiscrs_1703_, v___f_1704_, v___x_1702_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v_matcherLevels_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_a_1705_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1732_, 0, v_a_1706_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
lean_inc(v_levelParams_1707_);
v___x_1733_ = l_List_appendTR___redArg(v_levelParams_1707_, v___x_1732_);
v___x_1734_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_1707_, v___x_1730_);
if (lean_obj_tag(v_uElimPos_x3f_1714_) == 0)
{
uint8_t v___x_1763_; 
v___x_1763_ = l_Lean_Level_isZero(v_a_1729_);
lean_dec(v_a_1729_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec(v___x_1734_);
lean_dec(v___x_1733_);
lean_dec(v_a_1727_);
lean_dec_ref(v_rel_1715_);
lean_dec(v___x_1713_);
lean_dec_ref(v_f_1712_);
lean_dec(v___x_1711_);
lean_dec_ref(v_matcherInfo_1710_);
lean_dec_ref(v___x_1709_);
lean_dec(v_numDiscrs_1703_);
lean_dec_ref(v_alpha_1701_);
lean_dec_ref(v_beta_1699_);
lean_dec(v___x_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1696_);
v___x_1764_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1);
v___x_1765_ = l_Lean_MessageData_ofConstName(v_matcherName_1708_, v___x_1702_);
v___x_1766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1764_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3);
v___x_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1766_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_1768_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
return v___x_1769_;
}
else
{
lean_inc(v___x_1734_);
v_matcherLevels_1736_ = v___x_1734_;
v___y_1737_ = v___y_1716_;
v___y_1738_ = v___y_1717_;
v___y_1739_ = v___y_1718_;
v___y_1740_ = v___y_1719_;
goto v___jp_1735_;
}
}
else
{
lean_object* v_val_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_val_1770_ = lean_ctor_get(v_uElimPos_x3f_1714_, 0);
lean_inc(v___x_1734_);
v___x_1771_ = lean_array_mk(v___x_1734_);
v___x_1772_ = lean_array_set(v___x_1771_, v_val_1770_, v_a_1729_);
v___x_1773_ = lean_array_to_list(v___x_1772_);
v_matcherLevels_1736_ = v___x_1773_;
v___y_1737_ = v___y_1716_;
v___y_1738_ = v___y_1717_;
v___y_1739_ = v___y_1718_;
v___y_1740_ = v___y_1719_;
goto v___jp_1735_;
}
v___jp_1735_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_inc(v_matcherName_1708_);
v___x_1741_ = l_Lean_Expr_const___override(v_matcherName_1708_, v_matcherLevels_1736_);
v___x_1742_ = l_Subarray_copy___redArg(v___x_1709_);
v___x_1743_ = l_Lean_mkAppN(v___x_1741_, v___x_1742_);
v___x_1744_ = l_Lean_Expr_app___override(v___x_1743_, v_a_1727_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc_ref(v___x_1744_);
v___x_1745_ = lean_infer_type(v___x_1744_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1747_ = l_Lean_Expr_const___override(v_matcherName_1708_, v___x_1734_);
v___x_1748_ = l_Lean_mkAppN(v___x_1747_, v___x_1742_);
lean_inc_ref(v___x_1696_);
v___x_1749_ = l_Lean_Expr_app___override(v___x_1748_, v___x_1696_);
v___x_1750_ = lean_box(v___x_1700_);
v___x_1751_ = lean_box(v___x_1702_);
v___f_1752_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed), 24, 17);
lean_closure_set(v___f_1752_, 0, v___x_1744_);
lean_closure_set(v___f_1752_, 1, v___x_1749_);
lean_closure_set(v___f_1752_, 2, v_matcherInfo_1710_);
lean_closure_set(v___f_1752_, 3, v___x_1711_);
lean_closure_set(v___f_1752_, 4, v_f_1712_);
lean_closure_set(v___f_1752_, 5, v___x_1697_);
lean_closure_set(v___f_1752_, 6, v_rel_1715_);
lean_closure_set(v___f_1752_, 7, v___x_1698_);
lean_closure_set(v___f_1752_, 8, v___x_1750_);
lean_closure_set(v___f_1752_, 9, v_alpha_1701_);
lean_closure_set(v___f_1752_, 10, v___x_1696_);
lean_closure_set(v___f_1752_, 11, v_beta_1699_);
lean_closure_set(v___f_1752_, 12, v___x_1742_);
lean_closure_set(v___f_1752_, 13, v___x_1751_);
lean_closure_set(v___f_1752_, 14, v___x_1713_);
lean_closure_set(v___f_1752_, 15, v___x_1733_);
lean_closure_set(v___f_1752_, 16, v___x_1730_);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_numDiscrs_1703_);
v___x_1754_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1746_, v___x_1753_, v___f_1752_, v___x_1702_, v___x_1702_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
return v___x_1754_;
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v___x_1744_);
lean_dec_ref(v___x_1742_);
lean_dec(v___x_1734_);
lean_dec(v___x_1733_);
lean_dec_ref(v_rel_1715_);
lean_dec(v___x_1713_);
lean_dec_ref(v_f_1712_);
lean_dec(v___x_1711_);
lean_dec_ref(v_matcherInfo_1710_);
lean_dec(v_matcherName_1708_);
lean_dec(v_numDiscrs_1703_);
lean_dec_ref(v_alpha_1701_);
lean_dec_ref(v_beta_1699_);
lean_dec(v___x_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1696_);
v_a_1755_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1745_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1745_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec(v_a_1727_);
lean_dec_ref(v_rel_1715_);
lean_dec(v___x_1713_);
lean_dec_ref(v_f_1712_);
lean_dec(v___x_1711_);
lean_dec_ref(v_matcherInfo_1710_);
lean_dec_ref(v___x_1709_);
lean_dec(v_matcherName_1708_);
lean_dec(v_levelParams_1707_);
lean_dec(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec(v_numDiscrs_1703_);
lean_dec_ref(v_alpha_1701_);
lean_dec_ref(v_beta_1699_);
lean_dec(v___x_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1696_);
v_a_1774_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1728_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1728_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v_rel_1715_);
lean_dec(v___x_1713_);
lean_dec_ref(v_f_1712_);
lean_dec(v___x_1711_);
lean_dec_ref(v_matcherInfo_1710_);
lean_dec_ref(v___x_1709_);
lean_dec(v_matcherName_1708_);
lean_dec(v_levelParams_1707_);
lean_dec(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v___f_1704_);
lean_dec(v_numDiscrs_1703_);
lean_dec_ref(v_alpha_1701_);
lean_dec_ref(v_beta_1699_);
lean_dec(v___x_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1696_);
v_a_1782_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1726_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1726_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v_rel_1715_);
lean_dec(v___x_1713_);
lean_dec_ref(v_f_1712_);
lean_dec(v___x_1711_);
lean_dec_ref(v_matcherInfo_1710_);
lean_dec_ref(v___x_1709_);
lean_dec(v_matcherName_1708_);
lean_dec(v_levelParams_1707_);
lean_dec(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v___f_1704_);
lean_dec(v_numDiscrs_1703_);
lean_dec_ref(v_alpha_1701_);
lean_dec_ref(v_beta_1699_);
lean_dec(v___x_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1696_);
v_a_1790_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1721_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1721_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed(lean_object** _args){
lean_object* v___x_1798_ = _args[0];
lean_object* v___x_1799_ = _args[1];
lean_object* v___x_1800_ = _args[2];
lean_object* v_beta_1801_ = _args[3];
lean_object* v___x_1802_ = _args[4];
lean_object* v_alpha_1803_ = _args[5];
lean_object* v___x_1804_ = _args[6];
lean_object* v_numDiscrs_1805_ = _args[7];
lean_object* v___f_1806_ = _args[8];
lean_object* v_a_1807_ = _args[9];
lean_object* v_a_1808_ = _args[10];
lean_object* v_levelParams_1809_ = _args[11];
lean_object* v_matcherName_1810_ = _args[12];
lean_object* v___x_1811_ = _args[13];
lean_object* v_matcherInfo_1812_ = _args[14];
lean_object* v___x_1813_ = _args[15];
lean_object* v_f_1814_ = _args[16];
lean_object* v___x_1815_ = _args[17];
lean_object* v_uElimPos_x3f_1816_ = _args[18];
lean_object* v_rel_1817_ = _args[19];
lean_object* v___y_1818_ = _args[20];
lean_object* v___y_1819_ = _args[21];
lean_object* v___y_1820_ = _args[22];
lean_object* v___y_1821_ = _args[23];
lean_object* v___y_1822_ = _args[24];
_start:
{
uint8_t v___x_17190__boxed_1823_; uint8_t v___x_17191__boxed_1824_; lean_object* v_res_1825_; 
v___x_17190__boxed_1823_ = lean_unbox(v___x_1802_);
v___x_17191__boxed_1824_ = lean_unbox(v___x_1804_);
v_res_1825_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(v___x_1798_, v___x_1799_, v___x_1800_, v_beta_1801_, v___x_17190__boxed_1823_, v_alpha_1803_, v___x_17191__boxed_1824_, v_numDiscrs_1805_, v___f_1806_, v_a_1807_, v_a_1808_, v_levelParams_1809_, v_matcherName_1810_, v___x_1811_, v_matcherInfo_1812_, v___x_1813_, v_f_1814_, v___x_1815_, v_uElimPos_x3f_1816_, v_rel_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v_uElimPos_x3f_1816_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(lean_object* v_k_1826_, lean_object* v_b_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___x_1833_; 
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
v___x_1833_ = lean_apply_6(v_k_1826_, v_b_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, lean_box(0));
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v_k_1834_, lean_object* v_b_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(v_k_1834_, v_b_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(lean_object* v_name_1842_, uint8_t v_bi_1843_, lean_object* v_type_1844_, lean_object* v_k_1845_, uint8_t v_kind_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___f_1852_; lean_object* v___x_1853_; 
v___f_1852_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1852_, 0, v_k_1845_);
v___x_1853_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1842_, v_bi_1843_, v_type_1844_, v___f_1852_, v_kind_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
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
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1862_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1853_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1853_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___boxed(lean_object* v_name_1870_, lean_object* v_bi_1871_, lean_object* v_type_1872_, lean_object* v_k_1873_, lean_object* v_kind_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v_bi_boxed_1880_; uint8_t v_kind_boxed_1881_; lean_object* v_res_1882_; 
v_bi_boxed_1880_ = lean_unbox(v_bi_1871_);
v_kind_boxed_1881_ = lean_unbox(v_kind_1874_);
v_res_1882_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1870_, v_bi_boxed_1880_, v_type_1872_, v_k_1873_, v_kind_boxed_1881_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(lean_object* v_name_1883_, lean_object* v_type_1884_, lean_object* v_k_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
uint8_t v___x_1891_; uint8_t v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = 0;
v___x_1892_ = 0;
v___x_1893_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1883_, v___x_1891_, v_type_1884_, v_k_1885_, v___x_1892_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg___boxed(lean_object* v_name_1894_, lean_object* v_type_1895_, lean_object* v_k_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_1894_, v_type_1895_, v_k_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(lean_object* v___x_1906_, lean_object* v___f_1907_, lean_object* v___x_1908_, lean_object* v___x_1909_, lean_object* v_beta_1910_, uint8_t v___x_1911_, lean_object* v_alpha_1912_, lean_object* v_numDiscrs_1913_, lean_object* v___f_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_levelParams_1917_, lean_object* v_matcherName_1918_, lean_object* v___x_1919_, lean_object* v_matcherInfo_1920_, lean_object* v___x_1921_, lean_object* v___x_1922_, lean_object* v_uElimPos_x3f_1923_, lean_object* v_f_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; 
lean_inc(v___y_1928_);
lean_inc_ref(v___y_1927_);
lean_inc(v___y_1926_);
lean_inc_ref(v___y_1925_);
lean_inc_ref(v___x_1906_);
v___x_1930_ = lean_infer_type(v___x_1906_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1932_ = 0;
v___x_1933_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1931_, v___f_1907_, v___x_1932_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1935_ = lean_box(v___x_1911_);
v___x_1936_ = lean_box(v___x_1932_);
v___f_1937_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed), 25, 19);
lean_closure_set(v___f_1937_, 0, v___x_1906_);
lean_closure_set(v___f_1937_, 1, v___x_1908_);
lean_closure_set(v___f_1937_, 2, v___x_1909_);
lean_closure_set(v___f_1937_, 3, v_beta_1910_);
lean_closure_set(v___f_1937_, 4, v___x_1935_);
lean_closure_set(v___f_1937_, 5, v_alpha_1912_);
lean_closure_set(v___f_1937_, 6, v___x_1936_);
lean_closure_set(v___f_1937_, 7, v_numDiscrs_1913_);
lean_closure_set(v___f_1937_, 8, v___f_1914_);
lean_closure_set(v___f_1937_, 9, v_a_1915_);
lean_closure_set(v___f_1937_, 10, v_a_1916_);
lean_closure_set(v___f_1937_, 11, v_levelParams_1917_);
lean_closure_set(v___f_1937_, 12, v_matcherName_1918_);
lean_closure_set(v___f_1937_, 13, v___x_1919_);
lean_closure_set(v___f_1937_, 14, v_matcherInfo_1920_);
lean_closure_set(v___f_1937_, 15, v___x_1921_);
lean_closure_set(v___f_1937_, 16, v_f_1924_);
lean_closure_set(v___f_1937_, 17, v___x_1922_);
lean_closure_set(v___f_1937_, 18, v_uElimPos_x3f_1923_);
v___x_1938_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__1));
v___x_1939_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_1938_, v_a_1934_, v___f_1937_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
return v___x_1939_;
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec_ref(v_f_1924_);
lean_dec(v_uElimPos_x3f_1923_);
lean_dec(v___x_1922_);
lean_dec(v___x_1921_);
lean_dec_ref(v_matcherInfo_1920_);
lean_dec_ref(v___x_1919_);
lean_dec(v_matcherName_1918_);
lean_dec(v_levelParams_1917_);
lean_dec(v_a_1916_);
lean_dec(v_a_1915_);
lean_dec_ref(v___f_1914_);
lean_dec(v_numDiscrs_1913_);
lean_dec_ref(v_alpha_1912_);
lean_dec_ref(v_beta_1910_);
lean_dec(v___x_1909_);
lean_dec_ref(v___x_1908_);
lean_dec_ref(v___x_1906_);
v_a_1940_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1933_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1933_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_f_1924_);
lean_dec(v_uElimPos_x3f_1923_);
lean_dec(v___x_1922_);
lean_dec(v___x_1921_);
lean_dec_ref(v_matcherInfo_1920_);
lean_dec_ref(v___x_1919_);
lean_dec(v_matcherName_1918_);
lean_dec(v_levelParams_1917_);
lean_dec(v_a_1916_);
lean_dec(v_a_1915_);
lean_dec_ref(v___f_1914_);
lean_dec(v_numDiscrs_1913_);
lean_dec_ref(v_alpha_1912_);
lean_dec_ref(v_beta_1910_);
lean_dec(v___x_1909_);
lean_dec_ref(v___x_1908_);
lean_dec_ref(v___f_1907_);
lean_dec_ref(v___x_1906_);
v_a_1948_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1930_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1930_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed(lean_object** _args){
lean_object* v___x_1956_ = _args[0];
lean_object* v___f_1957_ = _args[1];
lean_object* v___x_1958_ = _args[2];
lean_object* v___x_1959_ = _args[3];
lean_object* v_beta_1960_ = _args[4];
lean_object* v___x_1961_ = _args[5];
lean_object* v_alpha_1962_ = _args[6];
lean_object* v_numDiscrs_1963_ = _args[7];
lean_object* v___f_1964_ = _args[8];
lean_object* v_a_1965_ = _args[9];
lean_object* v_a_1966_ = _args[10];
lean_object* v_levelParams_1967_ = _args[11];
lean_object* v_matcherName_1968_ = _args[12];
lean_object* v___x_1969_ = _args[13];
lean_object* v_matcherInfo_1970_ = _args[14];
lean_object* v___x_1971_ = _args[15];
lean_object* v___x_1972_ = _args[16];
lean_object* v_uElimPos_x3f_1973_ = _args[17];
lean_object* v_f_1974_ = _args[18];
lean_object* v___y_1975_ = _args[19];
lean_object* v___y_1976_ = _args[20];
lean_object* v___y_1977_ = _args[21];
lean_object* v___y_1978_ = _args[22];
lean_object* v___y_1979_ = _args[23];
_start:
{
uint8_t v___x_17494__boxed_1980_; lean_object* v_res_1981_; 
v___x_17494__boxed_1980_ = lean_unbox(v___x_1961_);
v_res_1981_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(v___x_1956_, v___f_1957_, v___x_1958_, v___x_1959_, v_beta_1960_, v___x_17494__boxed_1980_, v_alpha_1962_, v_numDiscrs_1963_, v___f_1964_, v_a_1965_, v_a_1966_, v_levelParams_1967_, v_matcherName_1968_, v___x_1969_, v_matcherInfo_1970_, v___x_1971_, v___x_1972_, v_uElimPos_x3f_1973_, v_f_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(lean_object* v___x_1988_, lean_object* v_alpha_1989_, lean_object* v___x_1990_, lean_object* v___x_1991_, lean_object* v_numDiscrs_1992_, lean_object* v___f_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_levelParams_1996_, lean_object* v_matcherName_1997_, lean_object* v___x_1998_, lean_object* v_matcherInfo_1999_, lean_object* v___x_2000_, lean_object* v_uElimPos_x3f_2001_, lean_object* v_beta_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; lean_object* v___f_2014_; lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2008_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__1));
v___x_2009_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__3));
lean_inc_n(v___x_1988_, 2);
v___x_2010_ = l_Lean_Expr_bvar___override(v___x_1988_);
lean_inc_ref(v___x_2010_);
lean_inc_ref(v_beta_2002_);
v___x_2011_ = l_Lean_Expr_app___override(v_beta_2002_, v___x_2010_);
v___x_2012_ = 0;
v___x_2013_ = lean_box(v___x_2012_);
lean_inc_ref_n(v_alpha_1989_, 2);
v___f_2014_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2014_, 0, v___x_1988_);
lean_closure_set(v___f_2014_, 1, v___x_2009_);
lean_closure_set(v___f_2014_, 2, v_alpha_1989_);
lean_closure_set(v___f_2014_, 3, v___x_2013_);
v___x_2015_ = lean_box(v___x_2012_);
v___f_2016_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed), 24, 18);
lean_closure_set(v___f_2016_, 0, v___x_1990_);
lean_closure_set(v___f_2016_, 1, v___f_2014_);
lean_closure_set(v___f_2016_, 2, v___x_2010_);
lean_closure_set(v___f_2016_, 3, v___x_1991_);
lean_closure_set(v___f_2016_, 4, v_beta_2002_);
lean_closure_set(v___f_2016_, 5, v___x_2015_);
lean_closure_set(v___f_2016_, 6, v_alpha_1989_);
lean_closure_set(v___f_2016_, 7, v_numDiscrs_1992_);
lean_closure_set(v___f_2016_, 8, v___f_1993_);
lean_closure_set(v___f_2016_, 9, v_a_1994_);
lean_closure_set(v___f_2016_, 10, v_a_1995_);
lean_closure_set(v___f_2016_, 11, v_levelParams_1996_);
lean_closure_set(v___f_2016_, 12, v_matcherName_1997_);
lean_closure_set(v___f_2016_, 13, v___x_1998_);
lean_closure_set(v___f_2016_, 14, v_matcherInfo_1999_);
lean_closure_set(v___f_2016_, 15, v___x_1988_);
lean_closure_set(v___f_2016_, 16, v___x_2000_);
lean_closure_set(v___f_2016_, 17, v_uElimPos_x3f_2001_);
v___x_2017_ = l_Lean_Expr_forallE___override(v___x_2009_, v_alpha_1989_, v___x_2011_, v___x_2012_);
v___x_2018_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2008_, v___x_2017_, v___f_2016_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed(lean_object** _args){
lean_object* v___x_2019_ = _args[0];
lean_object* v_alpha_2020_ = _args[1];
lean_object* v___x_2021_ = _args[2];
lean_object* v___x_2022_ = _args[3];
lean_object* v_numDiscrs_2023_ = _args[4];
lean_object* v___f_2024_ = _args[5];
lean_object* v_a_2025_ = _args[6];
lean_object* v_a_2026_ = _args[7];
lean_object* v_levelParams_2027_ = _args[8];
lean_object* v_matcherName_2028_ = _args[9];
lean_object* v___x_2029_ = _args[10];
lean_object* v_matcherInfo_2030_ = _args[11];
lean_object* v___x_2031_ = _args[12];
lean_object* v_uElimPos_x3f_2032_ = _args[13];
lean_object* v_beta_2033_ = _args[14];
lean_object* v___y_2034_ = _args[15];
lean_object* v___y_2035_ = _args[16];
lean_object* v___y_2036_ = _args[17];
lean_object* v___y_2037_ = _args[18];
lean_object* v___y_2038_ = _args[19];
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(v___x_2019_, v_alpha_2020_, v___x_2021_, v___x_2022_, v_numDiscrs_2023_, v___f_2024_, v_a_2025_, v_a_2026_, v_levelParams_2027_, v_matcherName_2028_, v___x_2029_, v_matcherInfo_2030_, v___x_2031_, v_uElimPos_x3f_2032_, v_beta_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(lean_object* v_a_2043_, lean_object* v___x_2044_, lean_object* v___x_2045_, lean_object* v___x_2046_, lean_object* v_numDiscrs_2047_, lean_object* v___f_2048_, lean_object* v_a_2049_, lean_object* v_levelParams_2050_, lean_object* v_matcherName_2051_, lean_object* v___x_2052_, lean_object* v_matcherInfo_2053_, lean_object* v___x_2054_, lean_object* v_uElimPos_x3f_2055_, lean_object* v_alpha_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_inc(v_a_2043_);
v___x_2062_ = l_Lean_Level_param___override(v_a_2043_);
v___x_2063_ = l_Lean_Expr_sort___override(v___x_2062_);
lean_inc_ref(v_alpha_2056_);
v___x_2064_ = l_Lean_mkArrow(v_alpha_2056_, v___x_2063_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___f_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___f_2066_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed), 20, 14);
lean_closure_set(v___f_2066_, 0, v___x_2044_);
lean_closure_set(v___f_2066_, 1, v_alpha_2056_);
lean_closure_set(v___f_2066_, 2, v___x_2045_);
lean_closure_set(v___f_2066_, 3, v___x_2046_);
lean_closure_set(v___f_2066_, 4, v_numDiscrs_2047_);
lean_closure_set(v___f_2066_, 5, v___f_2048_);
lean_closure_set(v___f_2066_, 6, v_a_2043_);
lean_closure_set(v___f_2066_, 7, v_a_2049_);
lean_closure_set(v___f_2066_, 8, v_levelParams_2050_);
lean_closure_set(v___f_2066_, 9, v_matcherName_2051_);
lean_closure_set(v___f_2066_, 10, v___x_2052_);
lean_closure_set(v___f_2066_, 11, v_matcherInfo_2053_);
lean_closure_set(v___f_2066_, 12, v___x_2054_);
lean_closure_set(v___f_2066_, 13, v_uElimPos_x3f_2055_);
v___x_2067_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__1));
v___x_2068_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2067_, v_a_2065_, v___f_2066_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
return v___x_2068_;
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec_ref(v_alpha_2056_);
lean_dec(v_uElimPos_x3f_2055_);
lean_dec(v___x_2054_);
lean_dec_ref(v_matcherInfo_2053_);
lean_dec_ref(v___x_2052_);
lean_dec(v_matcherName_2051_);
lean_dec(v_levelParams_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v___f_2048_);
lean_dec(v_numDiscrs_2047_);
lean_dec(v___x_2046_);
lean_dec_ref(v___x_2045_);
lean_dec(v___x_2044_);
lean_dec(v_a_2043_);
v_a_2069_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2064_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2064_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed(lean_object** _args){
lean_object* v_a_2077_ = _args[0];
lean_object* v___x_2078_ = _args[1];
lean_object* v___x_2079_ = _args[2];
lean_object* v___x_2080_ = _args[3];
lean_object* v_numDiscrs_2081_ = _args[4];
lean_object* v___f_2082_ = _args[5];
lean_object* v_a_2083_ = _args[6];
lean_object* v_levelParams_2084_ = _args[7];
lean_object* v_matcherName_2085_ = _args[8];
lean_object* v___x_2086_ = _args[9];
lean_object* v_matcherInfo_2087_ = _args[10];
lean_object* v___x_2088_ = _args[11];
lean_object* v_uElimPos_x3f_2089_ = _args[12];
lean_object* v_alpha_2090_ = _args[13];
lean_object* v___y_2091_ = _args[14];
lean_object* v___y_2092_ = _args[15];
lean_object* v___y_2093_ = _args[16];
lean_object* v___y_2094_ = _args[17];
lean_object* v___y_2095_ = _args[18];
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(v_a_2077_, v___x_2078_, v___x_2079_, v___x_2080_, v_numDiscrs_2081_, v___f_2082_, v_a_2083_, v_levelParams_2084_, v_matcherName_2085_, v___x_2086_, v_matcherInfo_2087_, v___x_2088_, v_uElimPos_x3f_2089_, v_alpha_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(lean_object* v_numParams_2106_, lean_object* v___x_2107_, lean_object* v___x_2108_, lean_object* v_numDiscrs_2109_, lean_object* v___f_2110_, lean_object* v_levelParams_2111_, lean_object* v_matcherName_2112_, lean_object* v_matcherInfo_2113_, lean_object* v___x_2114_, lean_object* v_uElimPos_x3f_2115_, lean_object* v_xs_2116_, lean_object* v_x_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__1));
v___x_2124_ = l_Lean_Core_mkFreshUserName(v___x_2123_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__3));
v___x_2127_ = l_Lean_Core_mkFreshUserName(v___x_2126_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___f_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___x_2129_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2106_);
lean_inc_ref(v_xs_2116_);
v___x_2130_ = l_Array_toSubarray___redArg(v_xs_2116_, v___x_2129_, v_numParams_2106_);
v___x_2131_ = lean_array_get(v___x_2107_, v_xs_2116_, v_numParams_2106_);
lean_dec(v_numParams_2106_);
lean_dec_ref(v_xs_2116_);
lean_inc(v_a_2125_);
v___f_2132_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed), 19, 13);
lean_closure_set(v___f_2132_, 0, v_a_2128_);
lean_closure_set(v___f_2132_, 1, v___x_2129_);
lean_closure_set(v___f_2132_, 2, v___x_2131_);
lean_closure_set(v___f_2132_, 3, v___x_2108_);
lean_closure_set(v___f_2132_, 4, v_numDiscrs_2109_);
lean_closure_set(v___f_2132_, 5, v___f_2110_);
lean_closure_set(v___f_2132_, 6, v_a_2125_);
lean_closure_set(v___f_2132_, 7, v_levelParams_2111_);
lean_closure_set(v___f_2132_, 8, v_matcherName_2112_);
lean_closure_set(v___f_2132_, 9, v___x_2130_);
lean_closure_set(v___f_2132_, 10, v_matcherInfo_2113_);
lean_closure_set(v___f_2132_, 11, v___x_2114_);
lean_closure_set(v___f_2132_, 12, v_uElimPos_x3f_2115_);
v___x_2133_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__5));
v___x_2134_ = l_Lean_Level_param___override(v_a_2125_);
v___x_2135_ = l_Lean_Expr_sort___override(v___x_2134_);
v___x_2136_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2133_, v___x_2135_, v___f_2132_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
return v___x_2136_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_a_2125_);
lean_dec_ref(v_xs_2116_);
lean_dec(v_uElimPos_x3f_2115_);
lean_dec(v___x_2114_);
lean_dec_ref(v_matcherInfo_2113_);
lean_dec(v_matcherName_2112_);
lean_dec(v_levelParams_2111_);
lean_dec_ref(v___f_2110_);
lean_dec(v_numDiscrs_2109_);
lean_dec(v___x_2108_);
lean_dec(v_numParams_2106_);
v_a_2137_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2127_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2127_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref(v_xs_2116_);
lean_dec(v_uElimPos_x3f_2115_);
lean_dec(v___x_2114_);
lean_dec_ref(v_matcherInfo_2113_);
lean_dec(v_matcherName_2112_);
lean_dec(v_levelParams_2111_);
lean_dec_ref(v___f_2110_);
lean_dec(v_numDiscrs_2109_);
lean_dec(v___x_2108_);
lean_dec(v_numParams_2106_);
v_a_2145_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2124_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2124_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed(lean_object** _args){
lean_object* v_numParams_2153_ = _args[0];
lean_object* v___x_2154_ = _args[1];
lean_object* v___x_2155_ = _args[2];
lean_object* v_numDiscrs_2156_ = _args[3];
lean_object* v___f_2157_ = _args[4];
lean_object* v_levelParams_2158_ = _args[5];
lean_object* v_matcherName_2159_ = _args[6];
lean_object* v_matcherInfo_2160_ = _args[7];
lean_object* v___x_2161_ = _args[8];
lean_object* v_uElimPos_x3f_2162_ = _args[9];
lean_object* v_xs_2163_ = _args[10];
lean_object* v_x_2164_ = _args[11];
lean_object* v___y_2165_ = _args[12];
lean_object* v___y_2166_ = _args[13];
lean_object* v___y_2167_ = _args[14];
lean_object* v___y_2168_ = _args[15];
lean_object* v___y_2169_ = _args[16];
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(v_numParams_2153_, v___x_2154_, v___x_2155_, v_numDiscrs_2156_, v___f_2157_, v_levelParams_2158_, v_matcherName_2159_, v_matcherInfo_2160_, v___x_2161_, v_uElimPos_x3f_2162_, v_xs_2163_, v_x_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec_ref(v_x_2164_);
lean_dec_ref(v___x_2154_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(lean_object* v_ref_2171_, lean_object* v_msg_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_fileName_2178_; lean_object* v_fileMap_2179_; lean_object* v_options_2180_; lean_object* v_currRecDepth_2181_; lean_object* v_maxRecDepth_2182_; lean_object* v_ref_2183_; lean_object* v_currNamespace_2184_; lean_object* v_openDecls_2185_; lean_object* v_initHeartbeats_2186_; lean_object* v_maxHeartbeats_2187_; lean_object* v_quotContext_2188_; lean_object* v_currMacroScope_2189_; uint8_t v_diag_2190_; lean_object* v_cancelTk_x3f_2191_; uint8_t v_suppressElabErrors_2192_; lean_object* v_inheritedTraceOptions_2193_; lean_object* v_ref_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_fileName_2178_ = lean_ctor_get(v___y_2175_, 0);
v_fileMap_2179_ = lean_ctor_get(v___y_2175_, 1);
v_options_2180_ = lean_ctor_get(v___y_2175_, 2);
v_currRecDepth_2181_ = lean_ctor_get(v___y_2175_, 3);
v_maxRecDepth_2182_ = lean_ctor_get(v___y_2175_, 4);
v_ref_2183_ = lean_ctor_get(v___y_2175_, 5);
v_currNamespace_2184_ = lean_ctor_get(v___y_2175_, 6);
v_openDecls_2185_ = lean_ctor_get(v___y_2175_, 7);
v_initHeartbeats_2186_ = lean_ctor_get(v___y_2175_, 8);
v_maxHeartbeats_2187_ = lean_ctor_get(v___y_2175_, 9);
v_quotContext_2188_ = lean_ctor_get(v___y_2175_, 10);
v_currMacroScope_2189_ = lean_ctor_get(v___y_2175_, 11);
v_diag_2190_ = lean_ctor_get_uint8(v___y_2175_, sizeof(void*)*14);
v_cancelTk_x3f_2191_ = lean_ctor_get(v___y_2175_, 12);
v_suppressElabErrors_2192_ = lean_ctor_get_uint8(v___y_2175_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2193_ = lean_ctor_get(v___y_2175_, 13);
v_ref_2194_ = l_Lean_replaceRef(v_ref_2171_, v_ref_2183_);
lean_inc_ref(v_inheritedTraceOptions_2193_);
lean_inc(v_cancelTk_x3f_2191_);
lean_inc(v_currMacroScope_2189_);
lean_inc(v_quotContext_2188_);
lean_inc(v_maxHeartbeats_2187_);
lean_inc(v_initHeartbeats_2186_);
lean_inc(v_openDecls_2185_);
lean_inc(v_currNamespace_2184_);
lean_inc(v_maxRecDepth_2182_);
lean_inc(v_currRecDepth_2181_);
lean_inc_ref(v_options_2180_);
lean_inc_ref(v_fileMap_2179_);
lean_inc_ref(v_fileName_2178_);
v___x_2195_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2195_, 0, v_fileName_2178_);
lean_ctor_set(v___x_2195_, 1, v_fileMap_2179_);
lean_ctor_set(v___x_2195_, 2, v_options_2180_);
lean_ctor_set(v___x_2195_, 3, v_currRecDepth_2181_);
lean_ctor_set(v___x_2195_, 4, v_maxRecDepth_2182_);
lean_ctor_set(v___x_2195_, 5, v_ref_2194_);
lean_ctor_set(v___x_2195_, 6, v_currNamespace_2184_);
lean_ctor_set(v___x_2195_, 7, v_openDecls_2185_);
lean_ctor_set(v___x_2195_, 8, v_initHeartbeats_2186_);
lean_ctor_set(v___x_2195_, 9, v_maxHeartbeats_2187_);
lean_ctor_set(v___x_2195_, 10, v_quotContext_2188_);
lean_ctor_set(v___x_2195_, 11, v_currMacroScope_2189_);
lean_ctor_set(v___x_2195_, 12, v_cancelTk_x3f_2191_);
lean_ctor_set(v___x_2195_, 13, v_inheritedTraceOptions_2193_);
lean_ctor_set_uint8(v___x_2195_, sizeof(void*)*14, v_diag_2190_);
lean_ctor_set_uint8(v___x_2195_, sizeof(void*)*14 + 1, v_suppressElabErrors_2192_);
v___x_2196_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_2172_, v___y_2173_, v___y_2174_, v___x_2195_, v___y_2176_);
lean_dec_ref_known(v___x_2195_, 14);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2197_, lean_object* v_msg_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2197_, v_msg_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v_ref_2197_);
return v_res_2204_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2209_ = lean_unsigned_to_nat(0u);
v___x_2210_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
lean_ctor_set(v___x_2210_, 2, v___x_2209_);
lean_ctor_set(v___x_2210_, 3, v___x_2209_);
lean_ctor_set(v___x_2210_, 4, v___x_2208_);
lean_ctor_set(v___x_2210_, 5, v___x_2208_);
lean_ctor_set(v___x_2210_, 6, v___x_2208_);
lean_ctor_set(v___x_2210_, 7, v___x_2208_);
lean_ctor_set(v___x_2210_, 8, v___x_2208_);
lean_ctor_set(v___x_2210_, 9, v___x_2208_);
lean_ctor_set(v___x_2210_, 10, v___x_2208_);
return v___x_2210_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = lean_unsigned_to_nat(32u);
v___x_2212_ = lean_mk_empty_array_with_capacity(v___x_2211_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2214_ = ((size_t)5ULL);
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = lean_unsigned_to_nat(32u);
v___x_2217_ = lean_mk_empty_array_with_capacity(v___x_2216_);
v___x_2218_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3);
v___x_2219_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v___x_2217_);
lean_ctor_set(v___x_2219_, 2, v___x_2215_);
lean_ctor_set(v___x_2219_, 3, v___x_2215_);
lean_ctor_set_usize(v___x_2219_, 4, v___x_2214_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2220_ = lean_box(1);
v___x_2221_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4);
v___x_2222_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v___x_2221_);
lean_ctor_set(v___x_2223_, 2, v___x_2220_);
return v___x_2223_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__6));
v___x_2226_ = l_Lean_stringToMessageData(v___x_2225_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__8));
v___x_2229_ = l_Lean_stringToMessageData(v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__10));
v___x_2232_ = l_Lean_stringToMessageData(v___x_2231_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__12));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__14));
v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18));
v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2245_, lean_object* v_declHint_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; lean_object* v_env_2250_; uint8_t v___x_2251_; 
v___x_2249_ = lean_st_ref_get(v___y_2247_);
v_env_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc_ref(v_env_2250_);
lean_dec(v___x_2249_);
v___x_2251_ = l_Lean_Name_isAnonymous(v_declHint_2246_);
if (v___x_2251_ == 0)
{
uint8_t v_isExporting_2252_; 
v_isExporting_2252_ = lean_ctor_get_uint8(v_env_2250_, sizeof(void*)*8);
if (v_isExporting_2252_ == 0)
{
lean_object* v___x_2253_; 
lean_dec_ref(v_env_2250_);
lean_dec(v_declHint_2246_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_msg_2245_);
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; uint8_t v___x_2255_; 
lean_inc_ref(v_env_2250_);
v___x_2254_ = l_Lean_Environment_setExporting(v_env_2250_, v___x_2251_);
lean_inc(v_declHint_2246_);
lean_inc_ref(v___x_2254_);
v___x_2255_ = l_Lean_Environment_contains(v___x_2254_, v_declHint_2246_, v_isExporting_2252_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; 
lean_dec_ref(v___x_2254_);
lean_dec_ref(v_env_2250_);
lean_dec(v_declHint_2246_);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v_msg_2245_);
return v___x_2256_;
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_c_2262_; lean_object* v___x_2263_; 
v___x_2257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2258_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2259_ = l_Lean_Options_empty;
v___x_2260_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2254_);
lean_ctor_set(v___x_2260_, 1, v___x_2257_);
lean_ctor_set(v___x_2260_, 2, v___x_2258_);
lean_ctor_set(v___x_2260_, 3, v___x_2259_);
lean_inc(v_declHint_2246_);
v___x_2261_ = l_Lean_MessageData_ofConstName(v_declHint_2246_, v___x_2251_);
v_c_2262_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2262_, 0, v___x_2260_);
lean_ctor_set(v_c_2262_, 1, v___x_2261_);
v___x_2263_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2250_, v_declHint_2246_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec_ref(v_env_2250_);
lean_dec(v_declHint_2246_);
v___x_2264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v_c_2262_);
v___x_2266_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = l_Lean_MessageData_note(v___x_2267_);
v___x_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2269_, 0, v_msg_2245_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
else
{
lean_object* v_val_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2306_; 
v_val_2271_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2273_ = v___x_2263_;
v_isShared_2274_ = v_isSharedCheck_2306_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_val_2271_);
lean_dec(v___x_2263_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2306_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v_mod_2278_; uint8_t v___x_2279_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = l_Lean_Environment_header(v_env_2250_);
lean_dec_ref(v_env_2250_);
v___x_2277_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2276_);
v_mod_2278_ = lean_array_get(v___x_2275_, v___x_2277_, v_val_2271_);
lean_dec(v_val_2271_);
lean_dec_ref(v___x_2277_);
v___x_2279_ = l_Lean_isPrivateName(v_declHint_2246_);
lean_dec(v_declHint_2246_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2291_; 
v___x_2280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
lean_ctor_set(v___x_2281_, 1, v_c_2262_);
v___x_2282_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2281_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = l_Lean_MessageData_ofName(v_mod_2278_);
v___x_2285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = l_Lean_MessageData_note(v___x_2287_);
v___x_2289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2289_, 0, v_msg_2245_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set_tag(v___x_2273_, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2289_);
v___x_2291_ = v___x_2273_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v_c_2262_);
v___x_2295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = l_Lean_MessageData_ofName(v_mod_2278_);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = l_Lean_MessageData_note(v___x_2300_);
v___x_2302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2302_, 0, v_msg_2245_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set_tag(v___x_2273_, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2302_);
v___x_2304_ = v___x_2273_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2307_; 
lean_dec_ref(v_env_2250_);
lean_dec(v_declHint_2246_);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v_msg_2245_);
return v___x_2307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2308_, lean_object* v_declHint_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2308_, v_declHint_2309_, v___y_2310_);
lean_dec(v___y_2310_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(lean_object* v_msg_2313_, lean_object* v_declHint_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2320_; lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2330_; 
v___x_2320_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2313_, v_declHint_2314_, v___y_2318_);
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2330_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2330_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2325_ = l_Lean_unknownIdentifierMessageTag;
v___x_2326_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v_a_2321_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2326_);
v___x_2328_ = v___x_2323_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11___boxed(lean_object* v_msg_2331_, lean_object* v_declHint_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2331_, v_declHint_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_ref_2339_, lean_object* v_msg_2340_, lean_object* v_declHint_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; lean_object* v_a_2348_; lean_object* v___x_2349_; 
v___x_2347_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2340_, v_declHint_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref(v___x_2347_);
v___x_2349_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2339_, v_a_2348_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_ref_2350_, lean_object* v_msg_2351_, lean_object* v_declHint_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2350_, v_msg_2351_, v_declHint_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v_ref_2350_);
return v_res_2358_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_2361_ = l_Lean_stringToMessageData(v___x_2360_);
return v___x_2361_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_2364_ = l_Lean_stringToMessageData(v___x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_2365_, lean_object* v_constName_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2372_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_2373_ = 0;
lean_inc(v_constName_2366_);
v___x_2374_ = l_Lean_MessageData_ofConstName(v_constName_2366_, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2372_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2365_, v___x_2377_, v_constName_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_2379_, lean_object* v_constName_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2379_, v_constName_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v_ref_2379_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(lean_object* v_constName_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_ref_2393_; lean_object* v___x_2394_; 
v_ref_2393_ = lean_ctor_get(v___y_2390_, 5);
v___x_2394_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2393_, v_constName_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(lean_object* v_constName_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___x_2408_; lean_object* v_env_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; 
v___x_2408_ = lean_st_ref_get(v___y_2406_);
v_env_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc_ref(v_env_2409_);
lean_dec(v___x_2408_);
v___x_2410_ = 0;
lean_inc(v_constName_2402_);
v___x_2411_ = l_Lean_Environment_findConstVal_x3f(v_env_2409_, v_constName_2402_, v___x_2410_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2412_;
}
else
{
lean_object* v_val_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec(v_constName_2402_);
v_val_2413_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2411_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_val_2413_);
lean_dec(v___x_2411_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set_tag(v___x_2415_, 0);
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_val_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0___boxed(lean_object* v_constName_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_constName_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(lean_object* v_matcherName_2428_, lean_object* v_matcherInfo_2429_, lean_object* v___x_2430_, lean_object* v___f_2431_, lean_object* v___x_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v___x_2438_; 
lean_inc(v_matcherName_2428_);
v___x_2438_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_matcherName_2428_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v_levelParams_2440_; lean_object* v_type_2441_; lean_object* v_numParams_2442_; lean_object* v_numDiscrs_2443_; lean_object* v_uElimPos_x3f_2444_; lean_object* v___x_2445_; lean_object* v___f_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v_levelParams_2440_ = lean_ctor_get(v_a_2439_, 1);
lean_inc(v_levelParams_2440_);
v_type_2441_ = lean_ctor_get(v_a_2439_, 2);
lean_inc_ref(v_type_2441_);
lean_dec(v_a_2439_);
v_numParams_2442_ = lean_ctor_get(v_matcherInfo_2429_, 0);
lean_inc_n(v_numParams_2442_, 2);
v_numDiscrs_2443_ = lean_ctor_get(v_matcherInfo_2429_, 1);
lean_inc(v_numDiscrs_2443_);
v_uElimPos_x3f_2444_ = lean_ctor_get(v_matcherInfo_2429_, 3);
lean_inc(v_uElimPos_x3f_2444_);
v___x_2445_ = lean_unsigned_to_nat(1u);
v___f_2446_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed), 17, 10);
lean_closure_set(v___f_2446_, 0, v_numParams_2442_);
lean_closure_set(v___f_2446_, 1, v___x_2430_);
lean_closure_set(v___f_2446_, 2, v___x_2445_);
lean_closure_set(v___f_2446_, 3, v_numDiscrs_2443_);
lean_closure_set(v___f_2446_, 4, v___f_2431_);
lean_closure_set(v___f_2446_, 5, v_levelParams_2440_);
lean_closure_set(v___f_2446_, 6, v_matcherName_2428_);
lean_closure_set(v___f_2446_, 7, v_matcherInfo_2429_);
lean_closure_set(v___f_2446_, 8, v___x_2432_);
lean_closure_set(v___f_2446_, 9, v_uElimPos_x3f_2444_);
v___x_2447_ = lean_nat_add(v_numParams_2442_, v___x_2445_);
lean_dec(v_numParams_2442_);
v___x_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
v___x_2449_ = 0;
v___x_2450_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_2441_, v___x_2448_, v___f_2446_, v___x_2449_, v___x_2449_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
return v___x_2450_;
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v___x_2432_);
lean_dec_ref(v___f_2431_);
lean_dec_ref(v___x_2430_);
lean_dec_ref(v_matcherInfo_2429_);
lean_dec(v_matcherName_2428_);
v_a_2451_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2438_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2438_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed(lean_object* v_matcherName_2459_, lean_object* v_matcherInfo_2460_, lean_object* v___x_2461_, lean_object* v___f_2462_, lean_object* v___x_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(v_matcherName_2459_, v_matcherInfo_2460_, v___x_2461_, v___f_2462_, v___x_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11(lean_object* v___x_2470_, lean_object* v_e_2471_){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = l_Lean_indentD(v_e_2471_);
v___x_2473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2470_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(lean_object* v___f_2474_, lean_object* v___f_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2474_, v___f_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_a_2490_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2481_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2481_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed(lean_object* v___f_2498_, lean_object* v___f_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(v___f_2498_, v___f_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
return v_res_2505_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__3));
v___x_2512_ = l_Lean_stringToMessageData(v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(lean_object* v_matcherName_2513_, lean_object* v_matcherInfo_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v___x_2520_; lean_object* v_env_2521_; lean_object* v___f_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___f_2531_; lean_object* v___f_2532_; lean_object* v___x_2533_; 
v___x_2520_ = lean_st_ref_get(v_a_2518_);
v_env_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc_ref(v_env_2521_);
lean_dec(v___x_2520_);
v___f_2522_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__0));
v___x_2523_ = l_Lean_instInhabitedExpr;
lean_inc_n(v_matcherName_2513_, 3);
v___x_2524_ = l_Lean_mkPrivateName(v_env_2521_, v_matcherName_2513_);
lean_dec_ref(v_env_2521_);
v___x_2525_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__2));
v___x_2526_ = l_Lean_Name_append(v___x_2524_, v___x_2525_);
lean_inc_n(v___x_2526_, 2);
v___f_2527_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed), 10, 5);
lean_closure_set(v___f_2527_, 0, v_matcherName_2513_);
lean_closure_set(v___f_2527_, 1, v_matcherInfo_2514_);
lean_closure_set(v___f_2527_, 2, v___x_2523_);
lean_closure_set(v___f_2527_, 3, v___f_2522_);
lean_closure_set(v___f_2527_, 4, v___x_2526_);
v___x_2528_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4);
v___x_2529_ = l_Lean_MessageData_ofName(v_matcherName_2513_);
v___x_2530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2528_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___f_2531_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_2531_, 0, v___x_2530_);
v___f_2532_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed), 7, 2);
lean_closure_set(v___f_2532_, 0, v___f_2527_);
lean_closure_set(v___f_2532_, 1, v___f_2531_);
v___x_2533_ = l_Lean_Meta_realizeConst(v_matcherName_2513_, v___x_2526_, v___f_2532_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; 
v_unused_2541_ = lean_ctor_get(v___x_2533_, 0);
lean_dec(v_unused_2541_);
v___x_2535_ = v___x_2533_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_dec(v___x_2533_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2526_);
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2526_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v___x_2526_);
v_a_2542_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2533_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2533_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___boxed(lean_object* v_matcherName_2550_, lean_object* v_matcherInfo_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_2550_, v_matcherInfo_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(lean_object* v_as_2558_, lean_object* v_as_x27_2559_, lean_object* v_b_2560_, lean_object* v_a_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_2559_, v_b_2560_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___boxed(lean_object* v_as_2568_, lean_object* v_as_x27_2569_, lean_object* v_b_2570_, lean_object* v_a_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(v_as_2568_, v_as_x27_2569_, v_b_2570_, v_a_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v_as_x27_2569_);
lean_dec(v_as_2568_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(lean_object* v_00_u03b1_2578_, lean_object* v_name_2579_, uint8_t v_bi_2580_, lean_object* v_type_2581_, lean_object* v_k_2582_, uint8_t v_kind_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_2579_, v_bi_2580_, v_type_2581_, v_k_2582_, v_kind_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2590_, lean_object* v_name_2591_, lean_object* v_bi_2592_, lean_object* v_type_2593_, lean_object* v_k_2594_, lean_object* v_kind_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
uint8_t v_bi_boxed_2601_; uint8_t v_kind_boxed_2602_; lean_object* v_res_2603_; 
v_bi_boxed_2601_ = lean_unbox(v_bi_2592_);
v_kind_boxed_2602_ = lean_unbox(v_kind_2595_);
v_res_2603_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(v_00_u03b1_2590_, v_name_2591_, v_bi_boxed_2601_, v_type_2593_, v_k_2594_, v_kind_boxed_2602_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(lean_object* v_00_u03b1_2604_, lean_object* v_name_2605_, lean_object* v_type_2606_, lean_object* v_k_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_2605_, v_type_2606_, v_k_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___boxed(lean_object* v_00_u03b1_2614_, lean_object* v_name_2615_, lean_object* v_type_2616_, lean_object* v_k_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(v_00_u03b1_2614_, v_name_2615_, v_type_2616_, v_k_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(lean_object* v_00_u03b1_2624_, lean_object* v_constName_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2632_, lean_object* v_constName_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(v_00_u03b1_2632_, v_constName_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2640_, lean_object* v_ref_2641_, lean_object* v_constName_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2641_, v_constName_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2649_, lean_object* v_ref_2650_, lean_object* v_constName_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(v_00_u03b1_2649_, v_ref_2650_, v_constName_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v_ref_2650_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b1_2658_, lean_object* v_ref_2659_, lean_object* v_msg_2660_, lean_object* v_declHint_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2659_, v_msg_2660_, v_declHint_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b1_2668_, lean_object* v_ref_2669_, lean_object* v_msg_2670_, lean_object* v_declHint_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(v_00_u03b1_2668_, v_ref_2669_, v_msg_2670_, v_declHint_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v_ref_2669_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(lean_object* v_msg_2678_, lean_object* v_declHint_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2678_, v_declHint_2679_, v___y_2683_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_2686_, lean_object* v_declHint_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(v_msg_2686_, v_declHint_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_2694_, lean_object* v_ref_2695_, lean_object* v_msg_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2695_, v_msg_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_2703_, lean_object* v_ref_2704_, lean_object* v_msg_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(v_00_u03b1_2703_, v_ref_2704_, v_msg_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v_ref_2704_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(lean_object* v_msg_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___f_2722_; lean_object* v___x_41558__overap_2723_; lean_object* v___x_2724_; 
v___f_2722_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0));
v___x_41558__overap_2723_ = lean_panic_fn_borrowed(v___f_2722_, v_msg_2713_);
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2719_);
lean_inc(v___y_2718_);
lean_inc_ref(v___y_2717_);
lean_inc(v___y_2716_);
lean_inc_ref(v___y_2715_);
lean_inc(v___y_2714_);
v___x_2724_ = lean_apply_8(v___x_41558__overap_2723_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, lean_box(0));
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___boxed(lean_object* v_msg_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v_msg_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(lean_object* v_k_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v_b_2739_, lean_object* v_c_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; 
lean_inc(v___y_2744_);
lean_inc_ref(v___y_2743_);
lean_inc(v___y_2742_);
lean_inc_ref(v___y_2741_);
lean_inc(v___y_2738_);
lean_inc_ref(v___y_2737_);
lean_inc(v___y_2736_);
v___x_2746_ = lean_apply_10(v_k_2735_, v_b_2739_, v_c_2740_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, lean_box(0));
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed(lean_object* v_k_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v_b_2751_, lean_object* v_c_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(v_k_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v_b_2751_, v_c_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(lean_object* v_e_2759_, lean_object* v_k_2760_, uint8_t v_cleanupAnnotations_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v___f_2770_; uint8_t v___x_2771_; uint8_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
lean_inc(v___y_2762_);
v___f_2770_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2770_, 0, v_k_2760_);
lean_closure_set(v___f_2770_, 1, v___y_2762_);
lean_closure_set(v___f_2770_, 2, v___y_2763_);
lean_closure_set(v___f_2770_, 3, v___y_2764_);
v___x_2771_ = 1;
v___x_2772_ = 0;
v___x_2773_ = lean_box(0);
v___x_2774_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2759_, v___x_2771_, v___x_2772_, v___x_2771_, v___x_2772_, v___x_2773_, v___f_2770_, v_cleanupAnnotations_2761_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2774_) == 0)
{
return v___x_2774_;
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___boxed(lean_object* v_e_2783_, lean_object* v_k_2784_, lean_object* v_cleanupAnnotations_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2794_; lean_object* v_res_2795_; 
v_cleanupAnnotations_boxed_2794_ = lean_unbox(v_cleanupAnnotations_2785_);
v_res_2795_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2783_, v_k_2784_, v_cleanupAnnotations_boxed_2794_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(lean_object* v_00_u03b1_2796_, lean_object* v_e_2797_, lean_object* v_k_2798_, uint8_t v_cleanupAnnotations_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2797_, v_k_2798_, v_cleanupAnnotations_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___boxed(lean_object* v_00_u03b1_2809_, lean_object* v_e_2810_, lean_object* v_k_2811_, lean_object* v_cleanupAnnotations_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2821_; lean_object* v_res_2822_; 
v_cleanupAnnotations_boxed_2821_ = lean_unbox(v_cleanupAnnotations_2812_);
v_res_2822_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(v_00_u03b1_2809_, v_e_2810_, v_k_2811_, v_cleanupAnnotations_boxed_2821_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(uint8_t v___x_2823_, uint8_t v___x_2824_, uint8_t v___x_2825_, lean_object* v_xs_2826_, lean_object* v_motiveBody_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; lean_object* v___x_2843_; 
v___x_2836_ = l_Lean_Expr_bindingDomain_x21(v_motiveBody_2827_);
v___x_2837_ = l_Lean_Expr_bindingName_x21(v___x_2836_);
v___x_2838_ = l_Lean_Expr_bindingDomain_x21(v___x_2836_);
v___x_2839_ = l_Lean_Expr_bindingBody_x21(v___x_2836_);
lean_dec_ref(v___x_2836_);
v___x_2840_ = l_Lean_Expr_bindingDomain_x21(v___x_2839_);
lean_dec_ref(v___x_2839_);
v___x_2841_ = l_Lean_Expr_lam___override(v___x_2837_, v___x_2838_, v___x_2840_, v___x_2823_);
v___x_2842_ = 1;
v___x_2843_ = l_Lean_Meta_mkLambdaFVars(v_xs_2826_, v___x_2841_, v___x_2824_, v___x_2825_, v___x_2824_, v___x_2825_, v___x_2842_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed(lean_object* v___x_2844_, lean_object* v___x_2845_, lean_object* v___x_2846_, lean_object* v_xs_2847_, lean_object* v_motiveBody_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
uint8_t v___x_49349__boxed_2857_; uint8_t v___x_49350__boxed_2858_; uint8_t v___x_49351__boxed_2859_; lean_object* v_res_2860_; 
v___x_49349__boxed_2857_ = lean_unbox(v___x_2844_);
v___x_49350__boxed_2858_ = lean_unbox(v___x_2845_);
v___x_49351__boxed_2859_ = lean_unbox(v___x_2846_);
v_res_2860_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(v___x_49349__boxed_2857_, v___x_49350__boxed_2858_, v___x_49351__boxed_2859_, v_xs_2847_, v_motiveBody_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v_motiveBody_2848_);
lean_dec_ref(v_xs_2847_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(size_t v_sz_2861_, size_t v_i_2862_, lean_object* v_bs_2863_){
_start:
{
uint8_t v___x_2864_; 
v___x_2864_ = lean_usize_dec_lt(v_i_2862_, v_sz_2861_);
if (v___x_2864_ == 0)
{
return v_bs_2863_;
}
else
{
lean_object* v_v_2865_; lean_object* v___x_2866_; lean_object* v_bs_x27_2867_; lean_object* v___x_2868_; size_t v___x_2869_; size_t v___x_2870_; lean_object* v___x_2871_; 
v_v_2865_ = lean_array_uget(v_bs_2863_, v_i_2862_);
v___x_2866_ = lean_unsigned_to_nat(0u);
v_bs_x27_2867_ = lean_array_uset(v_bs_2863_, v_i_2862_, v___x_2866_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v_v_2865_);
v___x_2869_ = ((size_t)1ULL);
v___x_2870_ = lean_usize_add(v_i_2862_, v___x_2869_);
v___x_2871_ = lean_array_uset(v_bs_x27_2867_, v_i_2862_, v___x_2868_);
v_i_2862_ = v___x_2870_;
v_bs_2863_ = v___x_2871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4___boxed(lean_object* v_sz_2873_, lean_object* v_i_2874_, lean_object* v_bs_2875_){
_start:
{
size_t v_sz_boxed_2876_; size_t v_i_boxed_2877_; lean_object* v_res_2878_; 
v_sz_boxed_2876_ = lean_unbox_usize(v_sz_2873_);
lean_dec(v_sz_2873_);
v_i_boxed_2877_ = lean_unbox_usize(v_i_2874_);
lean_dec(v_i_2874_);
v_res_2878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_boxed_2876_, v_i_boxed_2877_, v_bs_2875_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(lean_object* v_msg_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_ref_2885_; lean_object* v___x_2886_; lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2895_; 
v_ref_2885_ = lean_ctor_get(v___y_2882_, 5);
v___x_2886_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2889_ = v___x_2886_;
v_isShared_2890_ = v_isSharedCheck_2895_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2886_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2895_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; lean_object* v___x_2893_; 
lean_inc(v_ref_2885_);
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v_ref_2885_);
lean_ctor_set(v___x_2891_, 1, v_a_2887_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set_tag(v___x_2889_, 1);
lean_ctor_set(v___x_2889_, 0, v___x_2891_);
v___x_2893_ = v___x_2889_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg___boxed(lean_object* v_msg_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(lean_object* v_declName_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v___x_2906_; lean_object* v_env_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2906_ = lean_st_ref_get(v___y_2904_);
v_env_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc_ref(v_env_2907_);
lean_dec(v___x_2906_);
v___x_2908_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2907_, v_declName_2903_);
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg___boxed(lean_object* v_declName_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_2910_, v___y_2911_);
lean_dec(v___y_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(lean_object* v_ref_2914_, lean_object* v_msg_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_fileName_2924_; lean_object* v_fileMap_2925_; lean_object* v_options_2926_; lean_object* v_currRecDepth_2927_; lean_object* v_maxRecDepth_2928_; lean_object* v_ref_2929_; lean_object* v_currNamespace_2930_; lean_object* v_openDecls_2931_; lean_object* v_initHeartbeats_2932_; lean_object* v_maxHeartbeats_2933_; lean_object* v_quotContext_2934_; lean_object* v_currMacroScope_2935_; uint8_t v_diag_2936_; lean_object* v_cancelTk_x3f_2937_; uint8_t v_suppressElabErrors_2938_; lean_object* v_inheritedTraceOptions_2939_; lean_object* v_ref_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_fileName_2924_ = lean_ctor_get(v___y_2921_, 0);
v_fileMap_2925_ = lean_ctor_get(v___y_2921_, 1);
v_options_2926_ = lean_ctor_get(v___y_2921_, 2);
v_currRecDepth_2927_ = lean_ctor_get(v___y_2921_, 3);
v_maxRecDepth_2928_ = lean_ctor_get(v___y_2921_, 4);
v_ref_2929_ = lean_ctor_get(v___y_2921_, 5);
v_currNamespace_2930_ = lean_ctor_get(v___y_2921_, 6);
v_openDecls_2931_ = lean_ctor_get(v___y_2921_, 7);
v_initHeartbeats_2932_ = lean_ctor_get(v___y_2921_, 8);
v_maxHeartbeats_2933_ = lean_ctor_get(v___y_2921_, 9);
v_quotContext_2934_ = lean_ctor_get(v___y_2921_, 10);
v_currMacroScope_2935_ = lean_ctor_get(v___y_2921_, 11);
v_diag_2936_ = lean_ctor_get_uint8(v___y_2921_, sizeof(void*)*14);
v_cancelTk_x3f_2937_ = lean_ctor_get(v___y_2921_, 12);
v_suppressElabErrors_2938_ = lean_ctor_get_uint8(v___y_2921_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2939_ = lean_ctor_get(v___y_2921_, 13);
v_ref_2940_ = l_Lean_replaceRef(v_ref_2914_, v_ref_2929_);
lean_inc_ref(v_inheritedTraceOptions_2939_);
lean_inc(v_cancelTk_x3f_2937_);
lean_inc(v_currMacroScope_2935_);
lean_inc(v_quotContext_2934_);
lean_inc(v_maxHeartbeats_2933_);
lean_inc(v_initHeartbeats_2932_);
lean_inc(v_openDecls_2931_);
lean_inc(v_currNamespace_2930_);
lean_inc(v_maxRecDepth_2928_);
lean_inc(v_currRecDepth_2927_);
lean_inc_ref(v_options_2926_);
lean_inc_ref(v_fileMap_2925_);
lean_inc_ref(v_fileName_2924_);
v___x_2941_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2941_, 0, v_fileName_2924_);
lean_ctor_set(v___x_2941_, 1, v_fileMap_2925_);
lean_ctor_set(v___x_2941_, 2, v_options_2926_);
lean_ctor_set(v___x_2941_, 3, v_currRecDepth_2927_);
lean_ctor_set(v___x_2941_, 4, v_maxRecDepth_2928_);
lean_ctor_set(v___x_2941_, 5, v_ref_2940_);
lean_ctor_set(v___x_2941_, 6, v_currNamespace_2930_);
lean_ctor_set(v___x_2941_, 7, v_openDecls_2931_);
lean_ctor_set(v___x_2941_, 8, v_initHeartbeats_2932_);
lean_ctor_set(v___x_2941_, 9, v_maxHeartbeats_2933_);
lean_ctor_set(v___x_2941_, 10, v_quotContext_2934_);
lean_ctor_set(v___x_2941_, 11, v_currMacroScope_2935_);
lean_ctor_set(v___x_2941_, 12, v_cancelTk_x3f_2937_);
lean_ctor_set(v___x_2941_, 13, v_inheritedTraceOptions_2939_);
lean_ctor_set_uint8(v___x_2941_, sizeof(void*)*14, v_diag_2936_);
lean_ctor_set_uint8(v___x_2941_, sizeof(void*)*14 + 1, v_suppressElabErrors_2938_);
v___x_2942_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2915_, v___y_2919_, v___y_2920_, v___x_2941_, v___y_2922_);
lean_dec_ref_known(v___x_2941_, 14);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2943_, lean_object* v_msg_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_2943_, v_msg_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v_ref_2943_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2954_, lean_object* v_declHint_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; lean_object* v_env_2959_; uint8_t v___x_2960_; 
v___x_2958_ = lean_st_ref_get(v___y_2956_);
v_env_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc_ref(v_env_2959_);
lean_dec(v___x_2958_);
v___x_2960_ = l_Lean_Name_isAnonymous(v_declHint_2955_);
if (v___x_2960_ == 0)
{
uint8_t v_isExporting_2961_; 
v_isExporting_2961_ = lean_ctor_get_uint8(v_env_2959_, sizeof(void*)*8);
if (v_isExporting_2961_ == 0)
{
lean_object* v___x_2962_; 
lean_dec_ref(v_env_2959_);
lean_dec(v_declHint_2955_);
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v_msg_2954_);
return v___x_2962_;
}
else
{
lean_object* v___x_2963_; uint8_t v___x_2964_; 
lean_inc_ref(v_env_2959_);
v___x_2963_ = l_Lean_Environment_setExporting(v_env_2959_, v___x_2960_);
lean_inc(v_declHint_2955_);
lean_inc_ref(v___x_2963_);
v___x_2964_ = l_Lean_Environment_contains(v___x_2963_, v_declHint_2955_, v_isExporting_2961_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; 
lean_dec_ref(v___x_2963_);
lean_dec_ref(v_env_2959_);
lean_dec(v_declHint_2955_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_msg_2954_);
return v___x_2965_;
}
else
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v_c_2973_; lean_object* v___x_2974_; 
v___x_2966_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2967_ = lean_unsigned_to_nat(32u);
v___x_2968_ = lean_mk_empty_array_with_capacity(v___x_2967_);
lean_dec_ref(v___x_2968_);
v___x_2969_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2970_ = l_Lean_Options_empty;
v___x_2971_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2963_);
lean_ctor_set(v___x_2971_, 1, v___x_2966_);
lean_ctor_set(v___x_2971_, 2, v___x_2969_);
lean_ctor_set(v___x_2971_, 3, v___x_2970_);
lean_inc(v_declHint_2955_);
v___x_2972_ = l_Lean_MessageData_ofConstName(v_declHint_2955_, v___x_2960_);
v_c_2973_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2973_, 0, v___x_2971_);
lean_ctor_set(v_c_2973_, 1, v___x_2972_);
v___x_2974_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2959_, v_declHint_2955_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_dec_ref(v_env_2959_);
lean_dec(v_declHint_2955_);
v___x_2975_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v_c_2973_);
v___x_2977_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2976_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = l_Lean_MessageData_note(v___x_2978_);
v___x_2980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2980_, 0, v_msg_2954_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
return v___x_2981_;
}
else
{
lean_object* v_val_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3017_; 
v_val_2982_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_2984_ = v___x_2974_;
v_isShared_2985_ = v_isSharedCheck_3017_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_val_2982_);
lean_dec(v___x_2974_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3017_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v_mod_2989_; uint8_t v___x_2990_; 
v___x_2986_ = lean_box(0);
v___x_2987_ = l_Lean_Environment_header(v_env_2959_);
lean_dec_ref(v_env_2959_);
v___x_2988_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2987_);
v_mod_2989_ = lean_array_get(v___x_2986_, v___x_2988_, v_val_2982_);
lean_dec(v_val_2982_);
lean_dec_ref(v___x_2988_);
v___x_2990_ = l_Lean_isPrivateName(v_declHint_2955_);
lean_dec(v_declHint_2955_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3002_; 
v___x_2991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
lean_ctor_set(v___x_2992_, 1, v_c_2973_);
v___x_2993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2992_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = l_Lean_MessageData_ofName(v_mod_2989_);
v___x_2996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2994_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
v___x_2997_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2996_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = l_Lean_MessageData_note(v___x_2998_);
v___x_3000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3000_, 0, v_msg_2954_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set_tag(v___x_2984_, 0);
lean_ctor_set(v___x_2984_, 0, v___x_3000_);
v___x_3002_ = v___x_2984_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_3005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
lean_ctor_set(v___x_3005_, 1, v_c_2973_);
v___x_3006_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_3007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = l_Lean_MessageData_ofName(v_mod_2989_);
v___x_3009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3007_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3009_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = l_Lean_MessageData_note(v___x_3011_);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v_msg_2954_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set_tag(v___x_2984_, 0);
lean_ctor_set(v___x_2984_, 0, v___x_3013_);
v___x_3015_ = v___x_2984_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3018_; 
lean_dec_ref(v_env_2959_);
lean_dec(v_declHint_2955_);
v___x_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3018_, 0, v_msg_2954_);
return v___x_3018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_3019_, lean_object* v_declHint_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3019_, v_declHint_3020_, v___y_3021_);
lean_dec(v___y_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(lean_object* v_msg_3024_, lean_object* v_declHint_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v___x_3034_; lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3044_; 
v___x_3034_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3024_, v_declHint_3025_, v___y_3032_);
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3037_ = v___x_3034_;
v_isShared_3038_ = v_isSharedCheck_3044_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3034_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3044_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3039_ = l_Lean_unknownIdentifierMessageTag;
v___x_3040_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v_a_3035_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 0, v___x_3040_);
v___x_3042_ = v___x_3037_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11___boxed(lean_object* v_msg_3045_, lean_object* v_declHint_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3045_, v_declHint_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object* v_ref_3056_, lean_object* v_msg_3057_, lean_object* v_declHint_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___x_3067_; lean_object* v_a_3068_; lean_object* v___x_3069_; 
v___x_3067_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3057_, v_declHint_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v___x_3067_);
v___x_3069_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3056_, v_a_3068_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_ref_3070_, lean_object* v_msg_3071_, lean_object* v_declHint_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3070_, v_msg_3071_, v_declHint_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec(v_ref_3070_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(lean_object* v_ref_3082_, lean_object* v_constName_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v___x_3092_; uint8_t v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3092_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3093_ = 0;
lean_inc(v_constName_3083_);
v___x_3094_ = l_Lean_MessageData_ofConstName(v_constName_3083_, v___x_3093_);
v___x_3095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3092_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
v___x_3096_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3082_, v___x_3097_, v_constName_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_ref_3099_, lean_object* v_constName_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3099_, v_constName_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec(v_ref_3099_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_ref_3119_; lean_object* v___x_3120_; 
v_ref_3119_ = lean_ctor_get(v___y_3116_, 5);
v___x_3120_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3119_, v_constName_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(lean_object* v_constName_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v_env_3141_; uint8_t v___x_3142_; lean_object* v___x_3143_; 
v___x_3140_ = lean_st_ref_get(v___y_3138_);
v_env_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc_ref(v_env_3141_);
lean_dec(v___x_3140_);
v___x_3142_ = 0;
lean_inc(v_constName_3131_);
v___x_3143_ = l_Lean_Environment_find_x3f(v_env_3141_, v_constName_3131_, v___x_3142_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
return v___x_3144_;
}
else
{
lean_object* v_val_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec(v_constName_3131_);
v_val_3145_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3143_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_val_3145_);
lean_dec(v___x_3143_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 0);
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_val_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0___boxed(lean_object* v_constName_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_constName_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
return v_res_3162_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_instMonadEIO(lean_box(0));
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(lean_object* v_msg_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v_toApplicative_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3243_; 
v___x_3177_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0);
v___x_3178_ = l_StateRefT_x27_instMonad___redArg(v___x_3177_);
v_toApplicative_3179_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v___x_3178_, 1);
lean_dec(v_unused_3244_);
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3243_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_toApplicative_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3243_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_toFunctor_3183_; lean_object* v_toSeq_3184_; lean_object* v_toSeqLeft_3185_; lean_object* v_toSeqRight_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3241_; 
v_toFunctor_3183_ = lean_ctor_get(v_toApplicative_3179_, 0);
v_toSeq_3184_ = lean_ctor_get(v_toApplicative_3179_, 2);
v_toSeqLeft_3185_ = lean_ctor_get(v_toApplicative_3179_, 3);
v_toSeqRight_3186_ = lean_ctor_get(v_toApplicative_3179_, 4);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_toApplicative_3179_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; 
v_unused_3242_ = lean_ctor_get(v_toApplicative_3179_, 1);
lean_dec(v_unused_3242_);
v___x_3188_ = v_toApplicative_3179_;
v_isShared_3189_ = v_isSharedCheck_3241_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_toSeqRight_3186_);
lean_inc(v_toSeqLeft_3185_);
lean_inc(v_toSeq_3184_);
lean_inc(v_toFunctor_3183_);
lean_dec(v_toApplicative_3179_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3241_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___f_3190_; lean_object* v___f_3191_; lean_object* v___f_3192_; lean_object* v___f_3193_; lean_object* v___x_3194_; lean_object* v___f_3195_; lean_object* v___f_3196_; lean_object* v___f_3197_; lean_object* v___x_3199_; 
v___f_3190_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__1));
v___f_3191_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3183_);
v___f_3192_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3192_, 0, v_toFunctor_3183_);
v___f_3193_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3193_, 0, v_toFunctor_3183_);
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___f_3192_);
lean_ctor_set(v___x_3194_, 1, v___f_3193_);
v___f_3195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3195_, 0, v_toSeqRight_3186_);
v___f_3196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3196_, 0, v_toSeqLeft_3185_);
v___f_3197_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3197_, 0, v_toSeq_3184_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 4, v___f_3195_);
lean_ctor_set(v___x_3188_, 3, v___f_3196_);
lean_ctor_set(v___x_3188_, 2, v___f_3197_);
lean_ctor_set(v___x_3188_, 1, v___f_3190_);
lean_ctor_set(v___x_3188_, 0, v___x_3194_);
v___x_3199_ = v___x_3188_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v___f_3190_);
lean_ctor_set(v_reuseFailAlloc_3240_, 2, v___f_3197_);
lean_ctor_set(v_reuseFailAlloc_3240_, 3, v___f_3196_);
lean_ctor_set(v_reuseFailAlloc_3240_, 4, v___f_3195_);
v___x_3199_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3201_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 1, v___f_3191_);
lean_ctor_set(v___x_3181_, 0, v___x_3199_);
v___x_3201_ = v___x_3181_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v___f_3191_);
v___x_3201_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3202_; lean_object* v_toApplicative_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3237_; 
v___x_3202_ = l_StateRefT_x27_instMonad___redArg(v___x_3201_);
v_toApplicative_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3237_ == 0)
{
lean_object* v_unused_3238_; 
v_unused_3238_ = lean_ctor_get(v___x_3202_, 1);
lean_dec(v_unused_3238_);
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3237_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_toApplicative_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3237_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v_toFunctor_3207_; lean_object* v_toSeq_3208_; lean_object* v_toSeqLeft_3209_; lean_object* v_toSeqRight_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3235_; 
v_toFunctor_3207_ = lean_ctor_get(v_toApplicative_3203_, 0);
v_toSeq_3208_ = lean_ctor_get(v_toApplicative_3203_, 2);
v_toSeqLeft_3209_ = lean_ctor_get(v_toApplicative_3203_, 3);
v_toSeqRight_3210_ = lean_ctor_get(v_toApplicative_3203_, 4);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_toApplicative_3203_);
if (v_isSharedCheck_3235_ == 0)
{
lean_object* v_unused_3236_; 
v_unused_3236_ = lean_ctor_get(v_toApplicative_3203_, 1);
lean_dec(v_unused_3236_);
v___x_3212_ = v_toApplicative_3203_;
v_isShared_3213_ = v_isSharedCheck_3235_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_toSeqRight_3210_);
lean_inc(v_toSeqLeft_3209_);
lean_inc(v_toSeq_3208_);
lean_inc(v_toFunctor_3207_);
lean_dec(v_toApplicative_3203_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3235_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___f_3214_; lean_object* v___f_3215_; lean_object* v___f_3216_; lean_object* v___f_3217_; lean_object* v___x_3218_; lean_object* v___f_3219_; lean_object* v___f_3220_; lean_object* v___f_3221_; lean_object* v___x_3223_; 
v___f_3214_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__3));
v___f_3215_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3207_);
v___f_3216_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3216_, 0, v_toFunctor_3207_);
v___f_3217_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3217_, 0, v_toFunctor_3207_);
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___f_3216_);
lean_ctor_set(v___x_3218_, 1, v___f_3217_);
v___f_3219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3219_, 0, v_toSeqRight_3210_);
v___f_3220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3220_, 0, v_toSeqLeft_3209_);
v___f_3221_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3221_, 0, v_toSeq_3208_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 4, v___f_3219_);
lean_ctor_set(v___x_3212_, 3, v___f_3220_);
lean_ctor_set(v___x_3212_, 2, v___f_3221_);
lean_ctor_set(v___x_3212_, 1, v___f_3214_);
lean_ctor_set(v___x_3212_, 0, v___x_3218_);
v___x_3223_ = v___x_3212_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3218_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v___f_3214_);
lean_ctor_set(v_reuseFailAlloc_3234_, 2, v___f_3221_);
lean_ctor_set(v_reuseFailAlloc_3234_, 3, v___f_3220_);
lean_ctor_set(v_reuseFailAlloc_3234_, 4, v___f_3219_);
v___x_3223_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3225_; 
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 1, v___f_3215_);
lean_ctor_set(v___x_3205_, 0, v___x_3223_);
v___x_3225_ = v___x_3205_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v___f_3215_);
v___x_3225_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_43632__overap_3231_; lean_object* v___x_3232_; 
v___x_3226_ = l_StateRefT_x27_instMonad___redArg(v___x_3225_);
v___x_3227_ = l_ReaderT_instMonad___redArg(v___x_3226_);
v___x_3228_ = l_ReaderT_instMonad___redArg(v___x_3227_);
v___x_3229_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3230_ = l_instInhabitedOfMonad___redArg(v___x_3228_, v___x_3229_);
v___x_43632__overap_3231_ = lean_panic_fn_borrowed(v___x_3230_, v_msg_3168_);
lean_dec(v___x_3230_);
lean_inc(v___y_3175_);
lean_inc_ref(v___y_3174_);
lean_inc(v___y_3173_);
lean_inc_ref(v___y_3172_);
lean_inc(v___y_3171_);
lean_inc_ref(v___y_3170_);
lean_inc(v___y_3169_);
v___x_3232_ = lean_apply_8(v___x_43632__overap_3231_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, lean_box(0));
return v___x_3232_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___boxed(lean_object* v_msg_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v_msg_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
return v_res_3254_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__2));
v___x_3259_ = lean_unsigned_to_nat(53u);
v___x_3260_ = lean_unsigned_to_nat(62u);
v___x_3261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__1));
v___x_3262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__0));
v___x_3263_ = l_mkPanicMessageWithDecl(v___x_3262_, v___x_3261_, v___x_3260_, v___x_3259_, v___x_3258_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(size_t v_sz_3264_, size_t v_i_3265_, lean_object* v_bs_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
uint8_t v___x_3275_; 
v___x_3275_ = lean_usize_dec_lt(v_i_3265_, v_sz_3264_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v_bs_3266_);
return v___x_3276_;
}
else
{
lean_object* v_v_3277_; lean_object* v___x_3278_; 
v_v_3277_ = lean_array_uget_borrowed(v_bs_3266_, v_i_3265_);
lean_inc(v_v_3277_);
v___x_3278_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_v_3277_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3280_; lean_object* v_bs_x27_3281_; lean_object* v_a_3283_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3278_, 1);
v___x_3280_ = lean_unsigned_to_nat(0u);
v_bs_x27_3281_ = lean_array_uset(v_bs_3266_, v_i_3265_, v___x_3280_);
if (lean_obj_tag(v_a_3279_) == 6)
{
lean_object* v_val_3288_; lean_object* v_numFields_3289_; uint8_t v___x_3290_; lean_object* v___x_3291_; 
v_val_3288_ = lean_ctor_get(v_a_3279_, 0);
lean_inc_ref(v_val_3288_);
lean_dec_ref_known(v_a_3279_, 1);
v_numFields_3289_ = lean_ctor_get(v_val_3288_, 4);
lean_inc(v_numFields_3289_);
lean_dec_ref(v_val_3288_);
v___x_3290_ = 0;
v___x_3291_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3291_, 0, v_numFields_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3280_);
lean_ctor_set_uint8(v___x_3291_, sizeof(void*)*2, v___x_3290_);
v_a_3283_ = v___x_3291_;
goto v___jp_3282_;
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_dec(v_a_3279_);
v___x_3292_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3);
v___x_3293_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v___x_3292_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3293_, 1);
v_a_3283_ = v_a_3294_;
goto v___jp_3282_;
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec_ref(v_bs_x27_3281_);
v_a_3295_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3293_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3293_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
v___jp_3282_:
{
size_t v___x_3284_; size_t v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = ((size_t)1ULL);
v___x_3285_ = lean_usize_add(v_i_3265_, v___x_3284_);
v___x_3286_ = lean_array_uset(v_bs_x27_3281_, v_i_3265_, v_a_3283_);
v_i_3265_ = v___x_3285_;
v_bs_3266_ = v___x_3286_;
goto _start;
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec_ref(v_bs_3266_);
v_a_3303_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3278_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3278_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___boxed(lean_object* v_sz_3311_, lean_object* v_i_3312_, lean_object* v_bs_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
size_t v_sz_boxed_3322_; size_t v_i_boxed_3323_; lean_object* v_res_3324_; 
v_sz_boxed_3322_ = lean_unbox_usize(v_sz_3311_);
lean_dec(v_sz_3311_);
v_i_boxed_3323_ = lean_unbox_usize(v_i_3312_);
lean_dec(v_i_3312_);
v_res_3324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_boxed_3322_, v_i_boxed_3323_, v_bs_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
return v_res_3324_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3325_ = lean_box(0);
v___x_3326_ = lean_unsigned_to_nat(16u);
v___x_3327_ = lean_mk_array(v___x_3326_, v___x_3325_);
return v___x_3327_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3328_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0);
v___x_3329_ = lean_unsigned_to_nat(0u);
v___x_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
lean_ctor_set(v___x_3330_, 1, v___x_3328_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(lean_object* v_e_3333_, uint8_t v_alsoCasesOn_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
uint8_t v___x_3346_; 
v___x_3346_ = l_Lean_Expr_isApp(v_e_3333_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec_ref(v_e_3333_);
v___x_3347_ = lean_box(0);
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
return v___x_3348_;
}
else
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_Expr_getAppFn(v_e_3333_);
if (lean_obj_tag(v___x_3349_) == 4)
{
lean_object* v_declName_3350_; lean_object* v_us_3351_; lean_object* v___x_3352_; lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3507_; 
v_declName_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc_n(v_declName_3350_, 2);
v_us_3351_ = lean_ctor_get(v___x_3349_, 1);
lean_inc(v_us_3351_);
lean_dec_ref_known(v___x_3349_, 2);
v___x_3352_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3350_, v___y_3341_);
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3507_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3507_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
if (lean_obj_tag(v_a_3353_) == 1)
{
lean_object* v_val_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3399_; 
v_val_3357_ = lean_ctor_get(v_a_3353_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v_a_3353_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3359_ = v_a_3353_;
v_isShared_3360_ = v_isSharedCheck_3399_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_val_3357_);
lean_dec(v_a_3353_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3399_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_dummy_3361_; lean_object* v_nargs_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v_args_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v_dummy_3361_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_3362_ = l_Lean_Expr_getAppNumArgs(v_e_3333_);
lean_inc(v_nargs_3362_);
v___x_3363_ = lean_mk_array(v_nargs_3362_, v_dummy_3361_);
v___x_3364_ = lean_unsigned_to_nat(1u);
v___x_3365_ = lean_nat_sub(v_nargs_3362_, v___x_3364_);
lean_dec(v_nargs_3362_);
v_args_3366_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3333_, v___x_3363_, v___x_3365_);
v___x_3367_ = lean_array_get_size(v_args_3366_);
v___x_3368_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_3357_);
v___x_3369_ = lean_nat_dec_lt(v___x_3367_, v___x_3368_);
lean_dec(v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v_numParams_3370_; lean_object* v_numDiscrs_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3390_; 
v_numParams_3370_ = lean_ctor_get(v_val_3357_, 0);
v_numDiscrs_3371_ = lean_ctor_get(v_val_3357_, 1);
v___x_3372_ = lean_array_mk(v_us_3351_);
v___x_3373_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3370_);
v___x_3374_ = l_Array_extract___redArg(v_args_3366_, v___x_3373_, v_numParams_3370_);
v___x_3375_ = l_Lean_instInhabitedExpr;
v___x_3376_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3357_);
v___x_3377_ = lean_array_get(v___x_3375_, v_args_3366_, v___x_3376_);
lean_dec(v___x_3376_);
v___x_3378_ = lean_nat_add(v_numParams_3370_, v___x_3364_);
v___x_3379_ = lean_nat_add(v___x_3378_, v_numDiscrs_3371_);
lean_inc(v___x_3379_);
lean_inc_ref_n(v_args_3366_, 2);
v___x_3380_ = l_Array_toSubarray___redArg(v_args_3366_, v___x_3378_, v___x_3379_);
v___x_3381_ = l_Subarray_copy___redArg(v___x_3380_);
v___x_3382_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3357_);
v___x_3383_ = lean_nat_add(v___x_3379_, v___x_3382_);
lean_dec(v___x_3382_);
lean_inc(v___x_3383_);
v___x_3384_ = l_Array_toSubarray___redArg(v_args_3366_, v___x_3379_, v___x_3383_);
v___x_3385_ = l_Subarray_copy___redArg(v___x_3384_);
v___x_3386_ = l_Array_toSubarray___redArg(v_args_3366_, v___x_3383_, v___x_3367_);
v___x_3387_ = l_Subarray_copy___redArg(v___x_3386_);
v___x_3388_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3388_, 0, v_val_3357_);
lean_ctor_set(v___x_3388_, 1, v_declName_3350_);
lean_ctor_set(v___x_3388_, 2, v___x_3372_);
lean_ctor_set(v___x_3388_, 3, v___x_3374_);
lean_ctor_set(v___x_3388_, 4, v___x_3377_);
lean_ctor_set(v___x_3388_, 5, v___x_3381_);
lean_ctor_set(v___x_3388_, 6, v___x_3385_);
lean_ctor_set(v___x_3388_, 7, v___x_3387_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3388_);
v___x_3390_ = v___x_3359_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3392_; 
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3390_);
v___x_3392_ = v___x_3355_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3397_; 
lean_dec_ref(v_args_3366_);
lean_del_object(v___x_3359_);
lean_dec(v_val_3357_);
lean_dec(v_us_3351_);
lean_dec(v_declName_3350_);
v___x_3395_ = lean_box(0);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3395_);
v___x_3397_ = v___x_3355_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3395_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
else
{
lean_object* v___x_3400_; 
lean_del_object(v___x_3355_);
lean_dec(v_a_3353_);
v___x_3400_ = lean_st_ref_get(v___y_3341_);
if (v_alsoCasesOn_3334_ == 0)
{
lean_dec(v___x_3400_);
lean_dec(v_us_3351_);
lean_dec(v_declName_3350_);
lean_dec_ref(v_e_3333_);
goto v___jp_3343_;
}
else
{
lean_object* v_env_3401_; uint8_t v___x_3402_; 
v_env_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc_ref(v_env_3401_);
lean_dec(v___x_3400_);
lean_inc(v_declName_3350_);
v___x_3402_ = l_Lean_isCasesOnRecursor(v_env_3401_, v_declName_3350_);
if (v___x_3402_ == 0)
{
lean_dec(v_us_3351_);
lean_dec(v_declName_3350_);
lean_dec_ref(v_e_3333_);
goto v___jp_3343_;
}
else
{
lean_object* v_indName_3403_; lean_object* v___x_3404_; 
v_indName_3403_ = l_Lean_Name_getPrefix(v_declName_3350_);
v___x_3404_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_indName_3403_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3498_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3498_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3498_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
if (lean_obj_tag(v_a_3405_) == 5)
{
lean_object* v_val_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3493_; 
v_val_3409_ = lean_ctor_get(v_a_3405_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_a_3405_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3411_ = v_a_3405_;
v_isShared_3412_ = v_isSharedCheck_3493_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_val_3409_);
lean_dec(v_a_3405_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3493_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v_toConstantVal_3413_; lean_object* v_numParams_3414_; lean_object* v_numIndices_3415_; lean_object* v_ctors_3416_; lean_object* v_nargs_3417_; lean_object* v_dummy_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v_args_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v_toConstantVal_3413_ = lean_ctor_get(v_val_3409_, 0);
lean_inc_ref(v_toConstantVal_3413_);
v_numParams_3414_ = lean_ctor_get(v_val_3409_, 1);
lean_inc(v_numParams_3414_);
v_numIndices_3415_ = lean_ctor_get(v_val_3409_, 2);
lean_inc(v_numIndices_3415_);
v_ctors_3416_ = lean_ctor_get(v_val_3409_, 4);
lean_inc(v_ctors_3416_);
v_nargs_3417_ = l_Lean_Expr_getAppNumArgs(v_e_3333_);
v_dummy_3418_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_3417_);
v___x_3419_ = lean_mk_array(v_nargs_3417_, v_dummy_3418_);
v___x_3420_ = lean_unsigned_to_nat(1u);
v___x_3421_ = lean_nat_sub(v_nargs_3417_, v___x_3420_);
lean_dec(v_nargs_3417_);
v_args_3422_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3333_, v___x_3419_, v___x_3421_);
v___x_3423_ = lean_nat_add(v_numParams_3414_, v___x_3420_);
v___x_3424_ = lean_nat_add(v___x_3423_, v_numIndices_3415_);
v___x_3425_ = lean_nat_add(v___x_3424_, v___x_3420_);
lean_dec(v___x_3424_);
v___x_3426_ = l_Lean_InductiveVal_numCtors(v_val_3409_);
lean_dec_ref(v_val_3409_);
v___x_3427_ = lean_nat_add(v___x_3425_, v___x_3426_);
lean_dec(v___x_3426_);
v___x_3428_ = lean_array_get_size(v_args_3422_);
v___x_3429_ = lean_nat_dec_le(v___x_3427_, v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3432_; 
lean_dec(v___x_3427_);
lean_dec(v___x_3425_);
lean_dec(v___x_3423_);
lean_dec_ref(v_args_3422_);
lean_dec(v_ctors_3416_);
lean_dec(v_numIndices_3415_);
lean_dec(v_numParams_3414_);
lean_dec_ref(v_toConstantVal_3413_);
lean_del_object(v___x_3411_);
lean_dec(v_us_3351_);
lean_dec(v_declName_3350_);
v___x_3430_ = lean_box(0);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3430_);
v___x_3432_ = v___x_3407_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3430_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
else
{
lean_object* v___x_3434_; lean_object* v_params_3435_; lean_object* v___x_3436_; lean_object* v_motive_3437_; lean_object* v_discrs_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v_discrInfos_3441_; lean_object* v_alts_3442_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v_lower_3484_; lean_object* v_upper_3485_; uint8_t v___x_3492_; 
lean_del_object(v___x_3407_);
v___x_3434_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3414_);
lean_inc_ref_n(v_args_3422_, 3);
v_params_3435_ = l_Array_toSubarray___redArg(v_args_3422_, v___x_3434_, v_numParams_3414_);
v___x_3436_ = l_Lean_instInhabitedExpr;
v_motive_3437_ = lean_array_get(v___x_3436_, v_args_3422_, v_numParams_3414_);
lean_dec(v_numParams_3414_);
lean_inc(v___x_3425_);
v_discrs_3438_ = l_Array_toSubarray___redArg(v_args_3422_, v___x_3423_, v___x_3425_);
v___x_3439_ = lean_nat_add(v_numIndices_3415_, v___x_3420_);
lean_dec(v_numIndices_3415_);
v___x_3440_ = lean_box(0);
v_discrInfos_3441_ = lean_mk_array(v___x_3439_, v___x_3440_);
lean_inc(v___x_3427_);
v_alts_3442_ = l_Array_toSubarray___redArg(v_args_3422_, v___x_3425_, v___x_3427_);
v___x_3492_ = lean_nat_dec_le(v___x_3427_, v___x_3434_);
if (v___x_3492_ == 0)
{
v_lower_3484_ = v___x_3427_;
v_upper_3485_ = v___x_3428_;
goto v___jp_3483_;
}
else
{
lean_dec(v___x_3427_);
v_lower_3484_ = v___x_3434_;
v_upper_3485_ = v___x_3428_;
goto v___jp_3483_;
}
v___jp_3443_:
{
lean_object* v___x_3446_; size_t v_sz_3447_; size_t v___x_3448_; lean_object* v___x_3449_; 
v___x_3446_ = lean_array_mk(v_ctors_3416_);
v_sz_3447_ = lean_array_size(v___x_3446_);
v___x_3448_ = ((size_t)0ULL);
v___x_3449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_3447_, v___x_3448_, v___x_3446_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3474_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3474_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3474_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_start_3454_; lean_object* v_stop_3455_; lean_object* v_start_3456_; lean_object* v_stop_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3469_; 
v_start_3454_ = lean_ctor_get(v_params_3435_, 1);
lean_inc(v_start_3454_);
v_stop_3455_ = lean_ctor_get(v_params_3435_, 2);
lean_inc(v_stop_3455_);
v_start_3456_ = lean_ctor_get(v_discrs_3438_, 1);
lean_inc(v_start_3456_);
v_stop_3457_ = lean_ctor_get(v_discrs_3438_, 2);
lean_inc(v_stop_3457_);
v___x_3458_ = lean_nat_sub(v_stop_3455_, v_start_3454_);
lean_dec(v_start_3454_);
lean_dec(v_stop_3455_);
v___x_3459_ = lean_nat_sub(v_stop_3457_, v_start_3456_);
lean_dec(v_start_3456_);
lean_dec(v_stop_3457_);
v___x_3460_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1);
v___x_3461_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3458_);
lean_ctor_set(v___x_3461_, 1, v___x_3459_);
lean_ctor_set(v___x_3461_, 2, v_a_3450_);
lean_ctor_set(v___x_3461_, 3, v___y_3445_);
lean_ctor_set(v___x_3461_, 4, v_discrInfos_3441_);
lean_ctor_set(v___x_3461_, 5, v___x_3460_);
v___x_3462_ = lean_array_mk(v_us_3351_);
v___x_3463_ = l_Subarray_copy___redArg(v_params_3435_);
v___x_3464_ = l_Subarray_copy___redArg(v_discrs_3438_);
v___x_3465_ = l_Subarray_copy___redArg(v_alts_3442_);
v___x_3466_ = l_Subarray_copy___redArg(v___y_3444_);
v___x_3467_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3461_);
lean_ctor_set(v___x_3467_, 1, v_declName_3350_);
lean_ctor_set(v___x_3467_, 2, v___x_3462_);
lean_ctor_set(v___x_3467_, 3, v___x_3463_);
lean_ctor_set(v___x_3467_, 4, v_motive_3437_);
lean_ctor_set(v___x_3467_, 5, v___x_3464_);
lean_ctor_set(v___x_3467_, 6, v___x_3465_);
lean_ctor_set(v___x_3467_, 7, v___x_3466_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 1);
lean_ctor_set(v___x_3411_, 0, v___x_3467_);
v___x_3469_ = v___x_3411_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3471_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3469_);
v___x_3471_ = v___x_3452_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec_ref(v_alts_3442_);
lean_dec_ref(v_discrInfos_3441_);
lean_dec_ref(v_discrs_3438_);
lean_dec(v_motive_3437_);
lean_dec_ref(v_params_3435_);
lean_del_object(v___x_3411_);
lean_dec(v_us_3351_);
lean_dec(v_declName_3350_);
v_a_3475_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3449_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3449_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
v___jp_3483_:
{
lean_object* v_levelParams_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
v_levelParams_3486_ = lean_ctor_get(v_toConstantVal_3413_, 1);
lean_inc(v_levelParams_3486_);
lean_dec_ref(v_toConstantVal_3413_);
v___x_3487_ = l_Array_toSubarray___redArg(v_args_3422_, v_lower_3484_, v_upper_3485_);
v___x_3488_ = l_List_lengthTR___redArg(v_levelParams_3486_);
lean_dec(v_levelParams_3486_);
v___x_3489_ = l_List_lengthTR___redArg(v_us_3351_);
v___x_3490_ = lean_nat_dec_eq(v___x_3488_, v___x_3489_);
lean_dec(v___x_3489_);
lean_dec(v___x_3488_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; 
v___x_3491_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__2));
v___y_3444_ = v___x_3487_;
v___y_3445_ = v___x_3491_;
goto v___jp_3443_;
}
else
{
v___y_3444_ = v___x_3487_;
v___y_3445_ = v___x_3440_;
goto v___jp_3443_;
}
}
}
}
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3496_; 
lean_dec(v_a_3405_);
lean_dec(v_us_3351_);
lean_dec(v_declName_3350_);
lean_dec_ref(v_e_3333_);
v___x_3494_ = lean_box(0);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3494_);
v___x_3496_ = v___x_3407_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3494_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v_us_3351_);
lean_dec(v_declName_3350_);
lean_dec_ref(v_e_3333_);
v_a_3499_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3404_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3404_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
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
lean_dec_ref(v___x_3349_);
lean_dec_ref(v_e_3333_);
goto v___jp_3343_;
}
}
v___jp_3343_:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
return v___x_3345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___boxed(lean_object* v_e_3508_, lean_object* v_alsoCasesOn_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
uint8_t v_alsoCasesOn_boxed_3518_; lean_object* v_res_3519_; 
v_alsoCasesOn_boxed_3518_ = lean_unbox(v_alsoCasesOn_3509_);
v_res_3519_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3508_, v_alsoCasesOn_boxed_3518_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
return v_res_3519_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__1));
v___x_3524_ = l_Lean_stringToMessageData(v___x_3523_);
return v___x_3524_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = lean_unsigned_to_nat(1u);
v___x_3526_ = l_Lean_Expr_bvar___override(v___x_3525_);
return v___x_3526_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3529_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__5));
v___x_3530_ = lean_unsigned_to_nat(2u);
v___x_3531_ = lean_unsigned_to_nat(182u);
v___x_3532_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__4));
v___x_3533_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_3534_ = l_mkPanicMessageWithDecl(v___x_3533_, v___x_3532_, v___x_3531_, v___x_3530_, v___x_3529_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(lean_object* v_e_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v_e_3544_; uint8_t v___x_3545_; lean_object* v___x_3546_; 
v_e_3544_ = l_Lean_Expr_headBeta(v_e_3535_);
v___x_3545_ = 1;
v___x_3546_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3544_, v___x_3545_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3780_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3549_ = v___x_3546_;
v_isShared_3550_ = v_isSharedCheck_3780_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3780_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
if (lean_obj_tag(v_a_3547_) == 1)
{
lean_object* v_val_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3775_; 
v_val_3551_ = lean_ctor_get(v_a_3547_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_a_3547_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3553_ = v_a_3547_;
v_isShared_3554_ = v_isSharedCheck_3775_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_val_3551_);
lean_dec(v_a_3547_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3775_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v_toMatcherInfo_3555_; lean_object* v_matcherName_3556_; lean_object* v_params_3557_; lean_object* v_motive_3558_; lean_object* v_discrs_3559_; lean_object* v_alts_3560_; lean_object* v_remaining_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v_toMatcherInfo_3555_ = lean_ctor_get(v_val_3551_, 0);
lean_inc_ref(v_toMatcherInfo_3555_);
v_matcherName_3556_ = lean_ctor_get(v_val_3551_, 1);
lean_inc(v_matcherName_3556_);
v_params_3557_ = lean_ctor_get(v_val_3551_, 3);
lean_inc_ref(v_params_3557_);
v_motive_3558_ = lean_ctor_get(v_val_3551_, 4);
lean_inc_ref(v_motive_3558_);
v_discrs_3559_ = lean_ctor_get(v_val_3551_, 5);
lean_inc_ref(v_discrs_3559_);
v_alts_3560_ = lean_ctor_get(v_val_3551_, 6);
lean_inc_ref(v_alts_3560_);
v_remaining_3561_ = lean_ctor_get(v_val_3551_, 7);
lean_inc_ref(v_remaining_3561_);
v___x_3562_ = lean_unsigned_to_nat(0u);
v___x_3563_ = lean_array_get_size(v_remaining_3561_);
v___x_3564_ = lean_nat_dec_lt(v___x_3562_, v___x_3563_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3565_; lean_object* v___x_3567_; 
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
lean_dec(v_val_3551_);
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3565_);
v___x_3567_ = v___x_3549_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
else
{
lean_object* v___x_3569_; uint8_t v___x_3570_; 
v___x_3569_ = lean_array_fget_borrowed(v_remaining_3561_, v___x_3562_);
v___x_3570_ = l_Lean_Expr_isLambda(v___x_3569_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; lean_object* v___x_3573_; 
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
lean_dec(v_val_3551_);
v___x_3571_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3571_);
v___x_3573_ = v___x_3549_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
else
{
lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3575_ = l_Lean_Expr_bindingBody_x21(v___x_3569_);
v___x_3576_ = l_Lean_Expr_isLambda(v___x_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
lean_dec_ref(v___x_3575_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
lean_dec(v_val_3551_);
v___x_3577_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3577_);
v___x_3579_ = v___x_3549_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
else
{
lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3581_ = l_Lean_Expr_bindingBody_x21(v___x_3575_);
lean_dec_ref(v___x_3575_);
v___x_3582_ = l_Lean_Expr_isApp(v___x_3581_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
lean_dec_ref(v___x_3581_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
lean_dec(v_val_3551_);
v___x_3583_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3583_);
v___x_3585_ = v___x_3549_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
else
{
uint8_t v___x_3587_; 
v___x_3587_ = lean_expr_has_loose_bvar(v___x_3581_, v___x_3562_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v_a_3591_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v___x_3588_ = l_Lean_Expr_appArg_x21(v___x_3581_);
v___x_3589_ = lean_unsigned_to_nat(1u);
v___x_3645_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3);
v___x_3646_ = lean_expr_eqv(v___x_3588_, v___x_3645_);
lean_dec_ref(v___x_3588_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3649_; 
lean_dec_ref(v___x_3581_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
lean_dec(v_val_3551_);
v___x_3647_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3647_);
v___x_3649_ = v___x_3549_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
else
{
lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___x_3651_ = l_Lean_Expr_appFn_x21(v___x_3581_);
lean_dec_ref(v___x_3581_);
v___x_3652_ = lean_expr_has_loose_bvar(v___x_3651_, v___x_3589_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; 
lean_del_object(v___x_3549_);
lean_inc(v_a_3542_);
lean_inc_ref(v_a_3541_);
lean_inc(v_a_3540_);
lean_inc_ref(v_a_3539_);
lean_inc_ref(v___x_3651_);
v___x_3653_ = lean_infer_type(v___x_3651_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v_keyedConfig_3655_; uint8_t v_trackZetaDelta_3656_; lean_object* v_zetaDeltaSet_3657_; lean_object* v_lctx_3658_; lean_object* v_localInstances_3659_; lean_object* v_defEqCtx_x3f_3660_; lean_object* v_synthPendingDepth_3661_; lean_object* v_customCanUnfoldPredicate_x3f_3662_; uint8_t v_univApprox_3663_; uint8_t v_inTypeClassResolution_3664_; uint8_t v_cacheInferType_3665_; uint8_t v___x_3666_; lean_object* v_a_3668_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3653_, 1);
v_keyedConfig_3655_ = lean_ctor_get(v_a_3539_, 0);
v_trackZetaDelta_3656_ = lean_ctor_get_uint8(v_a_3539_, sizeof(void*)*7);
v_zetaDeltaSet_3657_ = lean_ctor_get(v_a_3539_, 1);
v_lctx_3658_ = lean_ctor_get(v_a_3539_, 2);
v_localInstances_3659_ = lean_ctor_get(v_a_3539_, 3);
v_defEqCtx_x3f_3660_ = lean_ctor_get(v_a_3539_, 4);
v_synthPendingDepth_3661_ = lean_ctor_get(v_a_3539_, 5);
v_customCanUnfoldPredicate_x3f_3662_ = lean_ctor_get(v_a_3539_, 6);
v_univApprox_3663_ = lean_ctor_get_uint8(v_a_3539_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3664_ = lean_ctor_get_uint8(v_a_3539_, sizeof(void*)*7 + 2);
v_cacheInferType_3665_ = lean_ctor_get_uint8(v_a_3539_, sizeof(void*)*7 + 3);
v___x_3666_ = 0;
lean_inc_ref(v_keyedConfig_3655_);
v___x_3746_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3666_, v_keyedConfig_3655_);
lean_inc(v_customCanUnfoldPredicate_x3f_3662_);
lean_inc(v_synthPendingDepth_3661_);
lean_inc(v_defEqCtx_x3f_3660_);
lean_inc_ref(v_localInstances_3659_);
lean_inc_ref(v_lctx_3658_);
lean_inc(v_zetaDeltaSet_3657_);
v___x_3747_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
lean_ctor_set(v___x_3747_, 1, v_zetaDeltaSet_3657_);
lean_ctor_set(v___x_3747_, 2, v_lctx_3658_);
lean_ctor_set(v___x_3747_, 3, v_localInstances_3659_);
lean_ctor_set(v___x_3747_, 4, v_defEqCtx_x3f_3660_);
lean_ctor_set(v___x_3747_, 5, v_synthPendingDepth_3661_);
lean_ctor_set(v___x_3747_, 6, v_customCanUnfoldPredicate_x3f_3662_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*7, v_trackZetaDelta_3656_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*7 + 1, v_univApprox_3663_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3664_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*7 + 3, v_cacheInferType_3665_);
v___x_3748_ = l_Lean_Meta_whnfForall(v_a_3654_, v___x_3747_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec_ref_known(v___x_3747_, 7);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3748_, 1);
v_a_3668_ = v_a_3749_;
goto v___jp_3667_;
}
else
{
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3750_; 
v_a_3750_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3750_);
lean_dec_ref_known(v___x_3748_, 1);
v_a_3668_ = v_a_3750_;
goto v___jp_3667_;
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_dec_ref(v___x_3651_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
lean_dec(v_val_3551_);
v_a_3751_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3748_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3748_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
v___jp_3667_:
{
uint8_t v___x_3669_; 
v___x_3669_ = l_Lean_Expr_isForall(v_a_3668_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_dec_ref(v_a_3668_);
lean_dec_ref(v___x_3651_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
lean_dec(v_val_3551_);
v___x_3670_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6);
v___x_3671_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v___x_3670_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
return v___x_3671_;
}
else
{
lean_object* v___x_3672_; 
v___x_3672_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_val_3551_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3737_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3675_ = v___x_3672_;
v_isShared_3676_ = v_isSharedCheck_3737_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3737_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
if (lean_obj_tag(v_a_3673_) == 1)
{
lean_object* v_val_3677_; uint8_t v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___f_3682_; lean_object* v___x_3683_; 
lean_del_object(v___x_3675_);
v_val_3677_ = lean_ctor_get(v_a_3673_, 0);
lean_inc(v_val_3677_);
lean_dec_ref_known(v_a_3673_, 1);
v___x_3678_ = 0;
v___x_3679_ = lean_box(v___x_3678_);
v___x_3680_ = lean_box(v___x_3652_);
v___x_3681_ = lean_box(v___x_3545_);
v___f_3682_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3682_, 0, v___x_3679_);
lean_closure_set(v___f_3682_, 1, v___x_3680_);
lean_closure_set(v___f_3682_, 2, v___x_3681_);
v___x_3683_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_motive_3558_, v___f_3682_, v___x_3652_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3685_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3683_, 1);
v___x_3685_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_3556_, v_toMatcherInfo_3555_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; size_t v_sz_3701_; size_t v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3685_, 1);
v___x_3687_ = l_Lean_Expr_bindingDomain_x21(v_a_3668_);
v___x_3688_ = l_Lean_Expr_bindingName_x21(v_a_3668_);
v___x_3689_ = l_Lean_Expr_bindingBody_x21(v_a_3668_);
lean_dec_ref(v_a_3668_);
lean_inc_ref(v___x_3687_);
v___x_3690_ = l_Lean_Expr_lam___override(v___x_3688_, v___x_3687_, v___x_3689_, v___x_3678_);
v___x_3691_ = lean_unsigned_to_nat(5u);
v___x_3692_ = lean_mk_empty_array_with_capacity(v___x_3691_);
v___x_3693_ = lean_array_push(v___x_3692_, v_val_3677_);
v___x_3694_ = lean_array_push(v___x_3693_, v___x_3687_);
v___x_3695_ = lean_array_push(v___x_3694_, v___x_3690_);
v___x_3696_ = lean_array_push(v___x_3695_, v___x_3651_);
v___x_3697_ = lean_array_push(v___x_3696_, v_a_3684_);
v___x_3698_ = l_Array_append___redArg(v_params_3557_, v___x_3697_);
lean_dec_ref(v___x_3697_);
v___x_3699_ = l_Array_append___redArg(v___x_3698_, v_discrs_3559_);
lean_dec_ref(v_discrs_3559_);
v___x_3700_ = l_Array_append___redArg(v___x_3699_, v_alts_3560_);
lean_dec_ref(v_alts_3560_);
v_sz_3701_ = lean_array_size(v___x_3700_);
v___x_3702_ = ((size_t)0ULL);
v___x_3703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_3701_, v___x_3702_, v___x_3700_);
lean_inc_ref(v_keyedConfig_3655_);
v___x_3704_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3666_, v_keyedConfig_3655_);
lean_inc(v_customCanUnfoldPredicate_x3f_3662_);
lean_inc(v_synthPendingDepth_3661_);
lean_inc(v_defEqCtx_x3f_3660_);
lean_inc_ref(v_localInstances_3659_);
lean_inc_ref(v_lctx_3658_);
lean_inc(v_zetaDeltaSet_3657_);
v___x_3705_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
lean_ctor_set(v___x_3705_, 1, v_zetaDeltaSet_3657_);
lean_ctor_set(v___x_3705_, 2, v_lctx_3658_);
lean_ctor_set(v___x_3705_, 3, v_localInstances_3659_);
lean_ctor_set(v___x_3705_, 4, v_defEqCtx_x3f_3660_);
lean_ctor_set(v___x_3705_, 5, v_synthPendingDepth_3661_);
lean_ctor_set(v___x_3705_, 6, v_customCanUnfoldPredicate_x3f_3662_);
lean_ctor_set_uint8(v___x_3705_, sizeof(void*)*7, v_trackZetaDelta_3656_);
lean_ctor_set_uint8(v___x_3705_, sizeof(void*)*7 + 1, v_univApprox_3663_);
lean_ctor_set_uint8(v___x_3705_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3664_);
lean_ctor_set_uint8(v___x_3705_, sizeof(void*)*7 + 3, v_cacheInferType_3665_);
v___x_3706_ = l_Lean_Meta_mkAppOptM(v_a_3686_, v___x_3703_, v___x_3705_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec_ref_known(v___x_3705_, 7);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
v_a_3591_ = v_a_3707_;
goto v___jp_3590_;
}
else
{
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3708_; 
v_a_3708_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3706_, 1);
v_a_3591_ = v_a_3708_;
goto v___jp_3590_;
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec_ref(v_remaining_3561_);
lean_del_object(v___x_3553_);
v_a_3709_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3706_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3706_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
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
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec(v_a_3684_);
lean_dec(v_val_3677_);
lean_dec_ref(v_a_3668_);
lean_dec_ref(v___x_3651_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_params_3557_);
lean_del_object(v___x_3553_);
v_a_3717_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3685_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3685_);
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
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec(v_val_3677_);
lean_dec_ref(v_a_3668_);
lean_dec_ref(v___x_3651_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
v_a_3725_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3683_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3683_);
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
else
{
lean_object* v___x_3733_; lean_object* v___x_3735_; 
lean_dec(v_a_3673_);
lean_dec_ref(v_a_3668_);
lean_dec_ref(v___x_3651_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
v___x_3733_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3733_);
v___x_3735_ = v___x_3675_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3733_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec_ref(v_a_3668_);
lean_dec_ref(v___x_3651_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
v_a_3738_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3672_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3672_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec_ref(v___x_3651_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
lean_dec(v_val_3551_);
v_a_3759_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3653_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3653_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
lean_dec_ref(v___x_3651_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
lean_dec(v_val_3551_);
v___x_3767_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3767_);
v___x_3769_ = v___x_3549_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
v___jp_3590_:
{
lean_object* v___x_3592_; 
lean_inc(v_a_3542_);
lean_inc_ref(v_a_3541_);
lean_inc(v_a_3540_);
lean_inc_ref(v_a_3539_);
lean_inc_ref(v_a_3591_);
v___x_3592_ = lean_infer_type(v_a_3591_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref_known(v___x_3592_, 1);
v___x_3594_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_3595_ = lean_unsigned_to_nat(3u);
v___x_3596_ = l_Lean_Expr_isAppOfArity(v_a_3593_, v___x_3594_, v___x_3595_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; 
lean_dec(v_a_3593_);
lean_dec_ref(v_remaining_3561_);
lean_del_object(v___x_3553_);
lean_inc(v_a_3542_);
lean_inc_ref(v_a_3541_);
lean_inc(v_a_3540_);
lean_inc_ref(v_a_3539_);
v___x_3597_ = lean_infer_type(v_a_3591_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3597_, 1);
v___x_3599_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2);
v___x_3600_ = l_Lean_indentExpr(v_a_3598_);
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3599_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v___x_3601_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
return v___x_3602_;
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
v_a_3603_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3597_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3597_);
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
else
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = l_Lean_Expr_appArg_x21(v_a_3593_);
lean_dec(v_a_3593_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v_a_3591_);
v___x_3613_ = v___x_3553_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3591_);
v___x_3613_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3614_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3614_, 0, v___x_3611_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
lean_ctor_set_uint8(v___x_3614_, sizeof(void*)*2, v___x_3545_);
v___x_3615_ = l_Array_toSubarray___redArg(v_remaining_3561_, v___x_3589_, v___x_3563_);
v___x_3616_ = l_Subarray_copy___redArg(v___x_3615_);
v___x_3617_ = l_Lean_Meta_Simp_Result_addExtraArgs(v___x_3614_, v___x_3616_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec_ref(v___x_3616_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3627_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3620_ = v___x_3617_;
v_isShared_3621_ = v_isSharedCheck_3627_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3617_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3627_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3625_; 
v___x_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3622_, 0, v_a_3618_);
v___x_3623_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 0, v___x_3623_);
v___x_3625_ = v___x_3620_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
v_a_3628_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3617_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3617_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec_ref(v_a_3591_);
lean_dec_ref(v_remaining_3561_);
lean_del_object(v___x_3553_);
v_a_3637_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3592_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3592_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
}
else
{
lean_object* v___x_3771_; lean_object* v___x_3773_; 
lean_dec_ref(v___x_3581_);
lean_dec_ref(v_remaining_3561_);
lean_dec_ref(v_alts_3560_);
lean_dec_ref(v_discrs_3559_);
lean_dec_ref(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_dec(v_matcherName_3556_);
lean_dec_ref(v_toMatcherInfo_3555_);
lean_del_object(v___x_3553_);
lean_dec(v_val_3551_);
v___x_3771_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3771_);
v___x_3773_ = v___x_3549_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
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
lean_object* v___x_3776_; lean_object* v___x_3778_; 
lean_dec(v_a_3547_);
v___x_3776_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3776_);
v___x_3778_ = v___x_3549_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
v_a_3781_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3546_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3546_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed(lean_object* v_e_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(v_e_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
lean_dec(v_a_3796_);
lean_dec_ref(v_a_3795_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
lean_dec(v_a_3790_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(lean_object* v_declName_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3799_, v___y_3806_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___boxed(lean_object* v_declName_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(v_declName_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(lean_object* v_00_u03b1_3819_, lean_object* v_msg_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_3820_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___boxed(lean_object* v_00_u03b1_3830_, lean_object* v_msg_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(v_00_u03b1_3830_, v_msg_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3841_, lean_object* v_constName_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3852_, lean_object* v_constName_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(v_00_u03b1_3852_, v_constName_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b1_3863_, lean_object* v_ref_3864_, lean_object* v_constName_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3864_, v_constName_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b1_3875_, lean_object* v_ref_3876_, lean_object* v_constName_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(v_00_u03b1_3875_, v_ref_3876_, v_constName_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec(v_ref_3876_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3887_, lean_object* v_ref_3888_, lean_object* v_msg_3889_, lean_object* v_declHint_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3888_, v_msg_3889_, v_declHint_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3900_, lean_object* v_ref_3901_, lean_object* v_msg_3902_, lean_object* v_declHint_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_3900_, v_ref_3901_, v_msg_3902_, v_declHint_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec(v_ref_3901_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_3913_, lean_object* v_declHint_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3913_, v_declHint_3914_, v___y_3921_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_3924_, lean_object* v_declHint_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(v_msg_3924_, v_declHint_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(lean_object* v_00_u03b1_3935_, lean_object* v_ref_3936_, lean_object* v_msg_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3936_, v_msg_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___boxed(lean_object* v_00_u03b1_3947_, lean_object* v_ref_3948_, lean_object* v_msg_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(v_00_u03b1_3947_, v_ref_3948_, v_msg_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec(v_ref_3948_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4004_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4005_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4006_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed), 9, 0);
v___x_4007_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4004_, v___x_4005_, v___x_4006_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10____boxed(lean_object* v_a_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_();
return v_res_4009_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2(void){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4019_ = lean_box(0);
v___x_4020_ = lean_unsigned_to_nat(16u);
v___x_4021_ = lean_mk_array(v___x_4020_, v___x_4019_);
return v___x_4021_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3(void){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4022_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2);
v___x_4023_ = lean_unsigned_to_nat(0u);
v___x_4024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
lean_ctor_set(v___x_4024_, 1, v___x_4022_);
return v___x_4024_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4(void){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4025_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5(void){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4026_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4);
v___x_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
return v___x_4027_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6(void){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; uint8_t v___x_4030_; lean_object* v___x_4031_; 
v___x_4028_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4029_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3);
v___x_4030_ = 1;
v___x_4031_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4031_, 0, v___x_4029_);
lean_ctor_set(v___x_4031_, 1, v___x_4028_);
lean_ctor_set_uint8(v___x_4031_, sizeof(void*)*2, v___x_4030_);
return v___x_4031_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7(void){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4032_ = lean_unsigned_to_nat(0u);
v___x_4033_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
lean_ctor_set(v___x_4034_, 1, v___x_4032_);
return v___x_4034_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8(void){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4035_ = lean_unsigned_to_nat(32u);
v___x_4036_ = lean_mk_empty_array_with_capacity(v___x_4035_);
v___x_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4036_);
return v___x_4037_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9(void){
_start:
{
size_t v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4038_ = ((size_t)5ULL);
v___x_4039_ = lean_unsigned_to_nat(0u);
v___x_4040_ = lean_unsigned_to_nat(32u);
v___x_4041_ = lean_mk_empty_array_with_capacity(v___x_4040_);
v___x_4042_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8);
v___x_4043_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
lean_ctor_set(v___x_4043_, 1, v___x_4041_);
lean_ctor_set(v___x_4043_, 2, v___x_4039_);
lean_ctor_set(v___x_4043_, 3, v___x_4039_);
lean_ctor_set_usize(v___x_4043_, 4, v___x_4038_);
return v___x_4043_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10(void){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4044_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9);
v___x_4045_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4046_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
lean_ctor_set(v___x_4046_, 1, v___x_4045_);
lean_ctor_set(v___x_4046_, 2, v___x_4045_);
lean_ctor_set(v___x_4046_, 3, v___x_4044_);
return v___x_4046_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11(void){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4047_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10);
v___x_4048_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7);
v___x_4049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
lean_ctor_set(v___x_4049_, 1, v___x_4047_);
return v___x_4049_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13(void){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4051_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12));
v___x_4052_ = l_Lean_stringToMessageData(v___x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object* v_declName_4053_, lean_object* v_mvarId_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
uint8_t v___x_4060_; uint8_t v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v_keyedConfig_4064_; uint8_t v_trackZetaDelta_4065_; lean_object* v_zetaDeltaSet_4066_; lean_object* v_lctx_4067_; lean_object* v_localInstances_4068_; lean_object* v_defEqCtx_x3f_4069_; lean_object* v_synthPendingDepth_4070_; lean_object* v_customCanUnfoldPredicate_x3f_4071_; uint8_t v_univApprox_4072_; uint8_t v_inTypeClassResolution_4073_; uint8_t v_cacheInferType_4074_; lean_object* v___x_4075_; uint8_t v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4060_ = 0;
v___x_4061_ = 1;
v___x_4062_ = lean_box(0);
v___x_4063_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0));
v_keyedConfig_4064_ = lean_ctor_get(v_a_4055_, 0);
v_trackZetaDelta_4065_ = lean_ctor_get_uint8(v_a_4055_, sizeof(void*)*7);
v_zetaDeltaSet_4066_ = lean_ctor_get(v_a_4055_, 1);
v_lctx_4067_ = lean_ctor_get(v_a_4055_, 2);
v_localInstances_4068_ = lean_ctor_get(v_a_4055_, 3);
v_defEqCtx_x3f_4069_ = lean_ctor_get(v_a_4055_, 4);
v_synthPendingDepth_4070_ = lean_ctor_get(v_a_4055_, 5);
v_customCanUnfoldPredicate_x3f_4071_ = lean_ctor_get(v_a_4055_, 6);
v_univApprox_4072_ = lean_ctor_get_uint8(v_a_4055_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4073_ = lean_ctor_get_uint8(v_a_4055_, sizeof(void*)*7 + 2);
v_cacheInferType_4074_ = lean_ctor_get_uint8(v_a_4055_, sizeof(void*)*7 + 3);
v___x_4075_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1));
v___x_4076_ = 0;
v___x_4077_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6);
v___x_4078_ = l_Lean_Options_empty;
lean_inc_ref(v_keyedConfig_4064_);
v___x_4079_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4076_, v_keyedConfig_4064_);
lean_inc(v_customCanUnfoldPredicate_x3f_4071_);
lean_inc(v_synthPendingDepth_4070_);
lean_inc(v_defEqCtx_x3f_4069_);
lean_inc_ref(v_localInstances_4068_);
lean_inc_ref(v_lctx_4067_);
lean_inc(v_zetaDeltaSet_4066_);
v___x_4080_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set(v___x_4080_, 1, v_zetaDeltaSet_4066_);
lean_ctor_set(v___x_4080_, 2, v_lctx_4067_);
lean_ctor_set(v___x_4080_, 3, v_localInstances_4068_);
lean_ctor_set(v___x_4080_, 4, v_defEqCtx_x3f_4069_);
lean_ctor_set(v___x_4080_, 5, v_synthPendingDepth_4070_);
lean_ctor_set(v___x_4080_, 6, v_customCanUnfoldPredicate_x3f_4071_);
lean_ctor_set_uint8(v___x_4080_, sizeof(void*)*7, v_trackZetaDelta_4065_);
lean_ctor_set_uint8(v___x_4080_, sizeof(void*)*7 + 1, v_univApprox_4072_);
lean_ctor_set_uint8(v___x_4080_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4073_);
lean_ctor_set_uint8(v___x_4080_, sizeof(void*)*7 + 3, v_cacheInferType_4074_);
v___x_4081_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_4063_, v___x_4075_, v___x_4077_, v___x_4078_, v___x_4080_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v___x_4081_, 1);
v___x_4083_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4084_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_4075_, v___x_4083_, v___x_4060_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v___x_4084_, 1);
v___x_4086_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11);
v___x_4087_ = l_Lean_Meta_simpTarget(v_mvarId_4054_, v_a_4082_, v_a_4085_, v___x_4062_, v___x_4061_, v___x_4086_, v___x_4080_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4130_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4130_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4130_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v_fst_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4128_; 
v_fst_4092_ = lean_ctor_get(v_a_4088_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_a_4088_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; 
v_unused_4129_ = lean_ctor_get(v_a_4088_, 1);
lean_dec(v_unused_4129_);
v___x_4094_ = v_a_4088_;
v_isShared_4095_ = v_isSharedCheck_4128_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_fst_4092_);
lean_dec(v_a_4088_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4128_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
if (lean_obj_tag(v_fst_4092_) == 0)
{
lean_object* v___x_4096_; lean_object* v___x_4098_; 
lean_del_object(v___x_4094_);
lean_dec_ref_known(v___x_4080_, 7);
lean_dec(v_declName_4053_);
v___x_4096_ = lean_box(0);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4096_);
v___x_4098_ = v___x_4090_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4096_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
else
{
lean_object* v_val_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4104_; 
lean_del_object(v___x_4090_);
v_val_4100_ = lean_ctor_get(v_fst_4092_, 0);
lean_inc(v_val_4100_);
lean_dec_ref_known(v_fst_4092_, 1);
v___x_4101_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13);
v___x_4102_ = l_Lean_MessageData_ofConstName(v_declName_4053_, v___x_4060_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set_tag(v___x_4094_, 7);
lean_ctor_set(v___x_4094_, 1, v___x_4102_);
lean_ctor_set(v___x_4094_, 0, v___x_4101_);
v___x_4104_ = v___x_4094_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4101_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4102_);
v___x_4104_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___f_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4105_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_4106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4104_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v___f_4107_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4107_, 0, v___x_4106_);
v___x_4108_ = lean_box(v___x_4061_);
v___x_4109_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___boxed), 7, 2);
lean_closure_set(v___x_4109_, 0, v_val_4100_);
lean_closure_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4109_, v___f_4107_, v___x_4080_, v_a_4056_, v_a_4057_, v_a_4058_);
lean_dec_ref_known(v___x_4080_, 7);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4110_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4110_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
v_a_4119_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4110_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4110_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
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
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
lean_dec_ref_known(v___x_4080_, 7);
lean_dec(v_declName_4053_);
v_a_4131_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4087_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4087_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
else
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
lean_dec(v_a_4082_);
lean_dec_ref_known(v___x_4080_, 7);
lean_dec(v_mvarId_4054_);
lean_dec(v_declName_4053_);
v_a_4139_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4084_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4084_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec_ref_known(v___x_4080_, 7);
lean_dec(v_mvarId_4054_);
lean_dec(v_declName_4053_);
v_a_4147_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4081_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4081_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___boxed(lean_object* v_declName_4155_, lean_object* v_mvarId_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4155_, v_mvarId_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(lean_object* v_e_4163_, lean_object* v_k_4164_, uint8_t v_cleanupAnnotations_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v___f_4171_; uint8_t v___x_4172_; uint8_t v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___f_4171_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4171_, 0, v_k_4164_);
v___x_4172_ = 1;
v___x_4173_ = 0;
v___x_4174_ = lean_box(0);
v___x_4175_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4163_, v___x_4172_, v___x_4173_, v___x_4172_, v___x_4173_, v___x_4174_, v___f_4171_, v_cleanupAnnotations_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4175_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
v_a_4184_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4175_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4175_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg___boxed(lean_object* v_e_4192_, lean_object* v_k_4193_, lean_object* v_cleanupAnnotations_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4200_; lean_object* v_res_4201_; 
v_cleanupAnnotations_boxed_4200_ = lean_unbox(v_cleanupAnnotations_4194_);
v_res_4201_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4192_, v_k_4193_, v_cleanupAnnotations_boxed_4200_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_object* v_00_u03b1_4202_, lean_object* v_e_4203_, lean_object* v_k_4204_, uint8_t v_cleanupAnnotations_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4203_, v_k_4204_, v_cleanupAnnotations_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed(lean_object* v_00_u03b1_4212_, lean_object* v_e_4213_, lean_object* v_k_4214_, lean_object* v_cleanupAnnotations_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4221_; lean_object* v_res_4222_; 
v_cleanupAnnotations_boxed_4221_ = lean_unbox(v_cleanupAnnotations_4215_);
v_res_4222_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(v_00_u03b1_4212_, v_e_4213_, v_k_4214_, v_cleanupAnnotations_boxed_4221_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
return v_res_4222_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object* v_opts_4223_, lean_object* v_opt_4224_){
_start:
{
lean_object* v_name_4225_; lean_object* v_defValue_4226_; lean_object* v_map_4227_; lean_object* v___x_4228_; 
v_name_4225_ = lean_ctor_get(v_opt_4224_, 0);
v_defValue_4226_ = lean_ctor_get(v_opt_4224_, 1);
v_map_4227_ = lean_ctor_get(v_opts_4223_, 0);
v___x_4228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4227_, v_name_4225_);
if (lean_obj_tag(v___x_4228_) == 0)
{
uint8_t v___x_4229_; 
v___x_4229_ = lean_unbox(v_defValue_4226_);
return v___x_4229_;
}
else
{
lean_object* v_val_4230_; 
v_val_4230_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_val_4230_);
lean_dec_ref_known(v___x_4228_, 1);
if (lean_obj_tag(v_val_4230_) == 1)
{
uint8_t v_v_4231_; 
v_v_4231_ = lean_ctor_get_uint8(v_val_4230_, 0);
lean_dec_ref_known(v_val_4230_, 0);
return v_v_4231_;
}
else
{
uint8_t v___x_4232_; 
lean_dec(v_val_4230_);
v___x_4232_ = lean_unbox(v_defValue_4226_);
return v___x_4232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object* v_opts_4233_, lean_object* v_opt_4234_){
_start:
{
uint8_t v_res_4235_; lean_object* v_r_4236_; 
v_res_4235_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v_opts_4233_, v_opt_4234_);
lean_dec_ref(v_opt_4234_);
lean_dec_ref(v_opts_4233_);
v_r_4236_ = lean_box(v_res_4235_);
return v_r_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(lean_object* v_opts_4237_, lean_object* v_opt_4238_){
_start:
{
lean_object* v_name_4239_; lean_object* v_defValue_4240_; lean_object* v_map_4241_; lean_object* v___x_4242_; 
v_name_4239_ = lean_ctor_get(v_opt_4238_, 0);
v_defValue_4240_ = lean_ctor_get(v_opt_4238_, 1);
v_map_4241_ = lean_ctor_get(v_opts_4237_, 0);
v___x_4242_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4241_, v_name_4239_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_inc(v_defValue_4240_);
return v_defValue_4240_;
}
else
{
lean_object* v_val_4243_; 
v_val_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_val_4243_);
lean_dec_ref_known(v___x_4242_, 1);
if (lean_obj_tag(v_val_4243_) == 3)
{
lean_object* v_v_4244_; 
v_v_4244_ = lean_ctor_get(v_val_4243_, 0);
lean_inc(v_v_4244_);
lean_dec_ref_known(v_val_4243_, 1);
return v_v_4244_;
}
else
{
lean_dec(v_val_4243_);
lean_inc(v_defValue_4240_);
return v_defValue_4240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4___boxed(lean_object* v_opts_4245_, lean_object* v_opt_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_opts_4245_, v_opt_4246_);
lean_dec_ref(v_opt_4246_);
lean_dec_ref(v_opts_4245_);
return v_res_4247_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4248_; double v___x_4249_; 
v___x_4248_ = lean_unsigned_to_nat(0u);
v___x_4249_ = lean_float_of_nat(v___x_4248_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(lean_object* v_cls_4253_, lean_object* v_msg_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v_ref_4260_; lean_object* v___x_4261_; lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4306_; 
v_ref_4260_ = lean_ctor_get(v___y_4257_, 5);
v___x_4261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4264_ = v___x_4261_;
v_isShared_4265_ = v_isSharedCheck_4306_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4261_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4306_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4266_; lean_object* v_traceState_4267_; lean_object* v_env_4268_; lean_object* v_nextMacroScope_4269_; lean_object* v_ngen_4270_; lean_object* v_auxDeclNGen_4271_; lean_object* v_cache_4272_; lean_object* v_messages_4273_; lean_object* v_infoState_4274_; lean_object* v_snapshotTasks_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4305_; 
v___x_4266_ = lean_st_ref_take(v___y_4258_);
v_traceState_4267_ = lean_ctor_get(v___x_4266_, 4);
v_env_4268_ = lean_ctor_get(v___x_4266_, 0);
v_nextMacroScope_4269_ = lean_ctor_get(v___x_4266_, 1);
v_ngen_4270_ = lean_ctor_get(v___x_4266_, 2);
v_auxDeclNGen_4271_ = lean_ctor_get(v___x_4266_, 3);
v_cache_4272_ = lean_ctor_get(v___x_4266_, 5);
v_messages_4273_ = lean_ctor_get(v___x_4266_, 6);
v_infoState_4274_ = lean_ctor_get(v___x_4266_, 7);
v_snapshotTasks_4275_ = lean_ctor_get(v___x_4266_, 8);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4277_ = v___x_4266_;
v_isShared_4278_ = v_isSharedCheck_4305_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_snapshotTasks_4275_);
lean_inc(v_infoState_4274_);
lean_inc(v_messages_4273_);
lean_inc(v_cache_4272_);
lean_inc(v_traceState_4267_);
lean_inc(v_auxDeclNGen_4271_);
lean_inc(v_ngen_4270_);
lean_inc(v_nextMacroScope_4269_);
lean_inc(v_env_4268_);
lean_dec(v___x_4266_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4305_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
uint64_t v_tid_4279_; lean_object* v_traces_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4304_; 
v_tid_4279_ = lean_ctor_get_uint64(v_traceState_4267_, sizeof(void*)*1);
v_traces_4280_ = lean_ctor_get(v_traceState_4267_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v_traceState_4267_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4282_ = v_traceState_4267_;
v_isShared_4283_ = v_isSharedCheck_4304_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_traces_4280_);
lean_dec(v_traceState_4267_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4304_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4284_; double v___x_4285_; uint8_t v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4294_; 
v___x_4284_ = lean_box(0);
v___x_4285_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0);
v___x_4286_ = 0;
v___x_4287_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__1));
v___x_4288_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4288_, 0, v_cls_4253_);
lean_ctor_set(v___x_4288_, 1, v___x_4284_);
lean_ctor_set(v___x_4288_, 2, v___x_4287_);
lean_ctor_set_float(v___x_4288_, sizeof(void*)*3, v___x_4285_);
lean_ctor_set_float(v___x_4288_, sizeof(void*)*3 + 8, v___x_4285_);
lean_ctor_set_uint8(v___x_4288_, sizeof(void*)*3 + 16, v___x_4286_);
v___x_4289_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__2));
v___x_4290_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4288_);
lean_ctor_set(v___x_4290_, 1, v_a_4262_);
lean_ctor_set(v___x_4290_, 2, v___x_4289_);
lean_inc(v_ref_4260_);
v___x_4291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4291_, 0, v_ref_4260_);
lean_ctor_set(v___x_4291_, 1, v___x_4290_);
v___x_4292_ = l_Lean_PersistentArray_push___redArg(v_traces_4280_, v___x_4291_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 0, v___x_4292_);
v___x_4294_ = v___x_4282_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v___x_4292_);
lean_ctor_set_uint64(v_reuseFailAlloc_4303_, sizeof(void*)*1, v_tid_4279_);
v___x_4294_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
lean_object* v___x_4296_; 
if (v_isShared_4278_ == 0)
{
lean_ctor_set(v___x_4277_, 4, v___x_4294_);
v___x_4296_ = v___x_4277_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_env_4268_);
lean_ctor_set(v_reuseFailAlloc_4302_, 1, v_nextMacroScope_4269_);
lean_ctor_set(v_reuseFailAlloc_4302_, 2, v_ngen_4270_);
lean_ctor_set(v_reuseFailAlloc_4302_, 3, v_auxDeclNGen_4271_);
lean_ctor_set(v_reuseFailAlloc_4302_, 4, v___x_4294_);
lean_ctor_set(v_reuseFailAlloc_4302_, 5, v_cache_4272_);
lean_ctor_set(v_reuseFailAlloc_4302_, 6, v_messages_4273_);
lean_ctor_set(v_reuseFailAlloc_4302_, 7, v_infoState_4274_);
lean_ctor_set(v_reuseFailAlloc_4302_, 8, v_snapshotTasks_4275_);
v___x_4296_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4300_; 
v___x_4297_ = lean_st_ref_put(v___y_4258_, v___x_4296_);
v___x_4298_ = lean_box(0);
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 0, v___x_4298_);
v___x_4300_ = v___x_4264_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v___x_4298_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___boxed(lean_object* v_cls_4307_, lean_object* v_msg_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v_cls_4307_, v_msg_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
return v_res_4314_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4324_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4325_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4326_ = l_Lean_Name_append(v___x_4325_, v___x_4324_);
return v___x_4326_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4328_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__6));
v___x_4329_ = l_Lean_stringToMessageData(v___x_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object* v_levelParams_4330_, lean_object* v_declName_4331_, lean_object* v_wfPreprocessProof_4332_, lean_object* v___x_4333_, lean_object* v_unaryPreDefName_4334_, lean_object* v_xs_4335_, lean_object* v_body_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4345_ = lean_box(0);
lean_inc(v_levelParams_4330_);
v___x_4346_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4330_, v___x_4345_);
lean_inc(v_declName_4331_);
v___x_4347_ = l_Lean_mkConst(v_declName_4331_, v___x_4346_);
v___x_4348_ = l_Lean_mkAppN(v___x_4347_, v_xs_4335_);
v___x_4349_ = l_Lean_Meta_mkEq(v___x_4348_, v_body_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc_n(v_a_4350_, 2);
lean_dec_ref_known(v___x_4349_, 1);
v___x_4351_ = lean_box(0);
v___x_4352_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4350_, v___x_4351_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4354_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
v___x_4354_ = l_Lean_Meta_Simp_Result_addExtraArgs(v_wfPreprocessProof_4332_, v_xs_4335_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; lean_object* v_mvarId_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4354_, 1);
v___x_4356_ = l_Lean_Expr_appFn_x21(v_a_4350_);
v___x_4357_ = lean_box(0);
v___x_4358_ = 1;
v___x_4432_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4432_, 0, v___x_4356_);
lean_ctor_set(v___x_4432_, 1, v___x_4357_);
lean_ctor_set_uint8(v___x_4432_, sizeof(void*)*2, v___x_4358_);
v___x_4433_ = l_Lean_Meta_Simp_mkCongr(v___x_4432_, v_a_4355_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4434_);
lean_dec_ref_known(v___x_4433_, 1);
v___x_4435_ = l_Lean_Expr_mvarId_x21(v_a_4353_);
v___x_4436_ = l_Lean_Meta_applySimpResultToTarget(v___x_4435_, v_a_4350_, v_a_4434_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v_a_4437_; uint8_t v___x_4438_; 
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
lean_inc(v_a_4437_);
lean_dec_ref_known(v___x_4436_, 1);
v___x_4438_ = lean_name_eq(v_declName_4331_, v_unaryPreDefName_4334_);
if (v___x_4438_ == 0)
{
lean_object* v___x_4439_; 
v___x_4439_ = l_Lean_Elab_Eqns_deltaLHS(v_a_4437_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v_a_4440_; 
v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc(v_a_4440_);
lean_dec_ref_known(v___x_4439_, 1);
v_mvarId_4360_ = v_a_4440_;
v___y_4361_ = v___y_4337_;
v___y_4362_ = v___y_4338_;
v___y_4363_ = v___y_4339_;
v___y_4364_ = v___y_4340_;
goto v___jp_4359_;
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec(v_a_4353_);
lean_dec(v_a_4350_);
lean_dec(v___x_4333_);
lean_dec(v_declName_4331_);
lean_dec(v_levelParams_4330_);
v_a_4441_ = lean_ctor_get(v___x_4439_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4439_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4439_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
else
{
v_mvarId_4360_ = v_a_4437_;
v___y_4361_ = v___y_4337_;
v___y_4362_ = v___y_4338_;
v___y_4363_ = v___y_4339_;
v___y_4364_ = v___y_4340_;
goto v___jp_4359_;
}
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_dec(v_a_4353_);
lean_dec(v_a_4350_);
lean_dec(v___x_4333_);
lean_dec(v_declName_4331_);
lean_dec(v_levelParams_4330_);
v_a_4449_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4436_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4436_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_dec(v_a_4353_);
lean_dec(v_a_4350_);
lean_dec(v___x_4333_);
lean_dec(v_declName_4331_);
lean_dec(v_levelParams_4330_);
v_a_4457_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4433_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4433_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
v___jp_4359_:
{
lean_object* v___x_4365_; 
v___x_4365_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4367_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_a_4366_);
lean_dec_ref_known(v___x_4365_, 1);
v___x_4367_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4331_, v_a_4366_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v___x_4368_; lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4423_; 
lean_dec_ref_known(v___x_4367_, 1);
v___x_4368_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4353_, v___y_4362_);
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4371_ = v___x_4368_;
v_isShared_4372_ = v_isSharedCheck_4423_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4368_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4423_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
uint8_t v___x_4373_; uint8_t v___x_4374_; lean_object* v___x_4375_; 
v___x_4373_ = 0;
v___x_4374_ = 1;
v___x_4375_ = l_Lean_Meta_mkForallFVars(v_xs_4335_, v_a_4350_, v___x_4373_, v___x_4358_, v___x_4358_, v___x_4374_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4377_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc(v_a_4376_);
lean_dec_ref_known(v___x_4375_, 1);
v___x_4377_ = l_Lean_Meta_letToHave(v_a_4376_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___x_4377_, 1);
v___x_4379_ = l_Lean_Meta_mkLambdaFVars(v_xs_4335_, v_a_4369_, v___x_4373_, v___x_4358_, v___x_4373_, v___x_4358_, v___x_4374_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4385_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v___x_4379_, 1);
lean_inc_n(v___x_4333_, 2);
v___x_4381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4333_);
lean_ctor_set(v___x_4381_, 1, v_levelParams_4330_);
lean_ctor_set(v___x_4381_, 2, v_a_4378_);
v___x_4382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4333_);
lean_ctor_set(v___x_4382_, 1, v___x_4345_);
v___x_4383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4381_);
lean_ctor_set(v___x_4383_, 1, v_a_4380_);
lean_ctor_set(v___x_4383_, 2, v___x_4382_);
if (v_isShared_4372_ == 0)
{
lean_ctor_set_tag(v___x_4371_, 2);
lean_ctor_set(v___x_4371_, 0, v___x_4383_);
v___x_4385_ = v___x_4371_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_Lean_addDecl(v___x_4385_, v___x_4373_, v___y_4363_, v___y_4364_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v___x_4387_; 
lean_dec_ref_known(v___x_4386_, 1);
lean_inc(v___x_4333_);
v___x_4387_ = l_Lean_inferDefEqAttr(v___x_4333_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_options_4388_; uint8_t v_hasTrace_4389_; 
lean_dec_ref_known(v___x_4387_, 1);
v_options_4388_ = lean_ctor_get(v___y_4363_, 2);
v_hasTrace_4389_ = lean_ctor_get_uint8(v_options_4388_, sizeof(void*)*1);
if (v_hasTrace_4389_ == 0)
{
lean_dec(v___x_4333_);
goto v___jp_4342_;
}
else
{
lean_object* v_inheritedTraceOptions_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v_inheritedTraceOptions_4390_ = lean_ctor_get(v___y_4363_, 13);
v___x_4391_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4392_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_4393_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4390_, v_options_4388_, v___x_4392_);
if (v___x_4393_ == 0)
{
lean_dec(v___x_4333_);
goto v___jp_4342_;
}
else
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4394_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7);
v___x_4395_ = l_Lean_MessageData_ofConstName(v___x_4333_, v___x_4373_);
v___x_4396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4394_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_4391_, v___x_4396_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
return v___x_4397_;
}
}
}
else
{
lean_dec(v___x_4333_);
return v___x_4387_;
}
}
else
{
lean_dec(v___x_4333_);
return v___x_4386_;
}
}
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
lean_dec(v_a_4378_);
lean_del_object(v___x_4371_);
lean_dec(v___x_4333_);
lean_dec(v_levelParams_4330_);
v_a_4399_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4379_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4379_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_del_object(v___x_4371_);
lean_dec(v_a_4369_);
lean_dec(v___x_4333_);
lean_dec(v_levelParams_4330_);
v_a_4407_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4377_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4377_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_del_object(v___x_4371_);
lean_dec(v_a_4369_);
lean_dec(v___x_4333_);
lean_dec(v_levelParams_4330_);
v_a_4415_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4375_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4375_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
else
{
lean_dec(v_a_4353_);
lean_dec(v_a_4350_);
lean_dec(v___x_4333_);
lean_dec(v_levelParams_4330_);
return v___x_4367_;
}
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v_a_4353_);
lean_dec(v_a_4350_);
lean_dec(v___x_4333_);
lean_dec(v_declName_4331_);
lean_dec(v_levelParams_4330_);
v_a_4424_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4365_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4365_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec(v_a_4353_);
lean_dec(v_a_4350_);
lean_dec(v___x_4333_);
lean_dec(v_declName_4331_);
lean_dec(v_levelParams_4330_);
v_a_4465_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4354_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4354_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_dec(v_a_4350_);
lean_dec(v___x_4333_);
lean_dec_ref(v_wfPreprocessProof_4332_);
lean_dec(v_declName_4331_);
lean_dec(v_levelParams_4330_);
v_a_4473_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4352_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4352_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_dec(v___x_4333_);
lean_dec_ref(v_wfPreprocessProof_4332_);
lean_dec(v_declName_4331_);
lean_dec(v_levelParams_4330_);
v_a_4481_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4349_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4349_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
v___jp_4342_:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4343_ = lean_box(0);
v___x_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4343_);
return v___x_4344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object* v_levelParams_4489_, lean_object* v_declName_4490_, lean_object* v_wfPreprocessProof_4491_, lean_object* v___x_4492_, lean_object* v_unaryPreDefName_4493_, lean_object* v_xs_4494_, lean_object* v_body_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l_Lean_Elab_WF_mkUnfoldEq___lam__0(v_levelParams_4489_, v_declName_4490_, v_wfPreprocessProof_4491_, v___x_4492_, v_unaryPreDefName_4493_, v_xs_4494_, v_body_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec_ref(v_xs_4494_);
lean_dec(v_unaryPreDefName_4493_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(lean_object* v___y_4502_, uint8_t v_isExporting_4503_, lean_object* v___x_4504_, lean_object* v___y_4505_, lean_object* v___x_4506_, lean_object* v_a_x3f_4507_){
_start:
{
lean_object* v___x_4509_; lean_object* v_env_4510_; lean_object* v_nextMacroScope_4511_; lean_object* v_ngen_4512_; lean_object* v_auxDeclNGen_4513_; lean_object* v_traceState_4514_; lean_object* v_messages_4515_; lean_object* v_infoState_4516_; lean_object* v_snapshotTasks_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4542_; 
v___x_4509_ = lean_st_ref_take(v___y_4502_);
v_env_4510_ = lean_ctor_get(v___x_4509_, 0);
v_nextMacroScope_4511_ = lean_ctor_get(v___x_4509_, 1);
v_ngen_4512_ = lean_ctor_get(v___x_4509_, 2);
v_auxDeclNGen_4513_ = lean_ctor_get(v___x_4509_, 3);
v_traceState_4514_ = lean_ctor_get(v___x_4509_, 4);
v_messages_4515_ = lean_ctor_get(v___x_4509_, 6);
v_infoState_4516_ = lean_ctor_get(v___x_4509_, 7);
v_snapshotTasks_4517_ = lean_ctor_get(v___x_4509_, 8);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4542_ == 0)
{
lean_object* v_unused_4543_; 
v_unused_4543_ = lean_ctor_get(v___x_4509_, 5);
lean_dec(v_unused_4543_);
v___x_4519_ = v___x_4509_;
v_isShared_4520_ = v_isSharedCheck_4542_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_snapshotTasks_4517_);
lean_inc(v_infoState_4516_);
lean_inc(v_messages_4515_);
lean_inc(v_traceState_4514_);
lean_inc(v_auxDeclNGen_4513_);
lean_inc(v_ngen_4512_);
lean_inc(v_nextMacroScope_4511_);
lean_inc(v_env_4510_);
lean_dec(v___x_4509_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4542_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4521_ = l_Lean_Environment_setExporting(v_env_4510_, v_isExporting_4503_);
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 5, v___x_4504_);
lean_ctor_set(v___x_4519_, 0, v___x_4521_);
v___x_4523_ = v___x_4519_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4521_);
lean_ctor_set(v_reuseFailAlloc_4541_, 1, v_nextMacroScope_4511_);
lean_ctor_set(v_reuseFailAlloc_4541_, 2, v_ngen_4512_);
lean_ctor_set(v_reuseFailAlloc_4541_, 3, v_auxDeclNGen_4513_);
lean_ctor_set(v_reuseFailAlloc_4541_, 4, v_traceState_4514_);
lean_ctor_set(v_reuseFailAlloc_4541_, 5, v___x_4504_);
lean_ctor_set(v_reuseFailAlloc_4541_, 6, v_messages_4515_);
lean_ctor_set(v_reuseFailAlloc_4541_, 7, v_infoState_4516_);
lean_ctor_set(v_reuseFailAlloc_4541_, 8, v_snapshotTasks_4517_);
v___x_4523_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v_mctx_4526_; lean_object* v_zetaDeltaFVarIds_4527_; lean_object* v_postponed_4528_; lean_object* v_diag_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4539_; 
v___x_4524_ = lean_st_ref_put(v___y_4502_, v___x_4523_);
v___x_4525_ = lean_st_ref_take(v___y_4505_);
v_mctx_4526_ = lean_ctor_get(v___x_4525_, 0);
v_zetaDeltaFVarIds_4527_ = lean_ctor_get(v___x_4525_, 2);
v_postponed_4528_ = lean_ctor_get(v___x_4525_, 3);
v_diag_4529_ = lean_ctor_get(v___x_4525_, 4);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4539_ == 0)
{
lean_object* v_unused_4540_; 
v_unused_4540_ = lean_ctor_get(v___x_4525_, 1);
lean_dec(v_unused_4540_);
v___x_4531_ = v___x_4525_;
v_isShared_4532_ = v_isSharedCheck_4539_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_diag_4529_);
lean_inc(v_postponed_4528_);
lean_inc(v_zetaDeltaFVarIds_4527_);
lean_inc(v_mctx_4526_);
lean_dec(v___x_4525_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4539_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
lean_ctor_set(v___x_4531_, 1, v___x_4506_);
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_mctx_4526_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4538_, 2, v_zetaDeltaFVarIds_4527_);
lean_ctor_set(v_reuseFailAlloc_4538_, 3, v_postponed_4528_);
lean_ctor_set(v_reuseFailAlloc_4538_, 4, v_diag_4529_);
v___x_4534_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = lean_st_ref_put(v___y_4505_, v___x_4534_);
v___x_4536_ = lean_box(0);
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
return v___x_4537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v___y_4544_, lean_object* v_isExporting_4545_, lean_object* v___x_4546_, lean_object* v___y_4547_, lean_object* v___x_4548_, lean_object* v_a_x3f_4549_, lean_object* v___y_4550_){
_start:
{
uint8_t v_isExporting_boxed_4551_; lean_object* v_res_4552_; 
v_isExporting_boxed_4551_ = lean_unbox(v_isExporting_4545_);
v_res_4552_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4544_, v_isExporting_boxed_4551_, v___x_4546_, v___y_4547_, v___x_4548_, v_a_x3f_4549_);
lean_dec(v_a_x3f_4549_);
lean_dec(v___y_4547_);
lean_dec(v___y_4544_);
return v_res_4552_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4553_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4554_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0);
v___x_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
return v___x_4555_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4556_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1);
v___x_4557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
lean_ctor_set(v___x_4557_, 1, v___x_4556_);
return v___x_4557_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4558_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1);
v___x_4559_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4558_);
lean_ctor_set(v___x_4559_, 1, v___x_4558_);
lean_ctor_set(v___x_4559_, 2, v___x_4558_);
lean_ctor_set(v___x_4559_, 3, v___x_4558_);
lean_ctor_set(v___x_4559_, 4, v___x_4558_);
lean_ctor_set(v___x_4559_, 5, v___x_4558_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(lean_object* v_x_4560_, uint8_t v_isExporting_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v___x_4567_; lean_object* v_env_4568_; uint8_t v_isExporting_4569_; lean_object* v___x_4635_; uint8_t v_isModule_4636_; 
v___x_4567_ = lean_st_ref_get(v___y_4565_);
v_env_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc_ref(v_env_4568_);
lean_dec(v___x_4567_);
v_isExporting_4569_ = lean_ctor_get_uint8(v_env_4568_, sizeof(void*)*8);
v___x_4635_ = l_Lean_Environment_header(v_env_4568_);
lean_dec_ref(v_env_4568_);
v_isModule_4636_ = lean_ctor_get_uint8(v___x_4635_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4635_);
if (v_isModule_4636_ == 0)
{
lean_object* v___x_4637_; 
lean_inc(v___y_4565_);
lean_inc_ref(v___y_4564_);
lean_inc(v___y_4563_);
lean_inc_ref(v___y_4562_);
v___x_4637_ = lean_apply_5(v_x_4560_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, lean_box(0));
return v___x_4637_;
}
else
{
if (v_isExporting_4569_ == 0)
{
if (v_isExporting_4561_ == 0)
{
lean_object* v___x_4638_; 
lean_inc(v___y_4565_);
lean_inc_ref(v___y_4564_);
lean_inc(v___y_4563_);
lean_inc_ref(v___y_4562_);
v___x_4638_ = lean_apply_5(v_x_4560_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, lean_box(0));
return v___x_4638_;
}
else
{
goto v___jp_4570_;
}
}
else
{
if (v_isExporting_4561_ == 0)
{
goto v___jp_4570_;
}
else
{
lean_object* v___x_4639_; 
lean_inc(v___y_4565_);
lean_inc_ref(v___y_4564_);
lean_inc(v___y_4563_);
lean_inc_ref(v___y_4562_);
v___x_4639_ = lean_apply_5(v_x_4560_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, lean_box(0));
return v___x_4639_;
}
}
}
v___jp_4570_:
{
lean_object* v___x_4571_; lean_object* v_env_4572_; lean_object* v_nextMacroScope_4573_; lean_object* v_ngen_4574_; lean_object* v_auxDeclNGen_4575_; lean_object* v_traceState_4576_; lean_object* v_messages_4577_; lean_object* v_infoState_4578_; lean_object* v_snapshotTasks_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4633_; 
v___x_4571_ = lean_st_ref_take(v___y_4565_);
v_env_4572_ = lean_ctor_get(v___x_4571_, 0);
v_nextMacroScope_4573_ = lean_ctor_get(v___x_4571_, 1);
v_ngen_4574_ = lean_ctor_get(v___x_4571_, 2);
v_auxDeclNGen_4575_ = lean_ctor_get(v___x_4571_, 3);
v_traceState_4576_ = lean_ctor_get(v___x_4571_, 4);
v_messages_4577_ = lean_ctor_get(v___x_4571_, 6);
v_infoState_4578_ = lean_ctor_get(v___x_4571_, 7);
v_snapshotTasks_4579_ = lean_ctor_get(v___x_4571_, 8);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4633_ == 0)
{
lean_object* v_unused_4634_; 
v_unused_4634_ = lean_ctor_get(v___x_4571_, 5);
lean_dec(v_unused_4634_);
v___x_4581_ = v___x_4571_;
v_isShared_4582_ = v_isSharedCheck_4633_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_snapshotTasks_4579_);
lean_inc(v_infoState_4578_);
lean_inc(v_messages_4577_);
lean_inc(v_traceState_4576_);
lean_inc(v_auxDeclNGen_4575_);
lean_inc(v_ngen_4574_);
lean_inc(v_nextMacroScope_4573_);
lean_inc(v_env_4572_);
lean_dec(v___x_4571_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4633_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4586_; 
v___x_4583_ = l_Lean_Environment_setExporting(v_env_4572_, v_isExporting_4561_);
v___x_4584_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_4582_ == 0)
{
lean_ctor_set(v___x_4581_, 5, v___x_4584_);
lean_ctor_set(v___x_4581_, 0, v___x_4583_);
v___x_4586_ = v___x_4581_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4583_);
lean_ctor_set(v_reuseFailAlloc_4632_, 1, v_nextMacroScope_4573_);
lean_ctor_set(v_reuseFailAlloc_4632_, 2, v_ngen_4574_);
lean_ctor_set(v_reuseFailAlloc_4632_, 3, v_auxDeclNGen_4575_);
lean_ctor_set(v_reuseFailAlloc_4632_, 4, v_traceState_4576_);
lean_ctor_set(v_reuseFailAlloc_4632_, 5, v___x_4584_);
lean_ctor_set(v_reuseFailAlloc_4632_, 6, v_messages_4577_);
lean_ctor_set(v_reuseFailAlloc_4632_, 7, v_infoState_4578_);
lean_ctor_set(v_reuseFailAlloc_4632_, 8, v_snapshotTasks_4579_);
v___x_4586_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v_mctx_4589_; lean_object* v_zetaDeltaFVarIds_4590_; lean_object* v_postponed_4591_; lean_object* v_diag_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4630_; 
v___x_4587_ = lean_st_ref_put(v___y_4565_, v___x_4586_);
v___x_4588_ = lean_st_ref_take(v___y_4563_);
v_mctx_4589_ = lean_ctor_get(v___x_4588_, 0);
v_zetaDeltaFVarIds_4590_ = lean_ctor_get(v___x_4588_, 2);
v_postponed_4591_ = lean_ctor_get(v___x_4588_, 3);
v_diag_4592_ = lean_ctor_get(v___x_4588_, 4);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4588_);
if (v_isSharedCheck_4630_ == 0)
{
lean_object* v_unused_4631_; 
v_unused_4631_ = lean_ctor_get(v___x_4588_, 1);
lean_dec(v_unused_4631_);
v___x_4594_ = v___x_4588_;
v_isShared_4595_ = v_isSharedCheck_4630_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_diag_4592_);
lean_inc(v_postponed_4591_);
lean_inc(v_zetaDeltaFVarIds_4590_);
lean_inc(v_mctx_4589_);
lean_dec(v___x_4588_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4630_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4596_; lean_object* v___x_4598_; 
v___x_4596_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 1, v___x_4596_);
v___x_4598_ = v___x_4594_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_mctx_4589_);
lean_ctor_set(v_reuseFailAlloc_4629_, 1, v___x_4596_);
lean_ctor_set(v_reuseFailAlloc_4629_, 2, v_zetaDeltaFVarIds_4590_);
lean_ctor_set(v_reuseFailAlloc_4629_, 3, v_postponed_4591_);
lean_ctor_set(v_reuseFailAlloc_4629_, 4, v_diag_4592_);
v___x_4598_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
lean_object* v___x_4599_; lean_object* v_r_4600_; 
v___x_4599_ = lean_st_ref_put(v___y_4563_, v___x_4598_);
lean_inc(v___y_4565_);
lean_inc_ref(v___y_4564_);
lean_inc(v___y_4563_);
lean_inc_ref(v___y_4562_);
v_r_4600_ = lean_apply_5(v_x_4560_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, lean_box(0));
if (lean_obj_tag(v_r_4600_) == 0)
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4617_; 
v_a_4601_ = lean_ctor_get(v_r_4600_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v_r_4600_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4603_ = v_r_4600_;
v_isShared_4604_ = v_isSharedCheck_4617_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v_r_4600_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4617_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
lean_inc(v_a_4601_);
if (v_isShared_4604_ == 0)
{
lean_ctor_set_tag(v___x_4603_, 1);
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
lean_object* v___x_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
v___x_4607_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4565_, v_isExporting_4569_, v___x_4584_, v___y_4563_, v___x_4596_, v___x_4606_);
lean_dec_ref(v___x_4606_);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4614_ == 0)
{
lean_object* v_unused_4615_; 
v_unused_4615_ = lean_ctor_get(v___x_4607_, 0);
lean_dec(v_unused_4615_);
v___x_4609_ = v___x_4607_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_dec(v___x_4607_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
lean_ctor_set(v___x_4609_, 0, v_a_4601_);
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4601_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4627_; 
v_a_4618_ = lean_ctor_get(v_r_4600_, 0);
lean_inc(v_a_4618_);
lean_dec_ref_known(v_r_4600_, 1);
v___x_4619_ = lean_box(0);
v___x_4620_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4565_, v_isExporting_4569_, v___x_4584_, v___y_4563_, v___x_4596_, v___x_4619_);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4627_ == 0)
{
lean_object* v_unused_4628_; 
v_unused_4628_ = lean_ctor_get(v___x_4620_, 0);
lean_dec(v_unused_4628_);
v___x_4622_ = v___x_4620_;
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
else
{
lean_dec(v___x_4620_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
lean_ctor_set_tag(v___x_4622_, 1);
lean_ctor_set(v___x_4622_, 0, v_a_4618_);
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4618_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___boxed(lean_object* v_x_4640_, lean_object* v_isExporting_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
uint8_t v_isExporting_boxed_4647_; lean_object* v_res_4648_; 
v_isExporting_boxed_4647_ = lean_unbox(v_isExporting_4641_);
v_res_4648_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4640_, v_isExporting_boxed_4647_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(lean_object* v_x_4649_, uint8_t v_when_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
if (v_when_4650_ == 0)
{
lean_object* v___x_4656_; 
lean_inc(v___y_4654_);
lean_inc_ref(v___y_4653_);
lean_inc(v___y_4652_);
lean_inc_ref(v___y_4651_);
v___x_4656_ = lean_apply_5(v_x_4649_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, lean_box(0));
return v___x_4656_;
}
else
{
uint8_t v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = 0;
v___x_4658_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4649_, v___x_4657_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
return v___x_4658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg___boxed(lean_object* v_x_4659_, lean_object* v_when_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
uint8_t v_when_boxed_4666_; lean_object* v_res_4667_; 
v_when_boxed_4666_ = lean_unbox(v_when_4660_);
v_res_4667_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v_x_4659_, v_when_boxed_4666_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(lean_object* v_o_4668_, lean_object* v_k_4669_, uint8_t v_v_4670_){
_start:
{
lean_object* v_map_4671_; uint8_t v_hasTrace_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4686_; 
v_map_4671_ = lean_ctor_get(v_o_4668_, 0);
v_hasTrace_4672_ = lean_ctor_get_uint8(v_o_4668_, sizeof(void*)*1);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_o_4668_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4674_ = v_o_4668_;
v_isShared_4675_ = v_isSharedCheck_4686_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_map_4671_);
lean_dec(v_o_4668_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4686_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4676_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4676_, 0, v_v_4670_);
lean_inc(v_k_4669_);
v___x_4677_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4669_, v___x_4676_, v_map_4671_);
if (v_hasTrace_4672_ == 0)
{
lean_object* v___x_4678_; uint8_t v___x_4679_; lean_object* v___x_4681_; 
v___x_4678_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4679_ = l_Lean_Name_isPrefixOf(v___x_4678_, v_k_4669_);
lean_dec(v_k_4669_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v___x_4677_);
v___x_4681_ = v___x_4674_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4677_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
lean_ctor_set_uint8(v___x_4681_, sizeof(void*)*1, v___x_4679_);
return v___x_4681_;
}
}
else
{
lean_object* v___x_4684_; 
lean_dec(v_k_4669_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v___x_4677_);
v___x_4684_ = v___x_4674_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4677_);
lean_ctor_set_uint8(v_reuseFailAlloc_4685_, sizeof(void*)*1, v_hasTrace_4672_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2___boxed(lean_object* v_o_4687_, lean_object* v_k_4688_, lean_object* v_v_4689_){
_start:
{
uint8_t v_v_boxed_4690_; lean_object* v_res_4691_; 
v_v_boxed_4690_ = lean_unbox(v_v_4689_);
v_res_4691_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(v_o_4687_, v_k_4688_, v_v_boxed_4690_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(lean_object* v_opts_4692_, lean_object* v_opt_4693_, uint8_t v_val_4694_){
_start:
{
lean_object* v_name_4695_; lean_object* v___x_4696_; 
v_name_4695_ = lean_ctor_get(v_opt_4693_, 0);
lean_inc(v_name_4695_);
lean_dec_ref(v_opt_4693_);
v___x_4696_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(v_opts_4692_, v_name_4695_, v_val_4694_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed(lean_object* v_opts_4697_, lean_object* v_opt_4698_, lean_object* v_val_4699_){
_start:
{
uint8_t v_val_boxed_4700_; lean_object* v_res_4701_; 
v_val_boxed_4700_ = lean_unbox(v_val_4699_);
v_res_4701_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_opts_4697_, v_opt_4698_, v_val_boxed_4700_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t v___x_4702_, lean_object* v___x_4703_, uint8_t v___x_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v___x_4710_; lean_object* v_fileName_4711_; lean_object* v_fileMap_4712_; lean_object* v_options_4713_; lean_object* v_currRecDepth_4714_; lean_object* v_ref_4715_; lean_object* v_currNamespace_4716_; lean_object* v_openDecls_4717_; lean_object* v_initHeartbeats_4718_; lean_object* v_maxHeartbeats_4719_; lean_object* v_quotContext_4720_; lean_object* v_currMacroScope_4721_; lean_object* v_cancelTk_x3f_4722_; uint8_t v_suppressElabErrors_4723_; lean_object* v_inheritedTraceOptions_4724_; lean_object* v_env_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; lean_object* v_fileName_4731_; lean_object* v_fileMap_4732_; lean_object* v_currRecDepth_4733_; lean_object* v_ref_4734_; lean_object* v_currNamespace_4735_; lean_object* v_openDecls_4736_; lean_object* v_initHeartbeats_4737_; lean_object* v_maxHeartbeats_4738_; lean_object* v_quotContext_4739_; lean_object* v_currMacroScope_4740_; lean_object* v_cancelTk_x3f_4741_; uint8_t v_suppressElabErrors_4742_; lean_object* v_inheritedTraceOptions_4743_; lean_object* v___y_4744_; uint8_t v___y_4750_; uint8_t v___x_4771_; 
v___x_4710_ = lean_st_ref_get(v___y_4708_);
v_fileName_4711_ = lean_ctor_get(v___y_4707_, 0);
v_fileMap_4712_ = lean_ctor_get(v___y_4707_, 1);
v_options_4713_ = lean_ctor_get(v___y_4707_, 2);
v_currRecDepth_4714_ = lean_ctor_get(v___y_4707_, 3);
v_ref_4715_ = lean_ctor_get(v___y_4707_, 5);
v_currNamespace_4716_ = lean_ctor_get(v___y_4707_, 6);
v_openDecls_4717_ = lean_ctor_get(v___y_4707_, 7);
v_initHeartbeats_4718_ = lean_ctor_get(v___y_4707_, 8);
v_maxHeartbeats_4719_ = lean_ctor_get(v___y_4707_, 9);
v_quotContext_4720_ = lean_ctor_get(v___y_4707_, 10);
v_currMacroScope_4721_ = lean_ctor_get(v___y_4707_, 11);
v_cancelTk_x3f_4722_ = lean_ctor_get(v___y_4707_, 12);
v_suppressElabErrors_4723_ = lean_ctor_get_uint8(v___y_4707_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4724_ = lean_ctor_get(v___y_4707_, 13);
v_env_4725_ = lean_ctor_get(v___x_4710_, 0);
lean_inc_ref(v_env_4725_);
lean_dec(v___x_4710_);
v___x_4726_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_4713_);
v___x_4727_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_options_4713_, v___x_4726_, v___x_4702_);
v___x_4728_ = l_Lean_diagnostics;
v___x_4729_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v___x_4727_, v___x_4728_);
v___x_4771_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4725_);
lean_dec_ref(v_env_4725_);
if (v___x_4771_ == 0)
{
if (v___x_4729_ == 0)
{
v_fileName_4731_ = v_fileName_4711_;
v_fileMap_4732_ = v_fileMap_4712_;
v_currRecDepth_4733_ = v_currRecDepth_4714_;
v_ref_4734_ = v_ref_4715_;
v_currNamespace_4735_ = v_currNamespace_4716_;
v_openDecls_4736_ = v_openDecls_4717_;
v_initHeartbeats_4737_ = v_initHeartbeats_4718_;
v_maxHeartbeats_4738_ = v_maxHeartbeats_4719_;
v_quotContext_4739_ = v_quotContext_4720_;
v_currMacroScope_4740_ = v_currMacroScope_4721_;
v_cancelTk_x3f_4741_ = v_cancelTk_x3f_4722_;
v_suppressElabErrors_4742_ = v_suppressElabErrors_4723_;
v_inheritedTraceOptions_4743_ = v_inheritedTraceOptions_4724_;
v___y_4744_ = v___y_4708_;
goto v___jp_4730_;
}
else
{
v___y_4750_ = v___x_4771_;
goto v___jp_4749_;
}
}
else
{
v___y_4750_ = v___x_4729_;
goto v___jp_4749_;
}
v___jp_4730_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4745_ = l_Lean_maxRecDepth;
v___x_4746_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v___x_4727_, v___x_4745_);
lean_inc_ref(v_inheritedTraceOptions_4743_);
lean_inc(v_cancelTk_x3f_4741_);
lean_inc(v_currMacroScope_4740_);
lean_inc(v_quotContext_4739_);
lean_inc(v_maxHeartbeats_4738_);
lean_inc(v_initHeartbeats_4737_);
lean_inc(v_openDecls_4736_);
lean_inc(v_currNamespace_4735_);
lean_inc(v_ref_4734_);
lean_inc(v_currRecDepth_4733_);
lean_inc_ref(v_fileMap_4732_);
lean_inc_ref(v_fileName_4731_);
v___x_4747_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4747_, 0, v_fileName_4731_);
lean_ctor_set(v___x_4747_, 1, v_fileMap_4732_);
lean_ctor_set(v___x_4747_, 2, v___x_4727_);
lean_ctor_set(v___x_4747_, 3, v_currRecDepth_4733_);
lean_ctor_set(v___x_4747_, 4, v___x_4746_);
lean_ctor_set(v___x_4747_, 5, v_ref_4734_);
lean_ctor_set(v___x_4747_, 6, v_currNamespace_4735_);
lean_ctor_set(v___x_4747_, 7, v_openDecls_4736_);
lean_ctor_set(v___x_4747_, 8, v_initHeartbeats_4737_);
lean_ctor_set(v___x_4747_, 9, v_maxHeartbeats_4738_);
lean_ctor_set(v___x_4747_, 10, v_quotContext_4739_);
lean_ctor_set(v___x_4747_, 11, v_currMacroScope_4740_);
lean_ctor_set(v___x_4747_, 12, v_cancelTk_x3f_4741_);
lean_ctor_set(v___x_4747_, 13, v_inheritedTraceOptions_4743_);
lean_ctor_set_uint8(v___x_4747_, sizeof(void*)*14, v___x_4729_);
lean_ctor_set_uint8(v___x_4747_, sizeof(void*)*14 + 1, v_suppressElabErrors_4742_);
v___x_4748_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v___x_4703_, v___x_4704_, v___y_4705_, v___y_4706_, v___x_4747_, v___y_4744_);
lean_dec_ref_known(v___x_4747_, 14);
return v___x_4748_;
}
v___jp_4749_:
{
if (v___y_4750_ == 0)
{
lean_object* v___x_4751_; lean_object* v_env_4752_; lean_object* v_nextMacroScope_4753_; lean_object* v_ngen_4754_; lean_object* v_auxDeclNGen_4755_; lean_object* v_traceState_4756_; lean_object* v_messages_4757_; lean_object* v_infoState_4758_; lean_object* v_snapshotTasks_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4769_; 
v___x_4751_ = lean_st_ref_take(v___y_4708_);
v_env_4752_ = lean_ctor_get(v___x_4751_, 0);
v_nextMacroScope_4753_ = lean_ctor_get(v___x_4751_, 1);
v_ngen_4754_ = lean_ctor_get(v___x_4751_, 2);
v_auxDeclNGen_4755_ = lean_ctor_get(v___x_4751_, 3);
v_traceState_4756_ = lean_ctor_get(v___x_4751_, 4);
v_messages_4757_ = lean_ctor_get(v___x_4751_, 6);
v_infoState_4758_ = lean_ctor_get(v___x_4751_, 7);
v_snapshotTasks_4759_ = lean_ctor_get(v___x_4751_, 8);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4769_ == 0)
{
lean_object* v_unused_4770_; 
v_unused_4770_ = lean_ctor_get(v___x_4751_, 5);
lean_dec(v_unused_4770_);
v___x_4761_ = v___x_4751_;
v_isShared_4762_ = v_isSharedCheck_4769_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_snapshotTasks_4759_);
lean_inc(v_infoState_4758_);
lean_inc(v_messages_4757_);
lean_inc(v_traceState_4756_);
lean_inc(v_auxDeclNGen_4755_);
lean_inc(v_ngen_4754_);
lean_inc(v_nextMacroScope_4753_);
lean_inc(v_env_4752_);
lean_dec(v___x_4751_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4769_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4766_; 
v___x_4763_ = l_Lean_Kernel_enableDiag(v_env_4752_, v___x_4729_);
v___x_4764_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_4762_ == 0)
{
lean_ctor_set(v___x_4761_, 5, v___x_4764_);
lean_ctor_set(v___x_4761_, 0, v___x_4763_);
v___x_4766_ = v___x_4761_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4763_);
lean_ctor_set(v_reuseFailAlloc_4768_, 1, v_nextMacroScope_4753_);
lean_ctor_set(v_reuseFailAlloc_4768_, 2, v_ngen_4754_);
lean_ctor_set(v_reuseFailAlloc_4768_, 3, v_auxDeclNGen_4755_);
lean_ctor_set(v_reuseFailAlloc_4768_, 4, v_traceState_4756_);
lean_ctor_set(v_reuseFailAlloc_4768_, 5, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4768_, 6, v_messages_4757_);
lean_ctor_set(v_reuseFailAlloc_4768_, 7, v_infoState_4758_);
lean_ctor_set(v_reuseFailAlloc_4768_, 8, v_snapshotTasks_4759_);
v___x_4766_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
lean_object* v___x_4767_; 
v___x_4767_ = lean_st_ref_put(v___y_4708_, v___x_4766_);
v_fileName_4731_ = v_fileName_4711_;
v_fileMap_4732_ = v_fileMap_4712_;
v_currRecDepth_4733_ = v_currRecDepth_4714_;
v_ref_4734_ = v_ref_4715_;
v_currNamespace_4735_ = v_currNamespace_4716_;
v_openDecls_4736_ = v_openDecls_4717_;
v_initHeartbeats_4737_ = v_initHeartbeats_4718_;
v_maxHeartbeats_4738_ = v_maxHeartbeats_4719_;
v_quotContext_4739_ = v_quotContext_4720_;
v_currMacroScope_4740_ = v_currMacroScope_4721_;
v_cancelTk_x3f_4741_ = v_cancelTk_x3f_4722_;
v_suppressElabErrors_4742_ = v_suppressElabErrors_4723_;
v_inheritedTraceOptions_4743_ = v_inheritedTraceOptions_4724_;
v___y_4744_ = v___y_4708_;
goto v___jp_4730_;
}
}
}
else
{
v_fileName_4731_ = v_fileName_4711_;
v_fileMap_4732_ = v_fileMap_4712_;
v_currRecDepth_4733_ = v_currRecDepth_4714_;
v_ref_4734_ = v_ref_4715_;
v_currNamespace_4735_ = v_currNamespace_4716_;
v_openDecls_4736_ = v_openDecls_4717_;
v_initHeartbeats_4737_ = v_initHeartbeats_4718_;
v_maxHeartbeats_4738_ = v_maxHeartbeats_4719_;
v_quotContext_4739_ = v_quotContext_4720_;
v_currMacroScope_4740_ = v_currMacroScope_4721_;
v_cancelTk_x3f_4741_ = v_cancelTk_x3f_4722_;
v_suppressElabErrors_4742_ = v_suppressElabErrors_4723_;
v_inheritedTraceOptions_4743_ = v_inheritedTraceOptions_4724_;
v___y_4744_ = v___y_4708_;
goto v___jp_4730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object* v___x_4772_, lean_object* v___x_4773_, lean_object* v___x_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
uint8_t v___x_9950__boxed_4780_; uint8_t v___x_9952__boxed_4781_; lean_object* v_res_4782_; 
v___x_9950__boxed_4780_ = lean_unbox(v___x_4772_);
v___x_9952__boxed_4781_ = lean_unbox(v___x_4774_);
v_res_4782_ = l_Lean_Elab_WF_mkUnfoldEq___lam__2(v___x_9950__boxed_4780_, v___x_4773_, v___x_9952__boxed_4781_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
return v_res_4782_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___closed__0));
v___x_4785_ = l_Lean_stringToMessageData(v___x_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object* v_preDef_4786_, lean_object* v_unaryPreDefName_4787_, lean_object* v_wfPreprocessProof_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_){
_start:
{
lean_object* v___x_4794_; lean_object* v_env_4795_; lean_object* v_levelParams_4796_; lean_object* v_declName_4797_; lean_object* v_value_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___f_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___f_4805_; uint8_t v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; uint8_t v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___f_4812_; lean_object* v___x_4813_; 
v___x_4794_ = lean_st_ref_get(v_a_4792_);
v_env_4795_ = lean_ctor_get(v___x_4794_, 0);
lean_inc_ref(v_env_4795_);
lean_dec(v___x_4794_);
v_levelParams_4796_ = lean_ctor_get(v_preDef_4786_, 1);
lean_inc(v_levelParams_4796_);
v_declName_4797_ = lean_ctor_get(v_preDef_4786_, 3);
lean_inc_n(v_declName_4797_, 2);
v_value_4798_ = lean_ctor_get(v_preDef_4786_, 7);
lean_inc_ref(v_value_4798_);
lean_dec_ref(v_preDef_4786_);
v___x_4799_ = l_Lean_Meta_unfoldThmSuffix;
v___x_4800_ = l_Lean_Meta_mkEqLikeNameFor(v_env_4795_, v_declName_4797_, v___x_4799_);
lean_inc(v___x_4800_);
v___f_4801_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4801_, 0, v_levelParams_4796_);
lean_closure_set(v___f_4801_, 1, v_declName_4797_);
lean_closure_set(v___f_4801_, 2, v_wfPreprocessProof_4788_);
lean_closure_set(v___f_4801_, 3, v___x_4800_);
lean_closure_set(v___f_4801_, 4, v_unaryPreDefName_4787_);
v___x_4802_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___closed__1, &l_Lean_Elab_WF_mkUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1);
v___x_4803_ = l_Lean_MessageData_ofName(v___x_4800_);
v___x_4804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4802_);
lean_ctor_set(v___x_4804_, 1, v___x_4803_);
v___f_4805_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4805_, 0, v___x_4804_);
v___x_4806_ = 0;
v___x_4807_ = lean_box(v___x_4806_);
v___x_4808_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed), 9, 4);
lean_closure_set(v___x_4808_, 0, lean_box(0));
lean_closure_set(v___x_4808_, 1, v_value_4798_);
lean_closure_set(v___x_4808_, 2, v___f_4801_);
lean_closure_set(v___x_4808_, 3, v___x_4807_);
v___x_4809_ = 1;
v___x_4810_ = lean_box(v___x_4806_);
v___x_4811_ = lean_box(v___x_4809_);
v___f_4812_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_4812_, 0, v___x_4810_);
lean_closure_set(v___f_4812_, 1, v___x_4808_);
lean_closure_set(v___f_4812_, 2, v___x_4811_);
v___x_4813_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4812_, v___f_4805_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v___x_4813_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4813_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4819_; 
if (v_isShared_4817_ == 0)
{
v___x_4819_ = v___x_4816_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4814_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
v_a_4822_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4813_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4813_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___boxed(lean_object* v_preDef_4830_, lean_object* v_unaryPreDefName_4831_, lean_object* v_wfPreprocessProof_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_){
_start:
{
lean_object* v_res_4838_; 
v_res_4838_ = l_Lean_Elab_WF_mkUnfoldEq(v_preDef_4830_, v_unaryPreDefName_4831_, v_wfPreprocessProof_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
lean_dec(v_a_4834_);
lean_dec_ref(v_a_4833_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6(lean_object* v_00_u03b1_4839_, lean_object* v_x_4840_, uint8_t v_isExporting_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
lean_object* v___x_4847_; 
v___x_4847_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4840_, v_isExporting_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4848_, lean_object* v_x_4849_, lean_object* v_isExporting_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
uint8_t v_isExporting_boxed_4856_; lean_object* v_res_4857_; 
v_isExporting_boxed_4856_ = lean_unbox(v_isExporting_4850_);
v_res_4857_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6(v_00_u03b1_4848_, v_x_4849_, v_isExporting_boxed_4856_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(lean_object* v_00_u03b1_4858_, lean_object* v_x_4859_, uint8_t v_when_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v___x_4866_; 
v___x_4866_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v_x_4859_, v_when_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___boxed(lean_object* v_00_u03b1_4867_, lean_object* v_x_4868_, lean_object* v_when_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
uint8_t v_when_boxed_4875_; lean_object* v_res_4876_; 
v_when_boxed_4875_ = lean_unbox(v_when_4869_);
v_res_4876_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(v_00_u03b1_4867_, v_x_4868_, v_when_boxed_4875_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
return v_res_4876_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0));
v___x_4879_ = l_Lean_stringToMessageData(v___x_4878_);
return v___x_4879_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4885_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3));
v___x_4886_ = l_Lean_stringToMessageData(v___x_4885_);
return v___x_4886_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4888_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5));
v___x_4889_ = l_Lean_stringToMessageData(v___x_4888_);
return v___x_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object* v_levelParams_4890_, lean_object* v_declName_4891_, lean_object* v___x_4892_, lean_object* v___x_4893_, lean_object* v___x_4894_, lean_object* v_xs_4895_, lean_object* v_body_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_){
_start:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4905_ = lean_box(0);
lean_inc(v_levelParams_4890_);
v___x_4906_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4890_, v___x_4905_);
v___x_4907_ = l_Lean_mkConst(v_declName_4891_, v___x_4906_);
v___x_4908_ = l_Lean_mkAppN(v___x_4907_, v_xs_4895_);
v___x_4909_ = l_Lean_Meta_mkEq(v___x_4908_, v_body_4896_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
lean_inc_n(v_a_4910_, 2);
lean_dec_ref_known(v___x_4909_, 1);
v___x_4911_ = lean_box(0);
v___x_4912_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4910_, v___x_4911_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref_known(v___x_4912_, 1);
v___x_4914_ = l_Lean_Expr_mvarId_x21(v_a_4913_);
v___x_4915_ = l_Lean_Elab_Eqns_deltaLHS(v___x_4914_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; uint8_t v___x_4917_; uint8_t v___x_4918_; lean_object* v___y_4920_; lean_object* v___y_4921_; lean_object* v___y_4922_; lean_object* v___y_4923_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc_n(v_a_4916_, 2);
lean_dec_ref_known(v___x_4915_, 1);
v___x_4917_ = 1;
v___x_4918_ = 0;
v___x_4979_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2));
v___x_4980_ = l_Lean_MVarId_applyConst(v_a_4916_, v___x_4892_, v___x_4979_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_);
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_object* v_a_4981_; uint8_t v___x_4982_; 
v_a_4981_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_a_4981_);
lean_dec_ref_known(v___x_4980_, 1);
v___x_4982_ = l_List_isEmpty___redArg(v_a_4981_);
lean_dec(v_a_4981_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
lean_dec(v_a_4913_);
lean_dec(v_a_4910_);
lean_dec(v___x_4893_);
lean_dec(v_levelParams_4890_);
v___x_4983_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4);
v___x_4984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4983_);
lean_ctor_set(v___x_4984_, 1, v___x_4894_);
v___x_4985_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6);
v___x_4986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4986_, 0, v___x_4984_);
lean_ctor_set(v___x_4986_, 1, v___x_4985_);
v___x_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4987_, 0, v_a_4916_);
v___x_4988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4986_);
lean_ctor_set(v___x_4988_, 1, v___x_4987_);
v___x_4989_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_4990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4988_);
lean_ctor_set(v___x_4990_, 1, v___x_4989_);
v___x_4991_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_4990_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_);
return v___x_4991_;
}
else
{
lean_dec(v_a_4916_);
lean_dec_ref(v___x_4894_);
v___y_4920_ = v___y_4897_;
v___y_4921_ = v___y_4898_;
v___y_4922_ = v___y_4899_;
v___y_4923_ = v___y_4900_;
goto v___jp_4919_;
}
}
else
{
lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
lean_dec(v_a_4916_);
lean_dec(v_a_4913_);
lean_dec(v_a_4910_);
lean_dec_ref(v___x_4894_);
lean_dec(v___x_4893_);
lean_dec(v_levelParams_4890_);
v_a_4992_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4994_ = v___x_4980_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_dec(v___x_4980_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4992_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
v___jp_4919_:
{
lean_object* v___x_4924_; lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4978_; 
v___x_4924_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4913_, v___y_4921_);
v_a_4925_ = lean_ctor_get(v___x_4924_, 0);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4924_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4927_ = v___x_4924_;
v_isShared_4928_ = v_isSharedCheck_4978_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4924_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4978_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
uint8_t v___x_4929_; lean_object* v___x_4930_; 
v___x_4929_ = 1;
v___x_4930_ = l_Lean_Meta_mkForallFVars(v_xs_4895_, v_a_4910_, v___x_4918_, v___x_4917_, v___x_4917_, v___x_4929_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4932_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___x_4930_, 1);
v___x_4932_ = l_Lean_Meta_letToHave(v_a_4931_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_a_4933_; lean_object* v___x_4934_; 
v_a_4933_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4933_);
lean_dec_ref_known(v___x_4932_, 1);
v___x_4934_ = l_Lean_Meta_mkLambdaFVars(v_xs_4895_, v_a_4925_, v___x_4918_, v___x_4917_, v___x_4918_, v___x_4917_, v___x_4929_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4934_) == 0)
{
lean_object* v_a_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4940_; 
v_a_4935_ = lean_ctor_get(v___x_4934_, 0);
lean_inc(v_a_4935_);
lean_dec_ref_known(v___x_4934_, 1);
lean_inc_n(v___x_4893_, 2);
v___x_4936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4893_);
lean_ctor_set(v___x_4936_, 1, v_levelParams_4890_);
lean_ctor_set(v___x_4936_, 2, v_a_4933_);
v___x_4937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4893_);
lean_ctor_set(v___x_4937_, 1, v___x_4905_);
v___x_4938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4936_);
lean_ctor_set(v___x_4938_, 1, v_a_4935_);
lean_ctor_set(v___x_4938_, 2, v___x_4937_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set_tag(v___x_4927_, 2);
lean_ctor_set(v___x_4927_, 0, v___x_4938_);
v___x_4940_ = v___x_4927_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v___x_4938_);
v___x_4940_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
lean_object* v___x_4941_; 
v___x_4941_ = l_Lean_addDecl(v___x_4940_, v___x_4918_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4941_) == 0)
{
lean_object* v___x_4942_; 
lean_dec_ref_known(v___x_4941_, 1);
lean_inc(v___x_4893_);
v___x_4942_ = l_Lean_inferDefEqAttr(v___x_4893_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4942_) == 0)
{
lean_object* v_options_4943_; uint8_t v_hasTrace_4944_; 
lean_dec_ref_known(v___x_4942_, 1);
v_options_4943_ = lean_ctor_get(v___y_4922_, 2);
v_hasTrace_4944_ = lean_ctor_get_uint8(v_options_4943_, sizeof(void*)*1);
if (v_hasTrace_4944_ == 0)
{
lean_dec(v___x_4893_);
goto v___jp_4902_;
}
else
{
lean_object* v_inheritedTraceOptions_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; uint8_t v___x_4948_; 
v_inheritedTraceOptions_4945_ = lean_ctor_get(v___y_4922_, 13);
v___x_4946_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4947_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_4948_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4945_, v_options_4943_, v___x_4947_);
if (v___x_4948_ == 0)
{
lean_dec(v___x_4893_);
goto v___jp_4902_;
}
else
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4949_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1);
v___x_4950_ = l_Lean_MessageData_ofConstName(v___x_4893_, v___x_4918_);
v___x_4951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4949_);
lean_ctor_set(v___x_4951_, 1, v___x_4950_);
v___x_4952_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_4946_, v___x_4951_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
return v___x_4952_;
}
}
}
else
{
lean_dec(v___x_4893_);
return v___x_4942_;
}
}
else
{
lean_dec(v___x_4893_);
return v___x_4941_;
}
}
}
else
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
lean_dec(v_a_4933_);
lean_del_object(v___x_4927_);
lean_dec(v___x_4893_);
lean_dec(v_levelParams_4890_);
v_a_4954_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4956_ = v___x_4934_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4934_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4957_ == 0)
{
v___x_4959_ = v___x_4956_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
else
{
lean_object* v_a_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4969_; 
lean_del_object(v___x_4927_);
lean_dec(v_a_4925_);
lean_dec(v___x_4893_);
lean_dec(v_levelParams_4890_);
v_a_4962_ = lean_ctor_get(v___x_4932_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4932_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4964_ = v___x_4932_;
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_a_4962_);
lean_dec(v___x_4932_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4967_; 
if (v_isShared_4965_ == 0)
{
v___x_4967_ = v___x_4964_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4962_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
return v___x_4967_;
}
}
}
}
else
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4977_; 
lean_del_object(v___x_4927_);
lean_dec(v_a_4925_);
lean_dec(v___x_4893_);
lean_dec(v_levelParams_4890_);
v_a_4970_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4972_ = v___x_4930_;
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4930_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
if (v_isShared_4973_ == 0)
{
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_a_4970_);
v___x_4975_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
return v___x_4975_;
}
}
}
}
}
}
else
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
lean_dec(v_a_4913_);
lean_dec(v_a_4910_);
lean_dec_ref(v___x_4894_);
lean_dec(v___x_4893_);
lean_dec(v___x_4892_);
lean_dec(v_levelParams_4890_);
v_a_5000_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5002_ = v___x_4915_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4915_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_5000_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
}
else
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
lean_dec(v_a_4910_);
lean_dec_ref(v___x_4894_);
lean_dec(v___x_4893_);
lean_dec(v___x_4892_);
lean_dec(v_levelParams_4890_);
v_a_5008_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_4912_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_4912_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
lean_dec_ref(v___x_4894_);
lean_dec(v___x_4893_);
lean_dec(v___x_4892_);
lean_dec(v_levelParams_4890_);
v_a_5016_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_4909_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_4909_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
v___jp_4902_:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4903_ = lean_box(0);
v___x_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
return v___x_4904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed(lean_object* v_levelParams_5024_, lean_object* v_declName_5025_, lean_object* v___x_5026_, lean_object* v___x_5027_, lean_object* v___x_5028_, lean_object* v_xs_5029_, lean_object* v_body_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(v_levelParams_5024_, v_declName_5025_, v___x_5026_, v___x_5027_, v___x_5028_, v_xs_5029_, v_body_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec_ref(v_xs_5029_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(uint8_t v___x_5037_, lean_object* v_value_5038_, lean_object* v___f_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
lean_object* v___x_5045_; lean_object* v_fileName_5046_; lean_object* v_fileMap_5047_; lean_object* v_options_5048_; lean_object* v_currRecDepth_5049_; lean_object* v_ref_5050_; lean_object* v_currNamespace_5051_; lean_object* v_openDecls_5052_; lean_object* v_initHeartbeats_5053_; lean_object* v_maxHeartbeats_5054_; lean_object* v_quotContext_5055_; lean_object* v_currMacroScope_5056_; lean_object* v_cancelTk_x3f_5057_; uint8_t v_suppressElabErrors_5058_; lean_object* v_inheritedTraceOptions_5059_; lean_object* v_env_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; uint8_t v___x_5064_; lean_object* v_fileName_5066_; lean_object* v_fileMap_5067_; lean_object* v_currRecDepth_5068_; lean_object* v_ref_5069_; lean_object* v_currNamespace_5070_; lean_object* v_openDecls_5071_; lean_object* v_initHeartbeats_5072_; lean_object* v_maxHeartbeats_5073_; lean_object* v_quotContext_5074_; lean_object* v_currMacroScope_5075_; lean_object* v_cancelTk_x3f_5076_; uint8_t v_suppressElabErrors_5077_; lean_object* v_inheritedTraceOptions_5078_; lean_object* v___y_5079_; uint8_t v___y_5085_; uint8_t v___x_5106_; 
v___x_5045_ = lean_st_ref_get(v___y_5043_);
v_fileName_5046_ = lean_ctor_get(v___y_5042_, 0);
v_fileMap_5047_ = lean_ctor_get(v___y_5042_, 1);
v_options_5048_ = lean_ctor_get(v___y_5042_, 2);
v_currRecDepth_5049_ = lean_ctor_get(v___y_5042_, 3);
v_ref_5050_ = lean_ctor_get(v___y_5042_, 5);
v_currNamespace_5051_ = lean_ctor_get(v___y_5042_, 6);
v_openDecls_5052_ = lean_ctor_get(v___y_5042_, 7);
v_initHeartbeats_5053_ = lean_ctor_get(v___y_5042_, 8);
v_maxHeartbeats_5054_ = lean_ctor_get(v___y_5042_, 9);
v_quotContext_5055_ = lean_ctor_get(v___y_5042_, 10);
v_currMacroScope_5056_ = lean_ctor_get(v___y_5042_, 11);
v_cancelTk_x3f_5057_ = lean_ctor_get(v___y_5042_, 12);
v_suppressElabErrors_5058_ = lean_ctor_get_uint8(v___y_5042_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5059_ = lean_ctor_get(v___y_5042_, 13);
v_env_5060_ = lean_ctor_get(v___x_5045_, 0);
lean_inc_ref(v_env_5060_);
lean_dec(v___x_5045_);
v___x_5061_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_5048_);
v___x_5062_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_options_5048_, v___x_5061_, v___x_5037_);
v___x_5063_ = l_Lean_diagnostics;
v___x_5064_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v___x_5062_, v___x_5063_);
v___x_5106_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5060_);
lean_dec_ref(v_env_5060_);
if (v___x_5106_ == 0)
{
if (v___x_5064_ == 0)
{
v_fileName_5066_ = v_fileName_5046_;
v_fileMap_5067_ = v_fileMap_5047_;
v_currRecDepth_5068_ = v_currRecDepth_5049_;
v_ref_5069_ = v_ref_5050_;
v_currNamespace_5070_ = v_currNamespace_5051_;
v_openDecls_5071_ = v_openDecls_5052_;
v_initHeartbeats_5072_ = v_initHeartbeats_5053_;
v_maxHeartbeats_5073_ = v_maxHeartbeats_5054_;
v_quotContext_5074_ = v_quotContext_5055_;
v_currMacroScope_5075_ = v_currMacroScope_5056_;
v_cancelTk_x3f_5076_ = v_cancelTk_x3f_5057_;
v_suppressElabErrors_5077_ = v_suppressElabErrors_5058_;
v_inheritedTraceOptions_5078_ = v_inheritedTraceOptions_5059_;
v___y_5079_ = v___y_5043_;
goto v___jp_5065_;
}
else
{
v___y_5085_ = v___x_5106_;
goto v___jp_5084_;
}
}
else
{
v___y_5085_ = v___x_5064_;
goto v___jp_5084_;
}
v___jp_5065_:
{
lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5080_ = l_Lean_maxRecDepth;
v___x_5081_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v___x_5062_, v___x_5080_);
lean_inc_ref(v_inheritedTraceOptions_5078_);
lean_inc(v_cancelTk_x3f_5076_);
lean_inc(v_currMacroScope_5075_);
lean_inc(v_quotContext_5074_);
lean_inc(v_maxHeartbeats_5073_);
lean_inc(v_initHeartbeats_5072_);
lean_inc(v_openDecls_5071_);
lean_inc(v_currNamespace_5070_);
lean_inc(v_ref_5069_);
lean_inc(v_currRecDepth_5068_);
lean_inc_ref(v_fileMap_5067_);
lean_inc_ref(v_fileName_5066_);
v___x_5082_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5082_, 0, v_fileName_5066_);
lean_ctor_set(v___x_5082_, 1, v_fileMap_5067_);
lean_ctor_set(v___x_5082_, 2, v___x_5062_);
lean_ctor_set(v___x_5082_, 3, v_currRecDepth_5068_);
lean_ctor_set(v___x_5082_, 4, v___x_5081_);
lean_ctor_set(v___x_5082_, 5, v_ref_5069_);
lean_ctor_set(v___x_5082_, 6, v_currNamespace_5070_);
lean_ctor_set(v___x_5082_, 7, v_openDecls_5071_);
lean_ctor_set(v___x_5082_, 8, v_initHeartbeats_5072_);
lean_ctor_set(v___x_5082_, 9, v_maxHeartbeats_5073_);
lean_ctor_set(v___x_5082_, 10, v_quotContext_5074_);
lean_ctor_set(v___x_5082_, 11, v_currMacroScope_5075_);
lean_ctor_set(v___x_5082_, 12, v_cancelTk_x3f_5076_);
lean_ctor_set(v___x_5082_, 13, v_inheritedTraceOptions_5078_);
lean_ctor_set_uint8(v___x_5082_, sizeof(void*)*14, v___x_5064_);
lean_ctor_set_uint8(v___x_5082_, sizeof(void*)*14 + 1, v_suppressElabErrors_5077_);
v___x_5083_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_value_5038_, v___f_5039_, v___x_5037_, v___y_5040_, v___y_5041_, v___x_5082_, v___y_5079_);
lean_dec_ref_known(v___x_5082_, 14);
return v___x_5083_;
}
v___jp_5084_:
{
if (v___y_5085_ == 0)
{
lean_object* v___x_5086_; lean_object* v_env_5087_; lean_object* v_nextMacroScope_5088_; lean_object* v_ngen_5089_; lean_object* v_auxDeclNGen_5090_; lean_object* v_traceState_5091_; lean_object* v_messages_5092_; lean_object* v_infoState_5093_; lean_object* v_snapshotTasks_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5104_; 
v___x_5086_ = lean_st_ref_take(v___y_5043_);
v_env_5087_ = lean_ctor_get(v___x_5086_, 0);
v_nextMacroScope_5088_ = lean_ctor_get(v___x_5086_, 1);
v_ngen_5089_ = lean_ctor_get(v___x_5086_, 2);
v_auxDeclNGen_5090_ = lean_ctor_get(v___x_5086_, 3);
v_traceState_5091_ = lean_ctor_get(v___x_5086_, 4);
v_messages_5092_ = lean_ctor_get(v___x_5086_, 6);
v_infoState_5093_ = lean_ctor_get(v___x_5086_, 7);
v_snapshotTasks_5094_ = lean_ctor_get(v___x_5086_, 8);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5104_ == 0)
{
lean_object* v_unused_5105_; 
v_unused_5105_ = lean_ctor_get(v___x_5086_, 5);
lean_dec(v_unused_5105_);
v___x_5096_ = v___x_5086_;
v_isShared_5097_ = v_isSharedCheck_5104_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_snapshotTasks_5094_);
lean_inc(v_infoState_5093_);
lean_inc(v_messages_5092_);
lean_inc(v_traceState_5091_);
lean_inc(v_auxDeclNGen_5090_);
lean_inc(v_ngen_5089_);
lean_inc(v_nextMacroScope_5088_);
lean_inc(v_env_5087_);
lean_dec(v___x_5086_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5104_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5101_; 
v___x_5098_ = l_Lean_Kernel_enableDiag(v_env_5087_, v___x_5064_);
v___x_5099_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 5, v___x_5099_);
lean_ctor_set(v___x_5096_, 0, v___x_5098_);
v___x_5101_ = v___x_5096_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_5098_);
lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_nextMacroScope_5088_);
lean_ctor_set(v_reuseFailAlloc_5103_, 2, v_ngen_5089_);
lean_ctor_set(v_reuseFailAlloc_5103_, 3, v_auxDeclNGen_5090_);
lean_ctor_set(v_reuseFailAlloc_5103_, 4, v_traceState_5091_);
lean_ctor_set(v_reuseFailAlloc_5103_, 5, v___x_5099_);
lean_ctor_set(v_reuseFailAlloc_5103_, 6, v_messages_5092_);
lean_ctor_set(v_reuseFailAlloc_5103_, 7, v_infoState_5093_);
lean_ctor_set(v_reuseFailAlloc_5103_, 8, v_snapshotTasks_5094_);
v___x_5101_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
lean_object* v___x_5102_; 
v___x_5102_ = lean_st_ref_put(v___y_5043_, v___x_5101_);
v_fileName_5066_ = v_fileName_5046_;
v_fileMap_5067_ = v_fileMap_5047_;
v_currRecDepth_5068_ = v_currRecDepth_5049_;
v_ref_5069_ = v_ref_5050_;
v_currNamespace_5070_ = v_currNamespace_5051_;
v_openDecls_5071_ = v_openDecls_5052_;
v_initHeartbeats_5072_ = v_initHeartbeats_5053_;
v_maxHeartbeats_5073_ = v_maxHeartbeats_5054_;
v_quotContext_5074_ = v_quotContext_5055_;
v_currMacroScope_5075_ = v_currMacroScope_5056_;
v_cancelTk_x3f_5076_ = v_cancelTk_x3f_5057_;
v_suppressElabErrors_5077_ = v_suppressElabErrors_5058_;
v_inheritedTraceOptions_5078_ = v_inheritedTraceOptions_5059_;
v___y_5079_ = v___y_5043_;
goto v___jp_5065_;
}
}
}
else
{
v_fileName_5066_ = v_fileName_5046_;
v_fileMap_5067_ = v_fileMap_5047_;
v_currRecDepth_5068_ = v_currRecDepth_5049_;
v_ref_5069_ = v_ref_5050_;
v_currNamespace_5070_ = v_currNamespace_5051_;
v_openDecls_5071_ = v_openDecls_5052_;
v_initHeartbeats_5072_ = v_initHeartbeats_5053_;
v_maxHeartbeats_5073_ = v_maxHeartbeats_5054_;
v_quotContext_5074_ = v_quotContext_5055_;
v_currMacroScope_5075_ = v_currMacroScope_5056_;
v_cancelTk_x3f_5076_ = v_cancelTk_x3f_5057_;
v_suppressElabErrors_5077_ = v_suppressElabErrors_5058_;
v_inheritedTraceOptions_5078_ = v_inheritedTraceOptions_5059_;
v___y_5079_ = v___y_5043_;
goto v___jp_5065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed(lean_object* v___x_5107_, lean_object* v_value_5108_, lean_object* v___f_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
uint8_t v___x_5503__boxed_5115_; lean_object* v_res_5116_; 
v___x_5503__boxed_5115_ = lean_unbox(v___x_5107_);
v_res_5116_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(v___x_5503__boxed_5115_, v_value_5108_, v___f_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_);
lean_dec(v___y_5113_);
lean_dec_ref(v___y_5112_);
lean_dec(v___y_5111_);
lean_dec_ref(v___y_5110_);
return v_res_5116_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_5118_; lean_object* v___x_5119_; 
v___x_5118_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0));
v___x_5119_ = l_Lean_stringToMessageData(v___x_5118_);
return v___x_5119_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3(void){
_start:
{
lean_object* v___x_5121_; lean_object* v___x_5122_; 
v___x_5121_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__2));
v___x_5122_ = l_Lean_stringToMessageData(v___x_5121_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object* v_preDef_5123_, lean_object* v_unaryPreDefName_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_){
_start:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v_env_5132_; lean_object* v_levelParams_5133_; lean_object* v_declName_5134_; lean_object* v_value_5135_; lean_object* v_env_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___f_5146_; lean_object* v___x_5147_; lean_object* v___f_5148_; uint8_t v___x_5149_; lean_object* v___x_5150_; lean_object* v___f_5151_; lean_object* v___x_5152_; 
v___x_5130_ = lean_st_ref_get(v_a_5128_);
v___x_5131_ = lean_st_ref_get(v_a_5128_);
v_env_5132_ = lean_ctor_get(v___x_5130_, 0);
lean_inc_ref(v_env_5132_);
lean_dec(v___x_5130_);
v_levelParams_5133_ = lean_ctor_get(v_preDef_5123_, 1);
lean_inc(v_levelParams_5133_);
v_declName_5134_ = lean_ctor_get(v_preDef_5123_, 3);
lean_inc_n(v_declName_5134_, 2);
v_value_5135_ = lean_ctor_get(v_preDef_5123_, 7);
lean_inc_ref(v_value_5135_);
lean_dec_ref(v_preDef_5123_);
v_env_5136_ = lean_ctor_get(v___x_5131_, 0);
lean_inc_ref(v_env_5136_);
lean_dec(v___x_5131_);
v___x_5137_ = l_Lean_Meta_unfoldThmSuffix;
v___x_5138_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5132_, v_declName_5134_, v___x_5137_);
v___x_5139_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5136_, v_unaryPreDefName_5124_, v___x_5137_);
v___x_5140_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1);
lean_inc(v___x_5138_);
v___x_5141_ = l_Lean_MessageData_ofName(v___x_5138_);
v___x_5142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5142_, 0, v___x_5140_);
lean_ctor_set(v___x_5142_, 1, v___x_5141_);
v___x_5143_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3);
v___x_5144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5144_, 0, v___x_5142_);
lean_ctor_set(v___x_5144_, 1, v___x_5143_);
lean_inc(v___x_5139_);
v___x_5145_ = l_Lean_MessageData_ofName(v___x_5139_);
lean_inc_ref(v___x_5145_);
v___f_5146_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5146_, 0, v_levelParams_5133_);
lean_closure_set(v___f_5146_, 1, v_declName_5134_);
lean_closure_set(v___f_5146_, 2, v___x_5139_);
lean_closure_set(v___f_5146_, 3, v___x_5138_);
lean_closure_set(v___f_5146_, 4, v___x_5145_);
v___x_5147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5147_, 0, v___x_5144_);
lean_ctor_set(v___x_5147_, 1, v___x_5145_);
v___f_5148_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_5148_, 0, v___x_5147_);
v___x_5149_ = 0;
v___x_5150_ = lean_box(v___x_5149_);
v___f_5151_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_5151_, 0, v___x_5150_);
lean_closure_set(v___f_5151_, 1, v_value_5135_);
lean_closure_set(v___f_5151_, 2, v___f_5146_);
v___x_5152_ = l_Lean_Meta_mapErrorImp___redArg(v___f_5151_, v___f_5148_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
if (lean_obj_tag(v___x_5152_) == 0)
{
lean_object* v_a_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5160_; 
v_a_5153_ = lean_ctor_get(v___x_5152_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5152_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5155_ = v___x_5152_;
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_a_5153_);
lean_dec(v___x_5152_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v___x_5158_; 
if (v_isShared_5156_ == 0)
{
v___x_5158_ = v___x_5155_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v_a_5153_);
v___x_5158_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
return v___x_5158_;
}
}
}
else
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5168_; 
v_a_5161_ = lean_ctor_get(v___x_5152_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5152_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5163_ = v___x_5152_;
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_5152_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5161_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___boxed(lean_object* v_preDef_5169_, lean_object* v_unaryPreDefName_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_preDef_5169_, v_unaryPreDefName_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
lean_dec(v_a_5174_);
lean_dec_ref(v_a_5173_);
lean_dec(v_a_5172_);
lean_dec_ref(v_a_5171_);
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5221_; uint8_t v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; 
v___x_5221_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5222_ = 0;
v___x_5223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5224_ = l_Lean_registerTraceClass(v___x_5221_, v___x_5222_, v___x_5223_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2____boxed(lean_object* v_a_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_();
return v_res_5226_;
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
