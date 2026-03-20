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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__2;
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "assertion violation: matcherInfo.numDiscrs = 1\n    "};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "assertion violation: discr.isFVar\n    "};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__4;
static const lean_array_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__5_value;
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
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7;
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WF"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(231, 60, 146, 67, 170, 35, 9, 50)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Unfold"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(107, 60, 73, 44, 205, 78, 214, 55)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(214, 186, 22, 181, 135, 89, 255, 35)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(127, 174, 101, 137, 114, 200, 12, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(33, 93, 149, 86, 9, 247, 3, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(177, 93, 103, 123, 232, 207, 165, 166)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "matcherPushArg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(225, 113, 246, 21, 195, 5, 15, 220)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
static const lean_array_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9____boxed(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "mkUnfoldEq defined "};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mkUnfoldEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Cannot derive unfold equation "};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___closed__0_value;
static lean_once_cell_t l_Lean_Elab_WF_mkUnfoldEq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 14, 28, 10, 226, 95, 51, 62)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 26, 119, 163, 229, 120, 15, 205)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(57, 120, 226, 204, 0, 34, 252, 196)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(156, 125, 245, 250, 214, 234, 210, 86)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(150, 57, 156, 205, 162, 224, 99, 74)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(201, 193, 43, 137, 57, 227, 113, 35)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(41, 253, 77, 165, 5, 71, 84, 139)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(133, 113, 198, 34, 182, 132, 253, 5)}};
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
lean_object* v___f_8_; lean_object* v___x_5139__overap_9_; lean_object* v___x_10_; 
v___f_8_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_5139__overap_9_ = lean_panic_fn(v___f_8_, v_msg_2_);
v___x_10_ = lean_apply_5(v___x_5139__overap_9_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___boxed(lean_object* v_msg_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(v_msg_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0(lean_object* v_k_18_, lean_object* v_b_19_, lean_object* v_c_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_apply_7(v_k_18_, v_b_19_, v_c_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, lean_box(0));
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed(lean_object* v_k_27_, lean_object* v_b_28_, lean_object* v_c_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0(v_k_27_, v_b_28_, v_c_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
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
uint8_t v___x_7605__boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v___x_7605__boxed_157_ = lean_unbox(v___x_155_);
v_res_158_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(v___x_7605__boxed_157_, v_x_156_);
lean_dec(v_x_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(lean_object* v___x_160_, lean_object* v___x_161_, uint8_t v___x_162_, lean_object* v_ys_163_, lean_object* v_x_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; uint8_t v___x_175_; lean_object* v___x_176_; 
v___x_170_ = l_Lean_Expr_appFn_x21(v___x_160_);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_array_get_borrowed(v___x_161_, v_ys_163_, v___x_171_);
lean_inc(v___x_172_);
v___x_173_ = l_Lean_Expr_app___override(v___x_170_, v___x_172_);
v___x_174_ = 0;
v___x_175_ = 1;
v___x_176_ = l_Lean_Meta_mkLambdaFVars(v_ys_163_, v___x_173_, v___x_174_, v___x_162_, v___x_174_, v___x_162_, v___x_175_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed(lean_object* v___x_177_, lean_object* v___x_178_, lean_object* v___x_179_, lean_object* v_ys_180_, lean_object* v_x_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
uint8_t v___x_7613__boxed_187_; lean_object* v_res_188_; 
v___x_7613__boxed_187_ = lean_unbox(v___x_179_);
v_res_188_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(v___x_177_, v___x_178_, v___x_7613__boxed_187_, v_ys_180_, v_x_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec_ref(v_x_181_);
lean_dec_ref(v_ys_180_);
lean_dec_ref(v___x_177_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(lean_object* v_msgData_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v___x_195_; lean_object* v_env_196_; lean_object* v___x_197_; lean_object* v_mctx_198_; lean_object* v_lctx_199_; lean_object* v_options_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_195_ = lean_st_ref_get(v___y_193_);
v_env_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc_ref(v_env_196_);
lean_dec(v___x_195_);
v___x_197_ = lean_st_ref_get(v___y_191_);
v_mctx_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc_ref(v_mctx_198_);
lean_dec(v___x_197_);
v_lctx_199_ = lean_ctor_get(v___y_190_, 2);
v_options_200_ = lean_ctor_get(v___y_192_, 2);
lean_inc_ref(v_options_200_);
lean_inc_ref(v_lctx_199_);
v___x_201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_201_, 0, v_env_196_);
lean_ctor_set(v___x_201_, 1, v_mctx_198_);
lean_ctor_set(v___x_201_, 2, v_lctx_199_);
lean_ctor_set(v___x_201_, 3, v_options_200_);
v___x_202_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_msgData_189_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4___boxed(lean_object* v_msgData_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msgData_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_ref_217_; lean_object* v___x_218_; lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_227_; 
v_ref_217_ = lean_ctor_get(v___y_214_, 5);
v___x_218_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_227_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
lean_inc(v_ref_217_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v_ref_217_);
lean_ctor_set(v___x_223_, 1, v_a_219_);
if (v_isShared_222_ == 0)
{
lean_ctor_set_tag(v___x_221_, 1);
lean_ctor_set(v___x_221_, 0, v___x_223_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg___boxed(lean_object* v_msg_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
lean_object* v_ks_239_; lean_object* v_vs_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_264_; 
v_ks_239_ = lean_ctor_get(v_x_235_, 0);
v_vs_240_ = lean_ctor_get(v_x_235_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_235_);
if (v_isSharedCheck_264_ == 0)
{
v___x_242_ = v_x_235_;
v_isShared_243_ = v_isSharedCheck_264_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_vs_240_);
lean_inc(v_ks_239_);
lean_dec(v_x_235_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_264_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_array_get_size(v_ks_239_);
v___x_245_ = lean_nat_dec_lt(v_x_236_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
lean_dec(v_x_236_);
v___x_246_ = lean_array_push(v_ks_239_, v_x_237_);
v___x_247_ = lean_array_push(v_vs_240_, v_x_238_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_247_);
lean_ctor_set(v___x_242_, 0, v___x_246_);
v___x_249_ = v___x_242_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
else
{
lean_object* v_k_x27_251_; uint8_t v___x_252_; 
v_k_x27_251_ = lean_array_fget_borrowed(v_ks_239_, v_x_236_);
v___x_252_ = l_Lean_instBEqMVarId_beq(v_x_237_, v_k_x27_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_254_; 
if (v_isShared_243_ == 0)
{
v___x_254_ = v___x_242_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_ks_239_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_vs_240_);
v___x_254_ = v_reuseFailAlloc_258_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_x_236_, v___x_255_);
lean_dec(v_x_236_);
v_x_235_ = v___x_254_;
v_x_236_ = v___x_256_;
goto _start;
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_259_ = lean_array_fset(v_ks_239_, v_x_236_, v_x_237_);
v___x_260_ = lean_array_fset(v_vs_240_, v_x_236_, v_x_238_);
lean_dec(v_x_236_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_260_);
lean_ctor_set(v___x_242_, 0, v___x_259_);
v___x_262_ = v___x_242_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_n_265_, lean_object* v_k_266_, lean_object* v_v_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_265_, v___x_268_, v_k_266_, v_v_267_);
return v___x_269_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; 
v___x_270_ = ((size_t)5ULL);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_shift_left(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_273_; size_t v___x_274_; size_t v___x_275_; 
v___x_273_ = ((size_t)1ULL);
v___x_274_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_275_ = lean_usize_sub(v___x_274_, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(lean_object* v_x_277_, size_t v_x_278_, size_t v_x_279_, lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v_es_282_; size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; size_t v___x_286_; lean_object* v_j_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_es_282_ = lean_ctor_get(v_x_277_, 0);
v___x_283_ = ((size_t)5ULL);
v___x_284_ = ((size_t)1ULL);
v___x_285_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__1);
v___x_286_ = lean_usize_land(v_x_278_, v___x_285_);
v_j_287_ = lean_usize_to_nat(v___x_286_);
v___x_288_ = lean_array_get_size(v_es_282_);
v___x_289_ = lean_nat_dec_lt(v_j_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_dec(v_j_287_);
lean_dec(v_x_281_);
lean_dec(v_x_280_);
return v_x_277_;
}
else
{
lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_326_; 
lean_inc_ref(v_es_282_);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; 
v_unused_327_ = lean_ctor_get(v_x_277_, 0);
lean_dec(v_unused_327_);
v___x_291_ = v_x_277_;
v_isShared_292_ = v_isSharedCheck_326_;
goto v_resetjp_290_;
}
else
{
lean_dec(v_x_277_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_326_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_v_293_; lean_object* v___x_294_; lean_object* v_xs_x27_295_; lean_object* v___y_297_; 
v_v_293_ = lean_array_fget(v_es_282_, v_j_287_);
v___x_294_ = lean_box(0);
v_xs_x27_295_ = lean_array_fset(v_es_282_, v_j_287_, v___x_294_);
switch(lean_obj_tag(v_v_293_))
{
case 0:
{
lean_object* v_key_302_; lean_object* v_val_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_313_; 
v_key_302_ = lean_ctor_get(v_v_293_, 0);
v_val_303_ = lean_ctor_get(v_v_293_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v_v_293_);
if (v_isSharedCheck_313_ == 0)
{
v___x_305_ = v_v_293_;
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_val_303_);
lean_inc(v_key_302_);
lean_dec(v_v_293_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
uint8_t v___x_307_; 
v___x_307_ = l_Lean_instBEqMVarId_beq(v_x_280_, v_key_302_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_del_object(v___x_305_);
v___x_308_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_302_, v_val_303_, v_x_280_, v_x_281_);
v___x_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
v___y_297_ = v___x_309_;
goto v___jp_296_;
}
else
{
lean_object* v___x_311_; 
lean_dec(v_val_303_);
lean_dec(v_key_302_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v_x_281_);
lean_ctor_set(v___x_305_, 0, v_x_280_);
v___x_311_ = v___x_305_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_x_280_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_x_281_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
v___y_297_ = v___x_311_;
goto v___jp_296_;
}
}
}
}
case 1:
{
lean_object* v_node_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_324_; 
v_node_314_ = lean_ctor_get(v_v_293_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v_v_293_);
if (v_isSharedCheck_324_ == 0)
{
v___x_316_ = v_v_293_;
v_isShared_317_ = v_isSharedCheck_324_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_node_314_);
lean_dec(v_v_293_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_324_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_318_ = lean_usize_shift_right(v_x_278_, v___x_283_);
v___x_319_ = lean_usize_add(v_x_279_, v___x_284_);
v___x_320_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_node_314_, v___x_318_, v___x_319_, v_x_280_, v_x_281_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_320_);
v___x_322_ = v___x_316_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
v___y_297_ = v___x_322_;
goto v___jp_296_;
}
}
}
default: 
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v_x_280_);
lean_ctor_set(v___x_325_, 1, v_x_281_);
v___y_297_ = v___x_325_;
goto v___jp_296_;
}
}
v___jp_296_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_array_fset(v_xs_x27_295_, v_j_287_, v___y_297_);
lean_dec(v_j_287_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_298_);
v___x_300_ = v___x_291_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
else
{
lean_object* v_ks_328_; lean_object* v_vs_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_349_; 
v_ks_328_ = lean_ctor_get(v_x_277_, 0);
v_vs_329_ = lean_ctor_get(v_x_277_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_349_ == 0)
{
v___x_331_ = v_x_277_;
v_isShared_332_ = v_isSharedCheck_349_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_vs_329_);
lean_inc(v_ks_328_);
lean_dec(v_x_277_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_349_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_ks_328_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_vs_329_);
v___x_334_ = v_reuseFailAlloc_348_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v_newNode_335_; uint8_t v___y_337_; size_t v___x_343_; uint8_t v___x_344_; 
v_newNode_335_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v___x_334_, v_x_280_, v_x_281_);
v___x_343_ = ((size_t)7ULL);
v___x_344_ = lean_usize_dec_le(v___x_343_, v_x_279_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_345_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_335_);
v___x_346_ = lean_unsigned_to_nat(4u);
v___x_347_ = lean_nat_dec_lt(v___x_345_, v___x_346_);
lean_dec(v___x_345_);
v___y_337_ = v___x_347_;
goto v___jp_336_;
}
else
{
v___y_337_ = v___x_344_;
goto v___jp_336_;
}
v___jp_336_:
{
if (v___y_337_ == 0)
{
lean_object* v_ks_338_; lean_object* v_vs_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_ks_338_ = lean_ctor_get(v_newNode_335_, 0);
lean_inc_ref(v_ks_338_);
v_vs_339_ = lean_ctor_get(v_newNode_335_, 1);
lean_inc_ref(v_vs_339_);
lean_dec_ref(v_newNode_335_);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__2);
v___x_342_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_x_279_, v_ks_338_, v_vs_339_, v___x_340_, v___x_341_);
lean_dec_ref(v_vs_339_);
lean_dec_ref(v_ks_338_);
return v___x_342_;
}
else
{
return v_newNode_335_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_350_, lean_object* v_keys_351_, lean_object* v_vals_352_, lean_object* v_i_353_, lean_object* v_entries_354_){
_start:
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_array_get_size(v_keys_351_);
v___x_356_ = lean_nat_dec_lt(v_i_353_, v___x_355_);
if (v___x_356_ == 0)
{
lean_dec(v_i_353_);
return v_entries_354_;
}
else
{
lean_object* v_k_357_; lean_object* v_v_358_; uint64_t v___x_359_; size_t v_h_360_; size_t v___x_361_; lean_object* v___x_362_; size_t v___x_363_; size_t v___x_364_; size_t v___x_365_; size_t v_h_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_k_357_ = lean_array_fget_borrowed(v_keys_351_, v_i_353_);
v_v_358_ = lean_array_fget_borrowed(v_vals_352_, v_i_353_);
v___x_359_ = l_Lean_instHashableMVarId_hash(v_k_357_);
v_h_360_ = lean_uint64_to_usize(v___x_359_);
v___x_361_ = ((size_t)5ULL);
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_sub(v_depth_350_, v___x_363_);
v___x_365_ = lean_usize_mul(v___x_361_, v___x_364_);
v_h_366_ = lean_usize_shift_right(v_h_360_, v___x_365_);
v___x_367_ = lean_nat_add(v_i_353_, v___x_362_);
lean_dec(v_i_353_);
lean_inc(v_v_358_);
lean_inc(v_k_357_);
v___x_368_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_entries_354_, v_h_366_, v_depth_350_, v_k_357_, v_v_358_);
v_i_353_ = v___x_367_;
v_entries_354_ = v___x_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_370_, lean_object* v_keys_371_, lean_object* v_vals_372_, lean_object* v_i_373_, lean_object* v_entries_374_){
_start:
{
size_t v_depth_boxed_375_; lean_object* v_res_376_; 
v_depth_boxed_375_ = lean_unbox_usize(v_depth_370_);
lean_dec(v_depth_370_);
v_res_376_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_375_, v_keys_371_, v_vals_372_, v_i_373_, v_entries_374_);
lean_dec_ref(v_vals_372_);
lean_dec_ref(v_keys_371_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
size_t v_x_7802__boxed_382_; size_t v_x_7803__boxed_383_; lean_object* v_res_384_; 
v_x_7802__boxed_382_ = lean_unbox_usize(v_x_378_);
lean_dec(v_x_378_);
v_x_7803__boxed_383_ = lean_unbox_usize(v_x_379_);
lean_dec(v_x_379_);
v_res_384_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_377_, v_x_7802__boxed_382_, v_x_7803__boxed_383_, v_x_380_, v_x_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
uint64_t v___x_388_; size_t v___x_389_; size_t v___x_390_; lean_object* v___x_391_; 
v___x_388_ = l_Lean_instHashableMVarId_hash(v_x_386_);
v___x_389_ = lean_uint64_to_usize(v___x_388_);
v___x_390_ = ((size_t)1ULL);
v___x_391_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_385_, v___x_389_, v___x_390_, v_x_386_, v_x_387_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(lean_object* v_mvarId_392_, lean_object* v_val_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; lean_object* v_mctx_397_; lean_object* v_cache_398_; lean_object* v_zetaDeltaFVarIds_399_; lean_object* v_postponed_400_; lean_object* v_diag_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_428_; 
v___x_396_ = lean_st_ref_take(v___y_394_);
v_mctx_397_ = lean_ctor_get(v___x_396_, 0);
v_cache_398_ = lean_ctor_get(v___x_396_, 1);
v_zetaDeltaFVarIds_399_ = lean_ctor_get(v___x_396_, 2);
v_postponed_400_ = lean_ctor_get(v___x_396_, 3);
v_diag_401_ = lean_ctor_get(v___x_396_, 4);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_428_ == 0)
{
v___x_403_ = v___x_396_;
v_isShared_404_ = v_isSharedCheck_428_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_diag_401_);
lean_inc(v_postponed_400_);
lean_inc(v_zetaDeltaFVarIds_399_);
lean_inc(v_cache_398_);
lean_inc(v_mctx_397_);
lean_dec(v___x_396_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_428_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_depth_405_; lean_object* v_levelAssignDepth_406_; lean_object* v_mvarCounter_407_; lean_object* v_lDepth_408_; lean_object* v_decls_409_; lean_object* v_userNames_410_; lean_object* v_lAssignment_411_; lean_object* v_eAssignment_412_; lean_object* v_dAssignment_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_427_; 
v_depth_405_ = lean_ctor_get(v_mctx_397_, 0);
v_levelAssignDepth_406_ = lean_ctor_get(v_mctx_397_, 1);
v_mvarCounter_407_ = lean_ctor_get(v_mctx_397_, 2);
v_lDepth_408_ = lean_ctor_get(v_mctx_397_, 3);
v_decls_409_ = lean_ctor_get(v_mctx_397_, 4);
v_userNames_410_ = lean_ctor_get(v_mctx_397_, 5);
v_lAssignment_411_ = lean_ctor_get(v_mctx_397_, 6);
v_eAssignment_412_ = lean_ctor_get(v_mctx_397_, 7);
v_dAssignment_413_ = lean_ctor_get(v_mctx_397_, 8);
v_isSharedCheck_427_ = !lean_is_exclusive(v_mctx_397_);
if (v_isSharedCheck_427_ == 0)
{
v___x_415_ = v_mctx_397_;
v_isShared_416_ = v_isSharedCheck_427_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_dAssignment_413_);
lean_inc(v_eAssignment_412_);
lean_inc(v_lAssignment_411_);
lean_inc(v_userNames_410_);
lean_inc(v_decls_409_);
lean_inc(v_lDepth_408_);
lean_inc(v_mvarCounter_407_);
lean_inc(v_levelAssignDepth_406_);
lean_inc(v_depth_405_);
lean_dec(v_mctx_397_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_427_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_eAssignment_412_, v_mvarId_392_, v_val_393_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 7, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_depth_405_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_levelAssignDepth_406_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_mvarCounter_407_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_lDepth_408_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v_decls_409_);
lean_ctor_set(v_reuseFailAlloc_426_, 5, v_userNames_410_);
lean_ctor_set(v_reuseFailAlloc_426_, 6, v_lAssignment_411_);
lean_ctor_set(v_reuseFailAlloc_426_, 7, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_426_, 8, v_dAssignment_413_);
v___x_419_ = v_reuseFailAlloc_426_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_421_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_419_);
v___x_421_ = v___x_403_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_cache_398_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_zetaDeltaFVarIds_399_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v_postponed_400_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v_diag_401_);
v___x_421_ = v_reuseFailAlloc_425_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_st_ref_set(v___y_394_, v___x_421_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg___boxed(lean_object* v_mvarId_429_, lean_object* v_val_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_429_, v_val_430_, v___y_431_);
lean_dec(v___y_431_);
return v_res_433_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_440_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4));
v___x_441_ = lean_unsigned_to_nat(41u);
v___x_442_ = lean_unsigned_to_nat(34u);
v___x_443_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3));
v___x_444_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_445_ = l_mkPanicMessageWithDecl(v___x_444_, v___x_443_, v___x_442_, v___x_441_, v___x_440_);
return v___x_445_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9));
v___x_453_ = l_Lean_stringToMessageData(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18(void){
_start:
{
lean_object* v___x_468_; lean_object* v_dummy_469_; 
v___x_468_ = lean_box(0);
v_dummy_469_ = l_Lean_Expr_sort___override(v___x_468_);
return v_dummy_469_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20));
v___x_476_ = l_Lean_stringToMessageData(v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object* v_mvarId_477_, lean_object* v___x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
lean_inc(v___y_482_);
lean_inc_ref(v___y_481_);
lean_inc(v___y_480_);
lean_inc_ref(v___y_479_);
lean_inc(v_mvarId_477_);
v___x_484_ = l_Lean_MVarId_getType_x27(v_mvarId_477_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v___x_484_);
v___x_486_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_487_ = lean_unsigned_to_nat(3u);
v___x_488_ = l_Lean_Expr_isAppOfArity(v_a_485_, v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_a_485_);
lean_dec_ref(v___x_478_);
lean_dec(v_mvarId_477_);
v___x_489_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5);
v___x_490_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(v___x_489_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___f_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = lean_box(v___x_488_);
v___f_492_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_492_, 0, v___x_491_);
v___x_493_ = l_Lean_Expr_appFn_x21(v_a_485_);
v___x_494_ = l_Lean_Expr_appArg_x21(v___x_493_);
lean_dec_ref(v___x_493_);
lean_inc_ref(v___x_494_);
v___x_495_ = l_Lean_Meta_delta_x3f(v___x_494_, v___f_492_, v___y_481_, v___y_482_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref(v___x_495_);
if (lean_obj_tag(v_a_496_) == 1)
{
lean_object* v_val_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_650_; 
v_val_497_ = lean_ctor_get(v_a_496_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_a_496_);
if (v_isSharedCheck_650_ == 0)
{
v___x_499_ = v_a_496_;
v_isShared_500_ = v_isSharedCheck_650_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_val_497_);
lean_dec(v_a_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_650_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; 
lean_inc(v_val_497_);
v___x_501_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_val_497_, v___y_480_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; lean_object* v___f_504_; lean_object* v___x_505_; lean_object* v_h_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
v___x_503_ = lean_box(v___x_488_);
v___f_504_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed), 10, 3);
lean_closure_set(v___f_504_, 0, v___x_494_);
lean_closure_set(v___f_504_, 1, v___x_478_);
lean_closure_set(v___f_504_, 2, v___x_503_);
v___x_505_ = l_Lean_Expr_appArg_x21(v_a_485_);
lean_dec(v_a_485_);
v___x_603_ = l_Lean_Expr_cleanupAnnotations(v_a_502_);
v___x_604_ = l_Lean_Expr_isApp(v___x_603_);
if (v___x_604_ == 0)
{
lean_dec_ref(v___x_603_);
v___y_582_ = v___y_479_;
v___y_583_ = v___y_480_;
v___y_584_ = v___y_481_;
v___y_585_ = v___y_482_;
goto v___jp_581_;
}
else
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = l_Lean_Expr_appFnCleanup___redArg(v___x_603_);
v___x_606_ = l_Lean_Expr_isApp(v___x_605_);
if (v___x_606_ == 0)
{
lean_dec_ref(v___x_605_);
v___y_582_ = v___y_479_;
v___y_583_ = v___y_480_;
v___y_584_ = v___y_481_;
v___y_585_ = v___y_482_;
goto v___jp_581_;
}
else
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = l_Lean_Expr_appFnCleanup___redArg(v___x_605_);
v___x_608_ = l_Lean_Expr_isApp(v___x_607_);
if (v___x_608_ == 0)
{
lean_dec_ref(v___x_607_);
v___y_582_ = v___y_479_;
v___y_583_ = v___y_480_;
v___y_584_ = v___y_481_;
v___y_585_ = v___y_482_;
goto v___jp_581_;
}
else
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = l_Lean_Expr_appFnCleanup___redArg(v___x_607_);
v___x_610_ = l_Lean_Expr_isApp(v___x_609_);
if (v___x_610_ == 0)
{
lean_dec_ref(v___x_609_);
v___y_582_ = v___y_479_;
v___y_583_ = v___y_480_;
v___y_584_ = v___y_481_;
v___y_585_ = v___y_482_;
goto v___jp_581_;
}
else
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = l_Lean_Expr_appFnCleanup___redArg(v___x_609_);
v___x_612_ = l_Lean_Expr_isApp(v___x_611_);
if (v___x_612_ == 0)
{
lean_dec_ref(v___x_611_);
v___y_582_ = v___y_479_;
v___y_583_ = v___y_480_;
v___y_584_ = v___y_481_;
v___y_585_ = v___y_482_;
goto v___jp_581_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_613_ = l_Lean_Expr_appFnCleanup___redArg(v___x_611_);
v___x_614_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14));
v___x_615_ = l_Lean_Expr_isConstOf(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
uint8_t v___x_616_; 
v___x_616_ = l_Lean_Expr_isApp(v___x_613_);
if (v___x_616_ == 0)
{
lean_dec_ref(v___x_613_);
v___y_582_ = v___y_479_;
v___y_583_ = v___y_480_;
v___y_584_ = v___y_481_;
v___y_585_ = v___y_482_;
goto v___jp_581_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = l_Lean_Expr_appFnCleanup___redArg(v___x_613_);
v___x_618_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15));
v___x_619_ = l_Lean_Expr_isConstOf(v___x_617_, v___x_618_);
lean_dec_ref(v___x_617_);
if (v___x_619_ == 0)
{
v___y_582_ = v___y_479_;
v___y_583_ = v___y_480_;
v___y_584_ = v___y_481_;
v___y_585_ = v___y_482_;
goto v___jp_581_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_dummy_624_; lean_object* v_nargs_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_del_object(v___x_499_);
v___x_620_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17));
v___x_621_ = l_Lean_Expr_getAppFn(v_val_497_);
v___x_622_ = l_Lean_Expr_constLevels_x21(v___x_621_);
lean_dec_ref(v___x_621_);
v___x_623_ = l_Lean_mkConst(v___x_620_, v___x_622_);
v_dummy_624_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_625_ = l_Lean_Expr_getAppNumArgs(v_val_497_);
lean_inc(v_nargs_625_);
v___x_626_ = lean_mk_array(v_nargs_625_, v_dummy_624_);
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_sub(v_nargs_625_, v___x_627_);
lean_dec(v_nargs_625_);
lean_inc(v_val_497_);
v___x_629_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_497_, v___x_626_, v___x_628_);
v___x_630_ = l_Lean_mkAppN(v___x_623_, v___x_629_);
lean_dec_ref(v___x_629_);
v_h_507_ = v___x_630_;
v___y_508_ = v___y_479_;
v___y_509_ = v___y_480_;
v___y_510_ = v___y_481_;
v___y_511_ = v___y_482_;
goto v___jp_506_;
}
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_dummy_635_; lean_object* v_nargs_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec_ref(v___x_613_);
lean_del_object(v___x_499_);
v___x_631_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19));
v___x_632_ = l_Lean_Expr_getAppFn(v_val_497_);
v___x_633_ = l_Lean_Expr_constLevels_x21(v___x_632_);
lean_dec_ref(v___x_632_);
v___x_634_ = l_Lean_mkConst(v___x_631_, v___x_633_);
v_dummy_635_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_636_ = l_Lean_Expr_getAppNumArgs(v_val_497_);
lean_inc(v_nargs_636_);
v___x_637_ = lean_mk_array(v_nargs_636_, v_dummy_635_);
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_sub(v_nargs_636_, v___x_638_);
lean_dec(v_nargs_636_);
lean_inc(v_val_497_);
v___x_640_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_497_, v___x_637_, v___x_639_);
v___x_641_ = l_Lean_mkAppN(v___x_634_, v___x_640_);
lean_dec_ref(v___x_640_);
v_h_507_ = v___x_641_;
v___y_508_ = v___y_479_;
v___y_509_ = v___y_480_;
v___y_510_ = v___y_481_;
v___y_511_ = v___y_482_;
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
v___x_512_ = l_Lean_Expr_appFn_x21(v_val_497_);
v___x_513_ = l_Lean_Expr_appArg_x21(v___x_512_);
lean_dec_ref(v___x_512_);
v___x_514_ = l_Lean_Expr_appArg_x21(v_val_497_);
lean_dec(v_val_497_);
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
lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref(v___x_516_);
v___x_518_ = l_Lean_Expr_bindingDomain_x21(v_a_517_);
lean_dec(v_a_517_);
v___x_519_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_520_ = 0;
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
lean_inc(v___y_509_);
lean_inc_ref(v___y_508_);
v___x_521_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_518_, v___x_519_, v___f_504_, v___x_520_, v___x_520_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v___x_521_);
v___x_523_ = l_Lean_mkAppB(v___x_513_, v___x_514_, v_a_522_);
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
lean_inc(v___y_509_);
lean_inc_ref(v___y_508_);
v___x_524_ = l_Lean_Meta_mkEq(v___x_523_, v___x_505_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref(v___x_524_);
v___x_526_ = lean_box(0);
lean_inc_ref(v___y_508_);
v___x_527_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_525_, v___x_526_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref(v___x_527_);
lean_inc(v___y_509_);
lean_inc(v_a_528_);
v___x_529_ = l_Lean_Meta_mkEqTrans(v_h_507_, v_a_528_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_539_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref(v___x_529_);
v___x_531_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_477_, v_a_530_, v___y_509_);
lean_dec(v___y_509_);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v___x_531_, 0);
lean_dec(v_unused_540_);
v___x_533_ = v___x_531_;
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
else
{
lean_dec(v___x_531_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = l_Lean_Expr_mvarId_x21(v_a_528_);
lean_dec(v_a_528_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_528_);
lean_dec(v___y_509_);
lean_dec(v_mvarId_477_);
v_a_541_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_529_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_529_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_h_507_);
lean_dec(v_mvarId_477_);
v_a_549_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_527_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_527_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_h_507_);
lean_dec(v_mvarId_477_);
v_a_557_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_524_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_524_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec_ref(v___x_514_);
lean_dec_ref(v___x_513_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_h_507_);
lean_dec_ref(v___x_505_);
lean_dec(v_mvarId_477_);
v_a_565_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_521_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_521_);
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
lean_dec_ref(v___x_514_);
lean_dec_ref(v___x_513_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_h_507_);
lean_dec_ref(v___x_505_);
lean_dec_ref(v___f_504_);
lean_dec(v_mvarId_477_);
v_a_573_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_516_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_516_);
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
v___jp_581_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_586_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8));
v___x_587_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10);
lean_inc(v_val_497_);
v___x_588_ = l_Lean_MessageData_ofExpr(v_val_497_);
v___x_589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_589_);
v___x_591_ = v___x_499_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_602_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; 
lean_inc(v_mvarId_477_);
v___x_592_ = l_Lean_Meta_throwTacticEx___redArg(v___x_586_, v_mvarId_477_, v___x_591_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref(v___x_592_);
v_h_507_ = v_a_593_;
v___y_508_ = v___y_582_;
v___y_509_ = v___y_583_;
v___y_510_ = v___y_584_;
v___y_511_ = v___y_585_;
goto v___jp_506_;
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec_ref(v___x_505_);
lean_dec_ref(v___f_504_);
lean_dec(v_val_497_);
lean_dec(v_mvarId_477_);
v_a_594_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_592_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_592_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_del_object(v___x_499_);
lean_dec(v_val_497_);
lean_dec_ref(v___x_494_);
lean_dec(v_a_485_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v___x_478_);
lean_dec(v_mvarId_477_);
v_a_642_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_501_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_501_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec(v_a_496_);
lean_dec(v_a_485_);
lean_dec_ref(v___x_478_);
lean_dec(v_mvarId_477_);
v___x_651_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21);
v___x_652_ = l_Lean_MessageData_ofExpr(v___x_494_);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_653_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v___x_654_;
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v___x_494_);
lean_dec(v_a_485_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v___x_478_);
lean_dec(v_mvarId_477_);
v_a_655_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_495_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_495_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v___x_478_);
lean_dec(v_mvarId_477_);
v_a_663_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_484_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_484_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed(lean_object* v_mvarId_671_, lean_object* v___x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(v_mvarId_671_, v___x_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(lean_object* v_mvarId_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v___x_685_; lean_object* v___f_686_; lean_object* v___x_687_; 
v___x_685_ = l_Lean_instInhabitedExpr;
lean_inc(v_mvarId_679_);
v___f_686_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed), 7, 2);
lean_closure_set(v___f_686_, 0, v_mvarId_679_);
lean_closure_set(v___f_686_, 1, v___x_685_);
v___x_687_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(v_mvarId_679_, v___f_686_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___boxed(lean_object* v_mvarId_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(lean_object* v_mvarId_695_, lean_object* v_val_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_695_, v_val_696_, v___y_698_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___boxed(lean_object* v_mvarId_703_, lean_object* v_val_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(v_mvarId_703_, v_val_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(lean_object* v_00_u03b1_711_, lean_object* v_msg_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___boxed(lean_object* v_00_u03b1_719_, lean_object* v_msg_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(v_00_u03b1_719_, v_msg_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2(lean_object* v_00_u03b2_727_, lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_x_728_, v_x_729_, v_x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_732_, lean_object* v_x_733_, size_t v_x_734_, size_t v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_733_, v_x_734_, v_x_735_, v_x_736_, v_x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_739_, lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
size_t v_x_8597__boxed_745_; size_t v_x_8598__boxed_746_; lean_object* v_res_747_; 
v_x_8597__boxed_745_ = lean_unbox_usize(v_x_741_);
lean_dec(v_x_741_);
v_x_8598__boxed_746_ = lean_unbox_usize(v_x_742_);
lean_dec(v_x_742_);
v_res_747_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(v_00_u03b2_739_, v_x_740_, v_x_8597__boxed_745_, v_x_8598__boxed_746_, v_x_743_, v_x_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_748_, lean_object* v_n_749_, lean_object* v_k_750_, lean_object* v_v_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v_n_749_, v_k_750_, v_v_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_753_, size_t v_depth_754_, lean_object* v_keys_755_, lean_object* v_vals_756_, lean_object* v_heq_757_, lean_object* v_i_758_, lean_object* v_entries_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_754_, v_keys_755_, v_vals_756_, v_i_758_, v_entries_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_761_, lean_object* v_depth_762_, lean_object* v_keys_763_, lean_object* v_vals_764_, lean_object* v_heq_765_, lean_object* v_i_766_, lean_object* v_entries_767_){
_start:
{
size_t v_depth_boxed_768_; lean_object* v_res_769_; 
v_depth_boxed_768_ = lean_unbox_usize(v_depth_762_);
lean_dec(v_depth_762_);
v_res_769_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_761_, v_depth_boxed_768_, v_keys_763_, v_vals_764_, v_heq_765_, v_i_766_, v_entries_767_);
lean_dec_ref(v_vals_764_);
lean_dec_ref(v_keys_763_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_770_, lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_771_, v_x_772_, v_x_773_, v_x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(lean_object* v_e_776_, lean_object* v_maxFVars_777_, lean_object* v_k_778_, uint8_t v_cleanupAnnotations_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___f_785_; uint8_t v___x_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___f_785_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_785_, 0, v_k_778_);
v___x_786_ = 1;
v___x_787_ = 0;
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_maxFVars_777_);
v___x_789_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_776_, v___x_786_, v___x_787_, v___x_786_, v___x_787_, v___x_788_, v___f_785_, v_cleanupAnnotations_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec_ref(v___x_788_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_a_798_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_789_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_789_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg___boxed(lean_object* v_e_806_, lean_object* v_maxFVars_807_, lean_object* v_k_808_, lean_object* v_cleanupAnnotations_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_815_; lean_object* v_res_816_; 
v_cleanupAnnotations_boxed_815_ = lean_unbox(v_cleanupAnnotations_809_);
v_res_816_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_806_, v_maxFVars_807_, v_k_808_, v_cleanupAnnotations_boxed_815_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(lean_object* v_00_u03b1_817_, lean_object* v_e_818_, lean_object* v_maxFVars_819_, lean_object* v_k_820_, uint8_t v_cleanupAnnotations_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_818_, v_maxFVars_819_, v_k_820_, v_cleanupAnnotations_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___boxed(lean_object* v_00_u03b1_828_, lean_object* v_e_829_, lean_object* v_maxFVars_830_, lean_object* v_k_831_, lean_object* v_cleanupAnnotations_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_838_; lean_object* v_res_839_; 
v_cleanupAnnotations_boxed_838_ = lean_unbox(v_cleanupAnnotations_832_);
v_res_839_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(v_00_u03b1_828_, v_e_829_, v_maxFVars_830_, v_k_831_, v_cleanupAnnotations_boxed_838_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(lean_object* v___x_840_, lean_object* v_xs_841_, lean_object* v_t_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v___y_852_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = lean_array_get_size(v_xs_841_);
v___x_876_ = lean_nat_dec_eq(v___x_875_, v___x_840_);
if (v___x_876_ == 0)
{
v___y_852_ = v___x_876_;
goto v___jp_851_;
}
else
{
uint8_t v___x_877_; 
v___x_877_ = l_Lean_Expr_isForall(v_t_842_);
v___y_852_ = v___x_877_;
goto v___jp_851_;
}
v___jp_848_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_box(0);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
v___jp_851_:
{
if (v___y_852_ == 0)
{
goto v___jp_848_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_853_ = l_Lean_Expr_bindingBody_x21(v_t_842_);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_expr_has_loose_bvar(v___x_853_, v___x_854_);
if (v___x_855_ == 0)
{
uint8_t v___x_856_; lean_object* v___x_857_; 
v___x_856_ = 1;
v___x_857_ = l_Lean_Meta_mkLambdaFVars(v_xs_841_, v___x_853_, v___x_855_, v___y_852_, v___x_855_, v___y_852_, v___x_856_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_866_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_866_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_866_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_866_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_862_, 0, v_a_858_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_862_);
v___x_864_ = v___x_860_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_a_867_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_857_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_857_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_dec_ref(v___x_853_);
goto v___jp_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed(lean_object* v___x_878_, lean_object* v_xs_879_, lean_object* v_t_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(v___x_878_, v_xs_879_, v_t_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec_ref(v_t_880_);
lean_dec_ref(v_xs_879_);
lean_dec(v___x_878_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(lean_object* v_matcherApp_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_motive_893_; lean_object* v_discrs_894_; lean_object* v___x_895_; lean_object* v___f_896_; uint8_t v___x_897_; lean_object* v___x_898_; 
v_motive_893_ = lean_ctor_get(v_matcherApp_887_, 4);
lean_inc_ref(v_motive_893_);
v_discrs_894_ = lean_ctor_get(v_matcherApp_887_, 5);
lean_inc_ref(v_discrs_894_);
lean_dec_ref(v_matcherApp_887_);
v___x_895_ = lean_array_get_size(v_discrs_894_);
lean_dec_ref(v_discrs_894_);
v___f_896_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed), 8, 1);
lean_closure_set(v___f_896_, 0, v___x_895_);
v___x_897_ = 0;
v___x_898_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_motive_893_, v___x_895_, v___f_896_, v___x_897_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___boxed(lean_object* v_matcherApp_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_matcherApp_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(lean_object* v_e_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; lean_object* v_env_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_909_ = lean_st_ref_get(v___y_907_);
v_env_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc_ref(v_env_910_);
lean_dec(v___x_909_);
v___x_911_ = l_Lean_Meta_isMatcherAppCore(v_env_910_, v_e_906_);
v___x_912_ = lean_box(v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg___boxed(lean_object* v_e_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v_e_914_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(lean_object* v_e_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_918_, v___y_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___boxed(lean_object* v_e_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(v_e_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v_e_925_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(lean_object* v_msg_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___f_938_; lean_object* v___x_899__overap_939_; lean_object* v___x_940_; 
v___f_938_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_899__overap_939_ = lean_panic_fn(v___f_938_, v_msg_932_);
v___x_940_ = lean_apply_5(v___x_899__overap_939_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, lean_box(0));
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1___boxed(lean_object* v_msg_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v_msg_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(size_t v_sz_948_, size_t v_i_949_, lean_object* v_bs_950_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = lean_usize_dec_lt(v_i_949_, v_sz_948_);
if (v___x_951_ == 0)
{
return v_bs_950_;
}
else
{
lean_object* v_v_952_; lean_object* v_toInductionSubgoal_953_; lean_object* v_mvarId_954_; lean_object* v___x_955_; lean_object* v_bs_x27_956_; size_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
v_v_952_ = lean_array_uget_borrowed(v_bs_950_, v_i_949_);
v_toInductionSubgoal_953_ = lean_ctor_get(v_v_952_, 0);
v_mvarId_954_ = lean_ctor_get(v_toInductionSubgoal_953_, 0);
lean_inc(v_mvarId_954_);
v___x_955_ = lean_unsigned_to_nat(0u);
v_bs_x27_956_ = lean_array_uset(v_bs_950_, v_i_949_, v___x_955_);
v___x_957_ = ((size_t)1ULL);
v___x_958_ = lean_usize_add(v_i_949_, v___x_957_);
v___x_959_ = lean_array_uset(v_bs_x27_956_, v_i_949_, v_mvarId_954_);
v_i_949_ = v___x_958_;
v_bs_950_ = v___x_959_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2___boxed(lean_object* v_sz_961_, lean_object* v_i_962_, lean_object* v_bs_963_){
_start:
{
size_t v_sz_boxed_964_; size_t v_i_boxed_965_; lean_object* v_res_966_; 
v_sz_boxed_964_ = lean_unbox_usize(v_sz_961_);
lean_dec(v_sz_961_);
v_i_boxed_965_ = lean_unbox_usize(v_i_962_);
lean_dec(v_i_962_);
v_res_966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_boxed_964_, v_i_boxed_965_, v_bs_963_);
return v_res_966_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1));
v___x_970_ = lean_unsigned_to_nat(4u);
v___x_971_ = lean_unsigned_to_nat(76u);
v___x_972_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0));
v___x_973_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_974_ = l_mkPanicMessageWithDecl(v___x_973_, v___x_972_, v___x_971_, v___x_970_, v___x_969_);
return v___x_974_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__4(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_976_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3));
v___x_977_ = lean_unsigned_to_nat(4u);
v___x_978_ = lean_unsigned_to_nat(78u);
v___x_979_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0));
v___x_980_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_981_ = l_mkPanicMessageWithDecl(v___x_980_, v___x_979_, v___x_978_, v___x_977_, v___x_976_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(lean_object* v_mvarId_984_, lean_object* v_e_985_, lean_object* v_matcherInfo_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; lean_object* v_a_993_; uint8_t v___x_994_; 
v___x_992_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_985_, v_a_990_);
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref(v___x_992_);
v___x_994_ = lean_unbox(v_a_993_);
if (v___x_994_ == 0)
{
lean_object* v_numParams_995_; lean_object* v_numDiscrs_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_numParams_995_ = lean_ctor_get(v_matcherInfo_986_, 0);
v_numDiscrs_996_ = lean_ctor_get(v_matcherInfo_986_, 1);
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_dec_eq(v_numDiscrs_996_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec(v_a_993_);
lean_dec_ref(v_e_985_);
lean_dec(v_mvarId_984_);
v___x_999_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2);
v___x_1000_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v___x_999_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; lean_object* v_dummy_1002_; lean_object* v_nargs_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1001_ = l_Lean_instInhabitedExpr;
v_dummy_1002_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_1003_ = l_Lean_Expr_getAppNumArgs(v_e_985_);
lean_inc(v_nargs_1003_);
v___x_1004_ = lean_mk_array(v_nargs_1003_, v_dummy_1002_);
v___x_1005_ = lean_nat_sub(v_nargs_1003_, v___x_997_);
lean_dec(v_nargs_1003_);
v___x_1006_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_985_, v___x_1004_, v___x_1005_);
v___x_1007_ = lean_nat_add(v_numParams_995_, v___x_997_);
v___x_1008_ = lean_array_get(v___x_1001_, v___x_1006_, v___x_1007_);
lean_dec(v___x_1007_);
lean_dec_ref(v___x_1006_);
v___x_1009_ = l_Lean_Expr_isFVar(v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec(v___x_1008_);
lean_dec(v_a_993_);
lean_dec(v_mvarId_984_);
v___x_1010_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__4);
v___x_1011_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v___x_1010_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
return v___x_1011_;
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; 
v___x_1012_ = l_Lean_Expr_fvarId_x21(v___x_1008_);
lean_dec(v___x_1008_);
v___x_1013_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__5));
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_unbox(v_a_993_);
lean_dec(v_a_993_);
v___x_1016_ = l_Lean_MVarId_cases(v_mvarId_984_, v___x_1012_, v___x_1013_, v___x_1015_, v___x_1014_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1028_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1028_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1028_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
size_t v_sz_1021_; size_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v_sz_1021_ = lean_array_size(v_a_1017_);
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_1021_, v___x_1022_, v_a_1017_);
v___x_1024_ = lean_array_to_list(v___x_1023_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1024_);
v___x_1026_ = v___x_1019_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_a_1029_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1016_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1016_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
else
{
lean_object* v___x_1037_; 
lean_dec(v_a_993_);
v___x_1037_ = l_Lean_Meta_Split_splitMatch(v_mvarId_984_, v_e_985_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___boxed(lean_object* v_mvarId_1038_, lean_object* v_e_1039_, lean_object* v_matcherInfo_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v_mvarId_1038_, v_e_1039_, v_matcherInfo_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
lean_dec_ref(v_matcherInfo_1040_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___f_1053_; lean_object* v___x_12431__overap_1054_; lean_object* v___x_1055_; 
v___f_1053_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_12431__overap_1054_ = lean_panic_fn(v___f_1053_, v_msg_1047_);
v___x_1055_ = lean_apply_5(v___x_12431__overap_1054_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, lean_box(0));
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1___boxed(lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v_msg_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(lean_object* v_type_1063_, lean_object* v_k_1064_, uint8_t v_cleanupAnnotations_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___f_1071_; uint8_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___f_1071_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1071_, 0, v_k_1064_);
v___x_1072_ = 0;
v___x_1073_ = lean_box(0);
v___x_1074_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1072_, v___x_1073_, v_type_1063_, v___f_1071_, v_cleanupAnnotations_1065_, v___x_1072_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1074_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1074_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg___boxed(lean_object* v_type_1091_, lean_object* v_k_1092_, lean_object* v_cleanupAnnotations_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1099_; lean_object* v_res_1100_; 
v_cleanupAnnotations_boxed_1099_ = lean_unbox(v_cleanupAnnotations_1093_);
v_res_1100_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1091_, v_k_1092_, v_cleanupAnnotations_boxed_1099_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(lean_object* v_00_u03b1_1101_, lean_object* v_type_1102_, lean_object* v_k_1103_, uint8_t v_cleanupAnnotations_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1102_, v_k_1103_, v_cleanupAnnotations_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___boxed(lean_object* v_00_u03b1_1111_, lean_object* v_type_1112_, lean_object* v_k_1113_, lean_object* v_cleanupAnnotations_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1120_; lean_object* v_res_1121_; 
v_cleanupAnnotations_boxed_1120_ = lean_unbox(v_cleanupAnnotations_1114_);
v_res_1121_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(v_00_u03b1_1111_, v_type_1112_, v_k_1113_, v_cleanupAnnotations_boxed_1120_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(lean_object* v_e_1122_, lean_object* v___y_1123_){
_start:
{
uint8_t v___x_1125_; 
v___x_1125_ = l_Lean_Expr_hasMVar(v_e_1122_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_e_1122_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; lean_object* v_mctx_1128_; lean_object* v___x_1129_; lean_object* v_fst_1130_; lean_object* v_snd_1131_; lean_object* v___x_1132_; lean_object* v_cache_1133_; lean_object* v_zetaDeltaFVarIds_1134_; lean_object* v_postponed_1135_; lean_object* v_diag_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1145_; 
v___x_1127_ = lean_st_ref_get(v___y_1123_);
v_mctx_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_mctx_1128_);
lean_dec(v___x_1127_);
v___x_1129_ = l_Lean_instantiateMVarsCore(v_mctx_1128_, v_e_1122_);
v_fst_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_fst_1130_);
v_snd_1131_ = lean_ctor_get(v___x_1129_, 1);
lean_inc(v_snd_1131_);
lean_dec_ref(v___x_1129_);
v___x_1132_ = lean_st_ref_take(v___y_1123_);
v_cache_1133_ = lean_ctor_get(v___x_1132_, 1);
v_zetaDeltaFVarIds_1134_ = lean_ctor_get(v___x_1132_, 2);
v_postponed_1135_ = lean_ctor_get(v___x_1132_, 3);
v_diag_1136_ = lean_ctor_get(v___x_1132_, 4);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; 
v_unused_1146_ = lean_ctor_get(v___x_1132_, 0);
lean_dec(v_unused_1146_);
v___x_1138_ = v___x_1132_;
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_diag_1136_);
lean_inc(v_postponed_1135_);
lean_inc(v_zetaDeltaFVarIds_1134_);
lean_inc(v_cache_1133_);
lean_dec(v___x_1132_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v_snd_1131_);
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_snd_1131_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_cache_1133_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_zetaDeltaFVarIds_1134_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_postponed_1135_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_diag_1136_);
v___x_1141_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_st_ref_set(v___y_1123_, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_fst_1130_);
return v___x_1143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg___boxed(lean_object* v_e_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1147_, v___y_1148_);
lean_dec(v___y_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(lean_object* v_e_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1151_, v___y_1153_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___boxed(lean_object* v_e_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(v_e_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(lean_object* v_x_1165_, lean_object* v_motiveBody_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Meta_getLevel(v_motiveBody_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0___boxed(lean_object* v_x_1173_, lean_object* v_motiveBody_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(v_x_1173_, v_motiveBody_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec_ref(v_x_1173_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(lean_object* v___x_1181_, lean_object* v___x_1182_, lean_object* v_alpha_1183_, uint8_t v___x_1184_, lean_object* v_xs_1185_, lean_object* v_x_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; uint8_t v___x_1196_; uint8_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1192_ = l_Lean_Level_ofNat(v___x_1181_);
v___x_1193_ = l_Lean_Expr_sort___override(v___x_1192_);
v___x_1194_ = l_Lean_Expr_forallE___override(v___x_1182_, v_alpha_1183_, v___x_1193_, v___x_1184_);
v___x_1195_ = 0;
v___x_1196_ = 1;
v___x_1197_ = 1;
v___x_1198_ = l_Lean_Meta_mkForallFVars(v_xs_1185_, v___x_1194_, v___x_1195_, v___x_1196_, v___x_1196_, v___x_1197_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed(lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v_alpha_1201_, lean_object* v___x_1202_, lean_object* v_xs_1203_, lean_object* v_x_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
uint8_t v___x_16634__boxed_1210_; lean_object* v_res_1211_; 
v___x_16634__boxed_1210_ = lean_unbox(v___x_1202_);
v_res_1211_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(v___x_1199_, v___x_1200_, v_alpha_1201_, v___x_16634__boxed_1210_, v_xs_1203_, v_x_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v_x_1204_);
lean_dec_ref(v_xs_1203_);
lean_dec(v___x_1199_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(lean_object* v___x_1218_, lean_object* v___x_1219_, lean_object* v_rel_1220_, lean_object* v___x_1221_, lean_object* v_beta_1222_, uint8_t v___x_1223_, lean_object* v_alpha_1224_, uint8_t v___x_1225_, lean_object* v_xs_1226_, lean_object* v_x_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1233_ = l_Lean_mkAppN(v___x_1218_, v_xs_1226_);
v___x_1234_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1235_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_xs_1226_);
v___x_1236_ = lean_array_push(v_xs_1226_, v___x_1219_);
v___x_1237_ = l_Lean_mkAppN(v_rel_1220_, v___x_1236_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = l_Lean_Expr_bvar___override(v___x_1221_);
v___x_1239_ = l_Lean_Expr_app___override(v_beta_1222_, v___x_1238_);
v___x_1240_ = l_Lean_Expr_forallE___override(v___x_1235_, v___x_1237_, v___x_1239_, v___x_1223_);
v___x_1241_ = l_Lean_Expr_forallE___override(v___x_1234_, v_alpha_1224_, v___x_1240_, v___x_1223_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
v___x_1242_ = l_Lean_mkArrow(v___x_1241_, v___x_1233_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; uint8_t v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref(v___x_1242_);
v___x_1244_ = 1;
v___x_1245_ = 1;
v___x_1246_ = l_Lean_Meta_mkLambdaFVars(v_xs_1226_, v_a_1243_, v___x_1225_, v___x_1244_, v___x_1225_, v___x_1244_, v___x_1245_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec_ref(v_xs_1226_);
return v___x_1246_;
}
else
{
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec_ref(v_xs_1226_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed(lean_object* v___x_1247_, lean_object* v___x_1248_, lean_object* v_rel_1249_, lean_object* v___x_1250_, lean_object* v_beta_1251_, lean_object* v___x_1252_, lean_object* v_alpha_1253_, lean_object* v___x_1254_, lean_object* v_xs_1255_, lean_object* v_x_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v___x_16688__boxed_1262_; uint8_t v___x_16689__boxed_1263_; lean_object* v_res_1264_; 
v___x_16688__boxed_1262_ = lean_unbox(v___x_1252_);
v___x_16689__boxed_1263_ = lean_unbox(v___x_1254_);
v_res_1264_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(v___x_1247_, v___x_1248_, v_rel_1249_, v___x_1250_, v_beta_1251_, v___x_16688__boxed_1262_, v_alpha_1253_, v___x_16689__boxed_1263_, v_xs_1255_, v_x_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec_ref(v_x_1256_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(lean_object* v___x_1265_, lean_object* v___x_1266_, lean_object* v_f_1267_, uint8_t v___x_1268_, uint8_t v___x_1269_, lean_object* v_ys_1270_, lean_object* v_x_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; 
v___x_1277_ = lean_array_get_borrowed(v___x_1265_, v_ys_1270_, v___x_1266_);
lean_inc(v___x_1277_);
v___x_1278_ = l_Lean_Expr_app___override(v_f_1267_, v___x_1277_);
v___x_1279_ = 1;
v___x_1280_ = l_Lean_Meta_mkLambdaFVars(v_ys_1270_, v___x_1278_, v___x_1268_, v___x_1269_, v___x_1268_, v___x_1269_, v___x_1279_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed(lean_object* v___x_1281_, lean_object* v___x_1282_, lean_object* v_f_1283_, lean_object* v___x_1284_, lean_object* v___x_1285_, lean_object* v_ys_1286_, lean_object* v_x_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
uint8_t v___x_16755__boxed_1293_; uint8_t v___x_16756__boxed_1294_; lean_object* v_res_1295_; 
v___x_16755__boxed_1293_ = lean_unbox(v___x_1284_);
v___x_16756__boxed_1294_ = lean_unbox(v___x_1285_);
v_res_1295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(v___x_1281_, v___x_1282_, v_f_1283_, v___x_16755__boxed_1293_, v___x_16756__boxed_1294_, v_ys_1286_, v_x_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec_ref(v_x_1287_);
lean_dec_ref(v_ys_1286_);
lean_dec(v___x_1282_);
return v_res_1295_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1));
v___x_1299_ = lean_unsigned_to_nat(10u);
v___x_1300_ = lean_unsigned_to_nat(145u);
v___x_1301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0));
v___x_1302_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_1303_ = l_mkPanicMessageWithDecl(v___x_1302_, v___x_1301_, v___x_1300_, v___x_1299_, v___x_1298_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(lean_object* v___x_1304_, lean_object* v___x_1305_, lean_object* v_f_1306_, uint8_t v___x_1307_, lean_object* v_a_1308_, lean_object* v_ys_1309_, lean_object* v_altBodyType_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v___x_1316_; 
v___x_1316_ = l_Lean_Expr_isForall(v_altBodyType_1310_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec_ref(v_ys_1309_);
lean_dec_ref(v_a_1308_);
lean_dec_ref(v_f_1306_);
lean_dec(v___x_1305_);
lean_dec_ref(v___x_1304_);
v___x_1317_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2);
v___x_1318_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v___x_1317_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1319_ = lean_box(v___x_1307_);
v___x_1320_ = lean_box(v___x_1316_);
v___f_1321_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1321_, 0, v___x_1304_);
lean_closure_set(v___f_1321_, 1, v___x_1305_);
lean_closure_set(v___f_1321_, 2, v_f_1306_);
lean_closure_set(v___f_1321_, 3, v___x_1319_);
lean_closure_set(v___f_1321_, 4, v___x_1320_);
v___x_1322_ = l_Lean_Expr_bindingDomain_x21(v_altBodyType_1310_);
v___x_1323_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
lean_inc(v___y_1314_);
lean_inc_ref(v___y_1313_);
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
v___x_1324_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_1322_, v___x_1323_, v___f_1321_, v___x_1307_, v___x_1307_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref(v___x_1324_);
lean_inc_ref(v_ys_1309_);
v___x_1326_ = lean_array_push(v_ys_1309_, v_a_1325_);
v___x_1327_ = l_Lean_mkAppN(v_a_1308_, v___x_1326_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = 1;
v___x_1329_ = l_Lean_Meta_mkLambdaFVars(v_ys_1309_, v___x_1327_, v___x_1307_, v___x_1316_, v___x_1307_, v___x_1316_, v___x_1328_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec_ref(v_ys_1309_);
return v___x_1329_;
}
else
{
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec_ref(v_ys_1309_);
lean_dec_ref(v_a_1308_);
return v___x_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed(lean_object* v___x_1330_, lean_object* v___x_1331_, lean_object* v_f_1332_, lean_object* v___x_1333_, lean_object* v_a_1334_, lean_object* v_ys_1335_, lean_object* v_altBodyType_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v___x_16812__boxed_1342_; lean_object* v_res_1343_; 
v___x_16812__boxed_1342_ = lean_unbox(v___x_1333_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(v___x_1330_, v___x_1331_, v_f_1332_, v___x_16812__boxed_1342_, v_a_1334_, v_ys_1335_, v_altBodyType_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec_ref(v_altBodyType_1336_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(lean_object* v_f_1344_, lean_object* v_as_1345_, size_t v_sz_1346_, size_t v_i_1347_, lean_object* v_b_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_usize_dec_lt(v_i_1347_, v_sz_1346_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec_ref(v_f_1344_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_b_1348_);
return v___x_1355_;
}
else
{
lean_object* v_snd_1356_; lean_object* v_fst_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1416_; 
v_snd_1356_ = lean_ctor_get(v_b_1348_, 1);
v_fst_1357_ = lean_ctor_get(v_b_1348_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_b_1348_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1359_ = v_b_1348_;
v_isShared_1360_ = v_isSharedCheck_1416_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_snd_1356_);
lean_inc(v_fst_1357_);
lean_dec(v_b_1348_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1416_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v_array_1361_; lean_object* v_start_1362_; lean_object* v_stop_1363_; uint8_t v___x_1364_; 
v_array_1361_ = lean_ctor_get(v_snd_1356_, 0);
v_start_1362_ = lean_ctor_get(v_snd_1356_, 1);
v_stop_1363_ = lean_ctor_get(v_snd_1356_, 2);
v___x_1364_ = lean_nat_dec_lt(v_start_1362_, v_stop_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1366_; 
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec_ref(v_f_1344_);
if (v_isShared_1360_ == 0)
{
v___x_1366_ = v___x_1359_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_fst_1357_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_snd_1356_);
v___x_1366_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
}
else
{
lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1412_; 
lean_inc(v_stop_1363_);
lean_inc(v_start_1362_);
lean_inc_ref(v_array_1361_);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_snd_1356_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; lean_object* v_unused_1414_; lean_object* v_unused_1415_; 
v_unused_1413_ = lean_ctor_get(v_snd_1356_, 2);
lean_dec(v_unused_1413_);
v_unused_1414_ = lean_ctor_get(v_snd_1356_, 1);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v_snd_1356_, 0);
lean_dec(v_unused_1415_);
v___x_1370_ = v_snd_1356_;
v_isShared_1371_ = v_isSharedCheck_1412_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v_snd_1356_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1412_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v_a_1372_; lean_object* v___x_1373_; 
v_a_1372_ = lean_array_uget_borrowed(v_as_1345_, v_i_1347_);
lean_inc(v___y_1352_);
lean_inc_ref(v___y_1351_);
lean_inc(v___y_1350_);
lean_inc_ref(v___y_1349_);
lean_inc(v_a_1372_);
v___x_1373_ = lean_infer_type(v_a_1372_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___f_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref(v___x_1373_);
v___x_1375_ = l_Lean_instInhabitedExpr;
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = 0;
v___x_1378_ = lean_box(v___x_1377_);
lean_inc(v_a_1372_);
lean_inc_ref(v_f_1344_);
v___f_1379_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed), 12, 5);
lean_closure_set(v___f_1379_, 0, v___x_1375_);
lean_closure_set(v___f_1379_, 1, v___x_1376_);
lean_closure_set(v___f_1379_, 2, v_f_1344_);
lean_closure_set(v___f_1379_, 3, v___x_1378_);
lean_closure_set(v___f_1379_, 4, v_a_1372_);
v___x_1380_ = lean_array_fget_borrowed(v_array_1361_, v_start_1362_);
lean_inc(v___x_1380_);
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_inc(v___y_1352_);
lean_inc_ref(v___y_1351_);
lean_inc(v___y_1350_);
lean_inc_ref(v___y_1349_);
v___x_1382_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1374_, v___x_1381_, v___f_1379_, v___x_1377_, v___x_1377_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_add(v_start_1362_, v___x_1384_);
lean_dec(v_start_1362_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v___x_1385_);
v___x_1387_ = v___x_1370_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_array_1361_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_stop_1363_);
v___x_1387_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = l_Lean_Expr_app___override(v_fst_1357_, v_a_1383_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v___x_1387_);
lean_ctor_set(v___x_1359_, 0, v___x_1388_);
v___x_1390_ = v___x_1359_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1387_);
v___x_1390_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
size_t v___x_1391_; size_t v___x_1392_; 
v___x_1391_ = ((size_t)1ULL);
v___x_1392_ = lean_usize_add(v_i_1347_, v___x_1391_);
v_i_1347_ = v___x_1392_;
v_b_1348_ = v___x_1390_;
goto _start;
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_del_object(v___x_1370_);
lean_dec(v_stop_1363_);
lean_dec(v_start_1362_);
lean_dec_ref(v_array_1361_);
lean_del_object(v___x_1359_);
lean_dec(v_fst_1357_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec_ref(v_f_1344_);
v_a_1396_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1382_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1382_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_del_object(v___x_1370_);
lean_dec(v_stop_1363_);
lean_dec(v_start_1362_);
lean_dec_ref(v_array_1361_);
lean_del_object(v___x_1359_);
lean_dec(v_fst_1357_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec_ref(v_f_1344_);
v_a_1404_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1373_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1373_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___boxed(lean_object* v_f_1417_, lean_object* v_as_1418_, lean_object* v_sz_1419_, lean_object* v_i_1420_, lean_object* v_b_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
size_t v_sz_boxed_1427_; size_t v_i_boxed_1428_; lean_object* v_res_1429_; 
v_sz_boxed_1427_ = lean_unbox_usize(v_sz_1419_);
lean_dec(v_sz_1419_);
v_i_boxed_1428_ = lean_unbox_usize(v_i_1420_);
lean_dec(v_i_1420_);
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1417_, v_as_1418_, v_sz_boxed_1427_, v_i_boxed_1428_, v_b_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec_ref(v_as_1418_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(lean_object* v_as_x27_1430_, lean_object* v_b_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
if (lean_obj_tag(v_as_x27_1430_) == 0)
{
lean_object* v___x_1437_; 
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_b_1431_);
return v___x_1437_;
}
else
{
lean_object* v_head_1438_; lean_object* v_tail_1439_; uint8_t v___x_1440_; lean_object* v___x_1441_; 
v_head_1438_ = lean_ctor_get(v_as_x27_1430_, 0);
lean_inc(v_head_1438_);
v_tail_1439_ = lean_ctor_get(v_as_x27_1430_, 1);
lean_inc(v_tail_1439_);
lean_dec_ref(v_as_x27_1430_);
v___x_1440_ = 1;
lean_inc(v___y_1435_);
lean_inc_ref(v___y_1434_);
lean_inc(v___y_1433_);
lean_inc_ref(v___y_1432_);
v___x_1441_ = l_Lean_MVarId_refl(v_head_1438_, v___x_1440_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v___x_1442_; 
lean_dec_ref(v___x_1441_);
v___x_1442_ = lean_box(0);
v_as_x27_1430_ = v_tail_1439_;
v_b_1431_ = v___x_1442_;
goto _start;
}
else
{
lean_dec(v_tail_1439_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
return v___x_1441_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg___boxed(lean_object* v_as_x27_1444_, lean_object* v_b_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_1444_, v_b_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(lean_object* v___x_1452_, lean_object* v_matcherInfo_1453_, lean_object* v___x_1454_, lean_object* v___x_1455_, lean_object* v_f_1456_, lean_object* v_discrs_1457_, lean_object* v___x_1458_, lean_object* v_rel_1459_, lean_object* v___x_1460_, uint8_t v___x_1461_, lean_object* v_alpha_1462_, lean_object* v___x_1463_, lean_object* v_beta_1464_, lean_object* v___x_1465_, uint8_t v___x_1466_, lean_object* v___x_1467_, lean_object* v___x_1468_, lean_object* v___x_1469_, lean_object* v_alts_1470_, lean_object* v_x_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; size_t v_sz_1482_; size_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1477_ = l_Lean_mkAppN(v___x_1452_, v_alts_1470_);
lean_inc_ref(v_matcherInfo_1453_);
v___x_1478_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_matcherInfo_1453_);
v___x_1479_ = lean_array_get_size(v___x_1478_);
v___x_1480_ = l_Array_toSubarray___redArg(v___x_1478_, v___x_1454_, v___x_1479_);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1455_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v_sz_1482_ = lean_array_size(v_alts_1470_);
v___x_1483_ = ((size_t)0ULL);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
lean_inc_ref(v_f_1456_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1456_, v_alts_1470_, v_sz_1482_, v___x_1483_, v___x_1481_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v_fst_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1580_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref(v___x_1484_);
v_fst_1486_ = lean_ctor_get(v_a_1485_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_a_1485_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v_a_1485_, 1);
lean_dec(v_unused_1581_);
v___x_1488_ = v_a_1485_;
v_isShared_1489_ = v_isSharedCheck_1580_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_fst_1486_);
lean_dec(v_a_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1580_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1490_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1491_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_discrs_1457_);
v___x_1492_ = lean_array_push(v_discrs_1457_, v___x_1458_);
lean_inc_ref(v_rel_1459_);
v___x_1493_ = l_Lean_mkAppN(v_rel_1459_, v___x_1492_);
lean_dec_ref(v___x_1492_);
v___x_1494_ = l_Lean_Expr_bvar___override(v___x_1460_);
lean_inc_ref(v_f_1456_);
v___x_1495_ = l_Lean_Expr_app___override(v_f_1456_, v___x_1494_);
v___x_1496_ = l_Lean_Expr_lam___override(v___x_1491_, v___x_1493_, v___x_1495_, v___x_1461_);
lean_inc_ref(v_alpha_1462_);
v___x_1497_ = l_Lean_Expr_lam___override(v___x_1490_, v_alpha_1462_, v___x_1496_, v___x_1461_);
v___x_1498_ = l_Lean_Expr_app___override(v___x_1477_, v___x_1497_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
lean_inc(v_fst_1486_);
v___x_1499_ = l_Lean_Meta_mkEq(v___x_1498_, v_fst_1486_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref(v___x_1499_);
v___x_1501_ = lean_box(0);
lean_inc_ref(v___y_1472_);
lean_inc(v_a_1500_);
v___x_1502_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1500_, v___x_1501_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref(v___x_1502_);
v___x_1504_ = l_Lean_Expr_mvarId_x21(v_a_1503_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
v___x_1505_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v___x_1504_, v_fst_1486_, v_matcherInfo_1453_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec_ref(v_matcherInfo_1453_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref(v___x_1505_);
v___x_1507_ = lean_box(0);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
v___x_1508_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_a_1506_, v___x_1507_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v___x_1509_; lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1555_; 
lean_dec_ref(v___x_1508_);
v___x_1509_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_1503_, v___y_1473_);
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1555_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1555_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
v___x_1514_ = lean_unsigned_to_nat(5u);
v___x_1515_ = lean_mk_empty_array_with_capacity(v___x_1514_);
v___x_1516_ = lean_array_push(v___x_1515_, v___x_1463_);
v___x_1517_ = lean_array_push(v___x_1516_, v_alpha_1462_);
v___x_1518_ = lean_array_push(v___x_1517_, v_beta_1464_);
v___x_1519_ = lean_array_push(v___x_1518_, v_f_1456_);
v___x_1520_ = lean_array_push(v___x_1519_, v_rel_1459_);
v___x_1521_ = l_Array_append___redArg(v___x_1465_, v___x_1520_);
lean_dec_ref(v___x_1520_);
v___x_1522_ = l_Array_append___redArg(v___x_1521_, v_discrs_1457_);
lean_dec_ref(v_discrs_1457_);
v___x_1523_ = l_Array_append___redArg(v___x_1522_, v_alts_1470_);
v___x_1524_ = 1;
v___x_1525_ = 1;
v___x_1526_ = l_Lean_Meta_mkForallFVars(v___x_1523_, v_a_1500_, v___x_1466_, v___x_1524_, v___x_1524_, v___x_1525_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1526_);
v___x_1528_ = l_Lean_Meta_mkLambdaFVars(v___x_1523_, v_a_1510_, v___x_1466_, v___x_1524_, v___x_1466_, v___x_1524_, v___x_1525_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec_ref(v___x_1523_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref(v___x_1528_);
lean_inc(v___x_1467_);
v___x_1530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1467_);
lean_ctor_set(v___x_1530_, 1, v___x_1468_);
lean_ctor_set(v___x_1530_, 2, v_a_1527_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set_tag(v___x_1488_, 1);
lean_ctor_set(v___x_1488_, 1, v___x_1469_);
lean_ctor_set(v___x_1488_, 0, v___x_1467_);
v___x_1532_ = v___x_1488_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___x_1469_);
v___x_1532_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1530_);
lean_ctor_set(v___x_1533_, 1, v_a_1529_);
lean_ctor_set(v___x_1533_, 2, v___x_1532_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set_tag(v___x_1512_, 2);
lean_ctor_set(v___x_1512_, 0, v___x_1533_);
v___x_1535_ = v___x_1512_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_addDecl(v___x_1535_, v___x_1466_, v___y_1474_, v___y_1475_);
return v___x_1536_;
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_a_1527_);
lean_del_object(v___x_1512_);
lean_del_object(v___x_1488_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___x_1469_);
lean_dec(v___x_1468_);
lean_dec(v___x_1467_);
v_a_1539_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1528_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1528_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v___x_1523_);
lean_del_object(v___x_1512_);
lean_dec(v_a_1510_);
lean_del_object(v___x_1488_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___x_1469_);
lean_dec(v___x_1468_);
lean_dec(v___x_1467_);
v_a_1547_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1526_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1526_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
else
{
lean_dec(v_a_1503_);
lean_dec(v_a_1500_);
lean_del_object(v___x_1488_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___x_1469_);
lean_dec(v___x_1468_);
lean_dec(v___x_1467_);
lean_dec_ref(v___x_1465_);
lean_dec_ref(v_beta_1464_);
lean_dec_ref(v___x_1463_);
lean_dec_ref(v_alpha_1462_);
lean_dec_ref(v_rel_1459_);
lean_dec_ref(v_discrs_1457_);
lean_dec_ref(v_f_1456_);
return v___x_1508_;
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_a_1503_);
lean_dec(v_a_1500_);
lean_del_object(v___x_1488_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___x_1469_);
lean_dec(v___x_1468_);
lean_dec(v___x_1467_);
lean_dec_ref(v___x_1465_);
lean_dec_ref(v_beta_1464_);
lean_dec_ref(v___x_1463_);
lean_dec_ref(v_alpha_1462_);
lean_dec_ref(v_rel_1459_);
lean_dec_ref(v_discrs_1457_);
lean_dec_ref(v_f_1456_);
v_a_1556_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1505_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1505_);
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
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_a_1500_);
lean_del_object(v___x_1488_);
lean_dec(v_fst_1486_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___x_1469_);
lean_dec(v___x_1468_);
lean_dec(v___x_1467_);
lean_dec_ref(v___x_1465_);
lean_dec_ref(v_beta_1464_);
lean_dec_ref(v___x_1463_);
lean_dec_ref(v_alpha_1462_);
lean_dec_ref(v_rel_1459_);
lean_dec_ref(v_discrs_1457_);
lean_dec_ref(v_f_1456_);
lean_dec_ref(v_matcherInfo_1453_);
v_a_1564_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1502_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1502_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_del_object(v___x_1488_);
lean_dec(v_fst_1486_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___x_1469_);
lean_dec(v___x_1468_);
lean_dec(v___x_1467_);
lean_dec_ref(v___x_1465_);
lean_dec_ref(v_beta_1464_);
lean_dec_ref(v___x_1463_);
lean_dec_ref(v_alpha_1462_);
lean_dec_ref(v_rel_1459_);
lean_dec_ref(v_discrs_1457_);
lean_dec_ref(v_f_1456_);
lean_dec_ref(v_matcherInfo_1453_);
v_a_1572_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1499_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1499_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v___x_1477_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___x_1469_);
lean_dec(v___x_1468_);
lean_dec(v___x_1467_);
lean_dec_ref(v___x_1465_);
lean_dec_ref(v_beta_1464_);
lean_dec_ref(v___x_1463_);
lean_dec_ref(v_alpha_1462_);
lean_dec(v___x_1460_);
lean_dec_ref(v_rel_1459_);
lean_dec_ref(v___x_1458_);
lean_dec_ref(v_discrs_1457_);
lean_dec_ref(v_f_1456_);
lean_dec_ref(v_matcherInfo_1453_);
v_a_1582_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1484_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1484_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed(lean_object** _args){
lean_object* v___x_1590_ = _args[0];
lean_object* v_matcherInfo_1591_ = _args[1];
lean_object* v___x_1592_ = _args[2];
lean_object* v___x_1593_ = _args[3];
lean_object* v_f_1594_ = _args[4];
lean_object* v_discrs_1595_ = _args[5];
lean_object* v___x_1596_ = _args[6];
lean_object* v_rel_1597_ = _args[7];
lean_object* v___x_1598_ = _args[8];
lean_object* v___x_1599_ = _args[9];
lean_object* v_alpha_1600_ = _args[10];
lean_object* v___x_1601_ = _args[11];
lean_object* v_beta_1602_ = _args[12];
lean_object* v___x_1603_ = _args[13];
lean_object* v___x_1604_ = _args[14];
lean_object* v___x_1605_ = _args[15];
lean_object* v___x_1606_ = _args[16];
lean_object* v___x_1607_ = _args[17];
lean_object* v_alts_1608_ = _args[18];
lean_object* v_x_1609_ = _args[19];
lean_object* v___y_1610_ = _args[20];
lean_object* v___y_1611_ = _args[21];
lean_object* v___y_1612_ = _args[22];
lean_object* v___y_1613_ = _args[23];
lean_object* v___y_1614_ = _args[24];
_start:
{
uint8_t v___x_17042__boxed_1615_; uint8_t v___x_17045__boxed_1616_; lean_object* v_res_1617_; 
v___x_17042__boxed_1615_ = lean_unbox(v___x_1599_);
v___x_17045__boxed_1616_ = lean_unbox(v___x_1604_);
v_res_1617_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(v___x_1590_, v_matcherInfo_1591_, v___x_1592_, v___x_1593_, v_f_1594_, v_discrs_1595_, v___x_1596_, v_rel_1597_, v___x_1598_, v___x_17042__boxed_1615_, v_alpha_1600_, v___x_1601_, v_beta_1602_, v___x_1603_, v___x_17045__boxed_1616_, v___x_1605_, v___x_1606_, v___x_1607_, v_alts_1608_, v_x_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec_ref(v_x_1609_);
lean_dec_ref(v_alts_1608_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(lean_object* v___x_1618_, lean_object* v___x_1619_, lean_object* v_matcherInfo_1620_, lean_object* v___x_1621_, lean_object* v_f_1622_, lean_object* v___x_1623_, lean_object* v_rel_1624_, lean_object* v___x_1625_, uint8_t v___x_1626_, lean_object* v_alpha_1627_, lean_object* v___x_1628_, lean_object* v_beta_1629_, lean_object* v___x_1630_, uint8_t v___x_1631_, lean_object* v___x_1632_, lean_object* v___x_1633_, lean_object* v___x_1634_, lean_object* v_discrs_1635_, lean_object* v_x_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = l_Lean_mkAppN(v___x_1618_, v_discrs_1635_);
lean_inc(v___y_1640_);
lean_inc_ref(v___y_1639_);
lean_inc(v___y_1638_);
lean_inc_ref(v___y_1637_);
lean_inc_ref(v___x_1642_);
v___x_1643_ = lean_infer_type(v___x_1642_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___f_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref(v___x_1643_);
v___x_1645_ = l_Lean_mkAppN(v___x_1619_, v_discrs_1635_);
v___x_1646_ = lean_box(v___x_1626_);
v___x_1647_ = lean_box(v___x_1631_);
lean_inc_ref(v_matcherInfo_1620_);
v___f_1648_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1648_, 0, v___x_1642_);
lean_closure_set(v___f_1648_, 1, v_matcherInfo_1620_);
lean_closure_set(v___f_1648_, 2, v___x_1621_);
lean_closure_set(v___f_1648_, 3, v___x_1645_);
lean_closure_set(v___f_1648_, 4, v_f_1622_);
lean_closure_set(v___f_1648_, 5, v_discrs_1635_);
lean_closure_set(v___f_1648_, 6, v___x_1623_);
lean_closure_set(v___f_1648_, 7, v_rel_1624_);
lean_closure_set(v___f_1648_, 8, v___x_1625_);
lean_closure_set(v___f_1648_, 9, v___x_1646_);
lean_closure_set(v___f_1648_, 10, v_alpha_1627_);
lean_closure_set(v___f_1648_, 11, v___x_1628_);
lean_closure_set(v___f_1648_, 12, v_beta_1629_);
lean_closure_set(v___f_1648_, 13, v___x_1630_);
lean_closure_set(v___f_1648_, 14, v___x_1647_);
lean_closure_set(v___f_1648_, 15, v___x_1632_);
lean_closure_set(v___f_1648_, 16, v___x_1633_);
lean_closure_set(v___f_1648_, 17, v___x_1634_);
v___x_1649_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_matcherInfo_1620_);
lean_dec_ref(v_matcherInfo_1620_);
v___x_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
v___x_1651_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1644_, v___x_1650_, v___f_1648_, v___x_1631_, v___x_1631_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
return v___x_1651_;
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___x_1642_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec_ref(v_discrs_1635_);
lean_dec(v___x_1634_);
lean_dec(v___x_1633_);
lean_dec(v___x_1632_);
lean_dec_ref(v___x_1630_);
lean_dec_ref(v_beta_1629_);
lean_dec_ref(v___x_1628_);
lean_dec_ref(v_alpha_1627_);
lean_dec(v___x_1625_);
lean_dec_ref(v_rel_1624_);
lean_dec_ref(v___x_1623_);
lean_dec_ref(v_f_1622_);
lean_dec(v___x_1621_);
lean_dec_ref(v_matcherInfo_1620_);
lean_dec_ref(v___x_1619_);
v_a_1652_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1643_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1643_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed(lean_object** _args){
lean_object* v___x_1660_ = _args[0];
lean_object* v___x_1661_ = _args[1];
lean_object* v_matcherInfo_1662_ = _args[2];
lean_object* v___x_1663_ = _args[3];
lean_object* v_f_1664_ = _args[4];
lean_object* v___x_1665_ = _args[5];
lean_object* v_rel_1666_ = _args[6];
lean_object* v___x_1667_ = _args[7];
lean_object* v___x_1668_ = _args[8];
lean_object* v_alpha_1669_ = _args[9];
lean_object* v___x_1670_ = _args[10];
lean_object* v_beta_1671_ = _args[11];
lean_object* v___x_1672_ = _args[12];
lean_object* v___x_1673_ = _args[13];
lean_object* v___x_1674_ = _args[14];
lean_object* v___x_1675_ = _args[15];
lean_object* v___x_1676_ = _args[16];
lean_object* v_discrs_1677_ = _args[17];
lean_object* v_x_1678_ = _args[18];
lean_object* v___y_1679_ = _args[19];
lean_object* v___y_1680_ = _args[20];
lean_object* v___y_1681_ = _args[21];
lean_object* v___y_1682_ = _args[22];
lean_object* v___y_1683_ = _args[23];
_start:
{
uint8_t v___x_17323__boxed_1684_; uint8_t v___x_17326__boxed_1685_; lean_object* v_res_1686_; 
v___x_17323__boxed_1684_ = lean_unbox(v___x_1668_);
v___x_17326__boxed_1685_ = lean_unbox(v___x_1673_);
v_res_1686_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(v___x_1660_, v___x_1661_, v_matcherInfo_1662_, v___x_1663_, v_f_1664_, v___x_1665_, v_rel_1666_, v___x_1667_, v___x_17323__boxed_1684_, v_alpha_1669_, v___x_1670_, v_beta_1671_, v___x_1672_, v___x_17326__boxed_1685_, v___x_1674_, v___x_1675_, v___x_1676_, v_discrs_1677_, v_x_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec_ref(v_x_1678_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
if (lean_obj_tag(v_a_1687_) == 0)
{
lean_object* v___x_1689_; 
v___x_1689_ = l_List_reverse___redArg(v_a_1688_);
return v___x_1689_;
}
else
{
lean_object* v_head_1690_; lean_object* v_tail_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1700_; 
v_head_1690_ = lean_ctor_get(v_a_1687_, 0);
v_tail_1691_ = lean_ctor_get(v_a_1687_, 1);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_a_1687_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1693_ = v_a_1687_;
v_isShared_1694_ = v_isSharedCheck_1700_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_tail_1691_);
lean_inc(v_head_1690_);
lean_dec(v_a_1687_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1700_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = l_Lean_mkLevelParam(v_head_1690_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 1, v_a_1688_);
lean_ctor_set(v___x_1693_, 0, v___x_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_a_1688_);
v___x_1697_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
v_a_1687_ = v_tail_1691_;
v_a_1688_ = v___x_1697_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__0));
v___x_1703_ = l_Lean_stringToMessageData(v___x_1702_);
return v___x_1703_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__2));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(lean_object* v___x_1707_, lean_object* v___x_1708_, lean_object* v___x_1709_, lean_object* v_beta_1710_, uint8_t v___x_1711_, lean_object* v_alpha_1712_, uint8_t v___x_1713_, lean_object* v_numDiscrs_1714_, lean_object* v___f_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_levelParams_1718_, lean_object* v_matcherName_1719_, lean_object* v___x_1720_, lean_object* v_matcherInfo_1721_, lean_object* v___x_1722_, lean_object* v_f_1723_, lean_object* v___x_1724_, lean_object* v_uElimPos_x3f_1725_, lean_object* v_rel_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
lean_inc(v___y_1730_);
lean_inc_ref(v___y_1729_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1727_);
lean_inc_ref(v___x_1707_);
v___x_1732_ = lean_infer_type(v___x_1707_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___f_1736_; lean_object* v___x_1737_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = lean_box(v___x_1711_);
v___x_1735_ = lean_box(v___x_1713_);
lean_inc_ref(v_alpha_1712_);
lean_inc_ref(v_beta_1710_);
lean_inc(v___x_1709_);
lean_inc_ref(v_rel_1726_);
lean_inc_ref(v___x_1708_);
lean_inc_ref(v___x_1707_);
v___f_1736_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed), 15, 8);
lean_closure_set(v___f_1736_, 0, v___x_1707_);
lean_closure_set(v___f_1736_, 1, v___x_1708_);
lean_closure_set(v___f_1736_, 2, v_rel_1726_);
lean_closure_set(v___f_1736_, 3, v___x_1709_);
lean_closure_set(v___f_1736_, 4, v_beta_1710_);
lean_closure_set(v___f_1736_, 5, v___x_1734_);
lean_closure_set(v___f_1736_, 6, v_alpha_1712_);
lean_closure_set(v___f_1736_, 7, v___x_1735_);
lean_inc(v___y_1730_);
lean_inc_ref(v___y_1729_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1727_);
v___x_1737_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1733_, v___f_1736_, v___x_1713_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1739_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref(v___x_1737_);
lean_inc(v___y_1730_);
lean_inc_ref(v___y_1729_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1727_);
lean_inc(v_numDiscrs_1714_);
lean_inc(v_a_1738_);
v___x_1739_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_a_1738_, v_numDiscrs_1714_, v___f_1715_, v___x_1713_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v_matcherLevels_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref(v___x_1739_);
v___x_1741_ = lean_box(0);
v___x_1742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1742_, 0, v_a_1716_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_a_1717_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
lean_inc(v_levelParams_1718_);
v___x_1744_ = l_List_appendTR___redArg(v_levelParams_1718_, v___x_1743_);
v___x_1745_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_1718_, v___x_1741_);
if (lean_obj_tag(v_uElimPos_x3f_1725_) == 0)
{
uint8_t v___x_1774_; 
v___x_1774_ = l_Lean_Level_isZero(v_a_1740_);
lean_dec(v_a_1740_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v___x_1745_);
lean_dec(v___x_1744_);
lean_dec(v_a_1738_);
lean_dec_ref(v_rel_1726_);
lean_dec(v___x_1724_);
lean_dec_ref(v_f_1723_);
lean_dec(v___x_1722_);
lean_dec_ref(v_matcherInfo_1721_);
lean_dec_ref(v___x_1720_);
lean_dec(v_numDiscrs_1714_);
lean_dec_ref(v_alpha_1712_);
lean_dec_ref(v_beta_1710_);
lean_dec(v___x_1709_);
lean_dec_ref(v___x_1708_);
lean_dec_ref(v___x_1707_);
v___x_1775_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1);
v___x_1776_ = l_Lean_MessageData_ofConstName(v_matcherName_1719_, v___x_1713_);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_1779_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
return v___x_1780_;
}
else
{
lean_inc(v___x_1745_);
v_matcherLevels_1747_ = v___x_1745_;
v___y_1748_ = v___y_1727_;
v___y_1749_ = v___y_1728_;
v___y_1750_ = v___y_1729_;
v___y_1751_ = v___y_1730_;
goto v___jp_1746_;
}
}
else
{
lean_object* v_val_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_val_1781_ = lean_ctor_get(v_uElimPos_x3f_1725_, 0);
lean_inc(v___x_1745_);
v___x_1782_ = lean_array_mk(v___x_1745_);
v___x_1783_ = lean_array_set(v___x_1782_, v_val_1781_, v_a_1740_);
v___x_1784_ = lean_array_to_list(v___x_1783_);
v_matcherLevels_1747_ = v___x_1784_;
v___y_1748_ = v___y_1727_;
v___y_1749_ = v___y_1728_;
v___y_1750_ = v___y_1729_;
v___y_1751_ = v___y_1730_;
goto v___jp_1746_;
}
v___jp_1746_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_inc(v_matcherName_1719_);
v___x_1752_ = l_Lean_Expr_const___override(v_matcherName_1719_, v_matcherLevels_1747_);
v___x_1753_ = l_Subarray_copy___redArg(v___x_1720_);
v___x_1754_ = l_Lean_mkAppN(v___x_1752_, v___x_1753_);
v___x_1755_ = l_Lean_Expr_app___override(v___x_1754_, v_a_1738_);
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
lean_inc_ref(v___x_1755_);
v___x_1756_ = lean_infer_type(v___x_1755_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = l_Lean_Expr_const___override(v_matcherName_1719_, v___x_1745_);
v___x_1759_ = l_Lean_mkAppN(v___x_1758_, v___x_1753_);
lean_inc_ref(v___x_1707_);
v___x_1760_ = l_Lean_Expr_app___override(v___x_1759_, v___x_1707_);
v___x_1761_ = lean_box(v___x_1711_);
v___x_1762_ = lean_box(v___x_1713_);
v___f_1763_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed), 24, 17);
lean_closure_set(v___f_1763_, 0, v___x_1755_);
lean_closure_set(v___f_1763_, 1, v___x_1760_);
lean_closure_set(v___f_1763_, 2, v_matcherInfo_1721_);
lean_closure_set(v___f_1763_, 3, v___x_1722_);
lean_closure_set(v___f_1763_, 4, v_f_1723_);
lean_closure_set(v___f_1763_, 5, v___x_1708_);
lean_closure_set(v___f_1763_, 6, v_rel_1726_);
lean_closure_set(v___f_1763_, 7, v___x_1709_);
lean_closure_set(v___f_1763_, 8, v___x_1761_);
lean_closure_set(v___f_1763_, 9, v_alpha_1712_);
lean_closure_set(v___f_1763_, 10, v___x_1707_);
lean_closure_set(v___f_1763_, 11, v_beta_1710_);
lean_closure_set(v___f_1763_, 12, v___x_1753_);
lean_closure_set(v___f_1763_, 13, v___x_1762_);
lean_closure_set(v___f_1763_, 14, v___x_1724_);
lean_closure_set(v___f_1763_, 15, v___x_1744_);
lean_closure_set(v___f_1763_, 16, v___x_1741_);
v___x_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_numDiscrs_1714_);
v___x_1765_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1757_, v___x_1764_, v___f_1763_, v___x_1713_, v___x_1713_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
return v___x_1765_;
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec_ref(v___x_1755_);
lean_dec_ref(v___x_1753_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___x_1745_);
lean_dec(v___x_1744_);
lean_dec_ref(v_rel_1726_);
lean_dec(v___x_1724_);
lean_dec_ref(v_f_1723_);
lean_dec(v___x_1722_);
lean_dec_ref(v_matcherInfo_1721_);
lean_dec(v_matcherName_1719_);
lean_dec(v_numDiscrs_1714_);
lean_dec_ref(v_alpha_1712_);
lean_dec_ref(v_beta_1710_);
lean_dec(v___x_1709_);
lean_dec_ref(v___x_1708_);
lean_dec_ref(v___x_1707_);
v_a_1766_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1756_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1756_);
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
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_a_1738_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v_rel_1726_);
lean_dec(v___x_1724_);
lean_dec_ref(v_f_1723_);
lean_dec(v___x_1722_);
lean_dec_ref(v_matcherInfo_1721_);
lean_dec_ref(v___x_1720_);
lean_dec(v_matcherName_1719_);
lean_dec(v_levelParams_1718_);
lean_dec(v_a_1717_);
lean_dec(v_a_1716_);
lean_dec(v_numDiscrs_1714_);
lean_dec_ref(v_alpha_1712_);
lean_dec_ref(v_beta_1710_);
lean_dec(v___x_1709_);
lean_dec_ref(v___x_1708_);
lean_dec_ref(v___x_1707_);
v_a_1785_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1739_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1739_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v_rel_1726_);
lean_dec(v___x_1724_);
lean_dec_ref(v_f_1723_);
lean_dec(v___x_1722_);
lean_dec_ref(v_matcherInfo_1721_);
lean_dec_ref(v___x_1720_);
lean_dec(v_matcherName_1719_);
lean_dec(v_levelParams_1718_);
lean_dec(v_a_1717_);
lean_dec(v_a_1716_);
lean_dec_ref(v___f_1715_);
lean_dec(v_numDiscrs_1714_);
lean_dec_ref(v_alpha_1712_);
lean_dec_ref(v_beta_1710_);
lean_dec(v___x_1709_);
lean_dec_ref(v___x_1708_);
lean_dec_ref(v___x_1707_);
v_a_1793_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1737_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1737_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v_rel_1726_);
lean_dec(v___x_1724_);
lean_dec_ref(v_f_1723_);
lean_dec(v___x_1722_);
lean_dec_ref(v_matcherInfo_1721_);
lean_dec_ref(v___x_1720_);
lean_dec(v_matcherName_1719_);
lean_dec(v_levelParams_1718_);
lean_dec(v_a_1717_);
lean_dec(v_a_1716_);
lean_dec_ref(v___f_1715_);
lean_dec(v_numDiscrs_1714_);
lean_dec_ref(v_alpha_1712_);
lean_dec_ref(v_beta_1710_);
lean_dec(v___x_1709_);
lean_dec_ref(v___x_1708_);
lean_dec_ref(v___x_1707_);
v_a_1801_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1732_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1732_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed(lean_object** _args){
lean_object* v___x_1809_ = _args[0];
lean_object* v___x_1810_ = _args[1];
lean_object* v___x_1811_ = _args[2];
lean_object* v_beta_1812_ = _args[3];
lean_object* v___x_1813_ = _args[4];
lean_object* v_alpha_1814_ = _args[5];
lean_object* v___x_1815_ = _args[6];
lean_object* v_numDiscrs_1816_ = _args[7];
lean_object* v___f_1817_ = _args[8];
lean_object* v_a_1818_ = _args[9];
lean_object* v_a_1819_ = _args[10];
lean_object* v_levelParams_1820_ = _args[11];
lean_object* v_matcherName_1821_ = _args[12];
lean_object* v___x_1822_ = _args[13];
lean_object* v_matcherInfo_1823_ = _args[14];
lean_object* v___x_1824_ = _args[15];
lean_object* v_f_1825_ = _args[16];
lean_object* v___x_1826_ = _args[17];
lean_object* v_uElimPos_x3f_1827_ = _args[18];
lean_object* v_rel_1828_ = _args[19];
lean_object* v___y_1829_ = _args[20];
lean_object* v___y_1830_ = _args[21];
lean_object* v___y_1831_ = _args[22];
lean_object* v___y_1832_ = _args[23];
lean_object* v___y_1833_ = _args[24];
_start:
{
uint8_t v___x_17451__boxed_1834_; uint8_t v___x_17452__boxed_1835_; lean_object* v_res_1836_; 
v___x_17451__boxed_1834_ = lean_unbox(v___x_1813_);
v___x_17452__boxed_1835_ = lean_unbox(v___x_1815_);
v_res_1836_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(v___x_1809_, v___x_1810_, v___x_1811_, v_beta_1812_, v___x_17451__boxed_1834_, v_alpha_1814_, v___x_17452__boxed_1835_, v_numDiscrs_1816_, v___f_1817_, v_a_1818_, v_a_1819_, v_levelParams_1820_, v_matcherName_1821_, v___x_1822_, v_matcherInfo_1823_, v___x_1824_, v_f_1825_, v___x_1826_, v_uElimPos_x3f_1827_, v_rel_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v_uElimPos_x3f_1827_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(lean_object* v_k_1837_, lean_object* v_b_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_apply_6(v_k_1837_, v_b_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, lean_box(0));
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v_k_1845_, lean_object* v_b_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(v_k_1845_, v_b_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(lean_object* v_name_1853_, uint8_t v_bi_1854_, lean_object* v_type_1855_, lean_object* v_k_1856_, uint8_t v_kind_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___f_1863_; lean_object* v___x_1864_; 
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1863_, 0, v_k_1856_);
v___x_1864_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1853_, v_bi_1854_, v_type_1855_, v___f_1863_, v_kind_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
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
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_a_1873_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1864_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1864_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___boxed(lean_object* v_name_1881_, lean_object* v_bi_1882_, lean_object* v_type_1883_, lean_object* v_k_1884_, lean_object* v_kind_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
uint8_t v_bi_boxed_1891_; uint8_t v_kind_boxed_1892_; lean_object* v_res_1893_; 
v_bi_boxed_1891_ = lean_unbox(v_bi_1882_);
v_kind_boxed_1892_ = lean_unbox(v_kind_1885_);
v_res_1893_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1881_, v_bi_boxed_1891_, v_type_1883_, v_k_1884_, v_kind_boxed_1892_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(lean_object* v_name_1894_, lean_object* v_type_1895_, lean_object* v_k_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
uint8_t v___x_1902_; uint8_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = 0;
v___x_1903_ = 0;
v___x_1904_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1894_, v___x_1902_, v_type_1895_, v_k_1896_, v___x_1903_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg___boxed(lean_object* v_name_1905_, lean_object* v_type_1906_, lean_object* v_k_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_1905_, v_type_1906_, v_k_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(lean_object* v___x_1917_, lean_object* v___f_1918_, lean_object* v___x_1919_, lean_object* v___x_1920_, lean_object* v_beta_1921_, uint8_t v___x_1922_, lean_object* v_alpha_1923_, lean_object* v_numDiscrs_1924_, lean_object* v___f_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_levelParams_1928_, lean_object* v_matcherName_1929_, lean_object* v___x_1930_, lean_object* v_matcherInfo_1931_, lean_object* v___x_1932_, lean_object* v___x_1933_, lean_object* v_uElimPos_x3f_1934_, lean_object* v_f_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; 
lean_inc(v___y_1939_);
lean_inc_ref(v___y_1938_);
lean_inc(v___y_1937_);
lean_inc_ref(v___y_1936_);
lean_inc_ref(v___x_1917_);
v___x_1941_ = lean_infer_type(v___x_1917_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1941_);
v___x_1943_ = 0;
lean_inc(v___y_1939_);
lean_inc_ref(v___y_1938_);
lean_inc(v___y_1937_);
lean_inc_ref(v___y_1936_);
v___x_1944_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1942_, v___f_1918_, v___x_1943_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref(v___x_1944_);
v___x_1946_ = lean_box(v___x_1922_);
v___x_1947_ = lean_box(v___x_1943_);
v___f_1948_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed), 25, 19);
lean_closure_set(v___f_1948_, 0, v___x_1917_);
lean_closure_set(v___f_1948_, 1, v___x_1919_);
lean_closure_set(v___f_1948_, 2, v___x_1920_);
lean_closure_set(v___f_1948_, 3, v_beta_1921_);
lean_closure_set(v___f_1948_, 4, v___x_1946_);
lean_closure_set(v___f_1948_, 5, v_alpha_1923_);
lean_closure_set(v___f_1948_, 6, v___x_1947_);
lean_closure_set(v___f_1948_, 7, v_numDiscrs_1924_);
lean_closure_set(v___f_1948_, 8, v___f_1925_);
lean_closure_set(v___f_1948_, 9, v_a_1926_);
lean_closure_set(v___f_1948_, 10, v_a_1927_);
lean_closure_set(v___f_1948_, 11, v_levelParams_1928_);
lean_closure_set(v___f_1948_, 12, v_matcherName_1929_);
lean_closure_set(v___f_1948_, 13, v___x_1930_);
lean_closure_set(v___f_1948_, 14, v_matcherInfo_1931_);
lean_closure_set(v___f_1948_, 15, v___x_1932_);
lean_closure_set(v___f_1948_, 16, v_f_1935_);
lean_closure_set(v___f_1948_, 17, v___x_1933_);
lean_closure_set(v___f_1948_, 18, v_uElimPos_x3f_1934_);
v___x_1949_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__1));
v___x_1950_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_1949_, v_a_1945_, v___f_1948_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
return v___x_1950_;
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec_ref(v_f_1935_);
lean_dec(v_uElimPos_x3f_1934_);
lean_dec(v___x_1933_);
lean_dec(v___x_1932_);
lean_dec_ref(v_matcherInfo_1931_);
lean_dec_ref(v___x_1930_);
lean_dec(v_matcherName_1929_);
lean_dec(v_levelParams_1928_);
lean_dec(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v___f_1925_);
lean_dec(v_numDiscrs_1924_);
lean_dec_ref(v_alpha_1923_);
lean_dec_ref(v_beta_1921_);
lean_dec(v___x_1920_);
lean_dec_ref(v___x_1919_);
lean_dec_ref(v___x_1917_);
v_a_1951_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1944_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1944_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec_ref(v_f_1935_);
lean_dec(v_uElimPos_x3f_1934_);
lean_dec(v___x_1933_);
lean_dec(v___x_1932_);
lean_dec_ref(v_matcherInfo_1931_);
lean_dec_ref(v___x_1930_);
lean_dec(v_matcherName_1929_);
lean_dec(v_levelParams_1928_);
lean_dec(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v___f_1925_);
lean_dec(v_numDiscrs_1924_);
lean_dec_ref(v_alpha_1923_);
lean_dec_ref(v_beta_1921_);
lean_dec(v___x_1920_);
lean_dec_ref(v___x_1919_);
lean_dec_ref(v___f_1918_);
lean_dec_ref(v___x_1917_);
v_a_1959_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1941_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1941_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed(lean_object** _args){
lean_object* v___x_1967_ = _args[0];
lean_object* v___f_1968_ = _args[1];
lean_object* v___x_1969_ = _args[2];
lean_object* v___x_1970_ = _args[3];
lean_object* v_beta_1971_ = _args[4];
lean_object* v___x_1972_ = _args[5];
lean_object* v_alpha_1973_ = _args[6];
lean_object* v_numDiscrs_1974_ = _args[7];
lean_object* v___f_1975_ = _args[8];
lean_object* v_a_1976_ = _args[9];
lean_object* v_a_1977_ = _args[10];
lean_object* v_levelParams_1978_ = _args[11];
lean_object* v_matcherName_1979_ = _args[12];
lean_object* v___x_1980_ = _args[13];
lean_object* v_matcherInfo_1981_ = _args[14];
lean_object* v___x_1982_ = _args[15];
lean_object* v___x_1983_ = _args[16];
lean_object* v_uElimPos_x3f_1984_ = _args[17];
lean_object* v_f_1985_ = _args[18];
lean_object* v___y_1986_ = _args[19];
lean_object* v___y_1987_ = _args[20];
lean_object* v___y_1988_ = _args[21];
lean_object* v___y_1989_ = _args[22];
lean_object* v___y_1990_ = _args[23];
_start:
{
uint8_t v___x_17755__boxed_1991_; lean_object* v_res_1992_; 
v___x_17755__boxed_1991_ = lean_unbox(v___x_1972_);
v_res_1992_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(v___x_1967_, v___f_1968_, v___x_1969_, v___x_1970_, v_beta_1971_, v___x_17755__boxed_1991_, v_alpha_1973_, v_numDiscrs_1974_, v___f_1975_, v_a_1976_, v_a_1977_, v_levelParams_1978_, v_matcherName_1979_, v___x_1980_, v_matcherInfo_1981_, v___x_1982_, v___x_1983_, v_uElimPos_x3f_1984_, v_f_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(lean_object* v___x_1999_, lean_object* v_alpha_2000_, lean_object* v___x_2001_, lean_object* v___x_2002_, lean_object* v_numDiscrs_2003_, lean_object* v___f_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_levelParams_2007_, lean_object* v_matcherName_2008_, lean_object* v___x_2009_, lean_object* v_matcherInfo_2010_, lean_object* v___x_2011_, lean_object* v_uElimPos_x3f_2012_, lean_object* v_beta_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; lean_object* v___f_2025_; lean_object* v___x_2026_; lean_object* v___f_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__1));
v___x_2020_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__3));
lean_inc(v___x_1999_);
v___x_2021_ = l_Lean_Expr_bvar___override(v___x_1999_);
lean_inc_ref(v___x_2021_);
lean_inc_ref(v_beta_2013_);
v___x_2022_ = l_Lean_Expr_app___override(v_beta_2013_, v___x_2021_);
v___x_2023_ = 0;
v___x_2024_ = lean_box(v___x_2023_);
lean_inc_ref(v_alpha_2000_);
lean_inc(v___x_1999_);
v___f_2025_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2025_, 0, v___x_1999_);
lean_closure_set(v___f_2025_, 1, v___x_2020_);
lean_closure_set(v___f_2025_, 2, v_alpha_2000_);
lean_closure_set(v___f_2025_, 3, v___x_2024_);
v___x_2026_ = lean_box(v___x_2023_);
lean_inc_ref(v_alpha_2000_);
v___f_2027_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed), 24, 18);
lean_closure_set(v___f_2027_, 0, v___x_2001_);
lean_closure_set(v___f_2027_, 1, v___f_2025_);
lean_closure_set(v___f_2027_, 2, v___x_2021_);
lean_closure_set(v___f_2027_, 3, v___x_2002_);
lean_closure_set(v___f_2027_, 4, v_beta_2013_);
lean_closure_set(v___f_2027_, 5, v___x_2026_);
lean_closure_set(v___f_2027_, 6, v_alpha_2000_);
lean_closure_set(v___f_2027_, 7, v_numDiscrs_2003_);
lean_closure_set(v___f_2027_, 8, v___f_2004_);
lean_closure_set(v___f_2027_, 9, v_a_2005_);
lean_closure_set(v___f_2027_, 10, v_a_2006_);
lean_closure_set(v___f_2027_, 11, v_levelParams_2007_);
lean_closure_set(v___f_2027_, 12, v_matcherName_2008_);
lean_closure_set(v___f_2027_, 13, v___x_2009_);
lean_closure_set(v___f_2027_, 14, v_matcherInfo_2010_);
lean_closure_set(v___f_2027_, 15, v___x_1999_);
lean_closure_set(v___f_2027_, 16, v___x_2011_);
lean_closure_set(v___f_2027_, 17, v_uElimPos_x3f_2012_);
v___x_2028_ = l_Lean_Expr_forallE___override(v___x_2020_, v_alpha_2000_, v___x_2022_, v___x_2023_);
v___x_2029_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2019_, v___x_2028_, v___f_2027_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed(lean_object** _args){
lean_object* v___x_2030_ = _args[0];
lean_object* v_alpha_2031_ = _args[1];
lean_object* v___x_2032_ = _args[2];
lean_object* v___x_2033_ = _args[3];
lean_object* v_numDiscrs_2034_ = _args[4];
lean_object* v___f_2035_ = _args[5];
lean_object* v_a_2036_ = _args[6];
lean_object* v_a_2037_ = _args[7];
lean_object* v_levelParams_2038_ = _args[8];
lean_object* v_matcherName_2039_ = _args[9];
lean_object* v___x_2040_ = _args[10];
lean_object* v_matcherInfo_2041_ = _args[11];
lean_object* v___x_2042_ = _args[12];
lean_object* v_uElimPos_x3f_2043_ = _args[13];
lean_object* v_beta_2044_ = _args[14];
lean_object* v___y_2045_ = _args[15];
lean_object* v___y_2046_ = _args[16];
lean_object* v___y_2047_ = _args[17];
lean_object* v___y_2048_ = _args[18];
lean_object* v___y_2049_ = _args[19];
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(v___x_2030_, v_alpha_2031_, v___x_2032_, v___x_2033_, v_numDiscrs_2034_, v___f_2035_, v_a_2036_, v_a_2037_, v_levelParams_2038_, v_matcherName_2039_, v___x_2040_, v_matcherInfo_2041_, v___x_2042_, v_uElimPos_x3f_2043_, v_beta_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(lean_object* v_a_2054_, lean_object* v___x_2055_, lean_object* v___x_2056_, lean_object* v___x_2057_, lean_object* v_numDiscrs_2058_, lean_object* v___f_2059_, lean_object* v_a_2060_, lean_object* v_levelParams_2061_, lean_object* v_matcherName_2062_, lean_object* v___x_2063_, lean_object* v_matcherInfo_2064_, lean_object* v___x_2065_, lean_object* v_uElimPos_x3f_2066_, lean_object* v_alpha_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_inc(v_a_2054_);
v___x_2073_ = l_Lean_Level_param___override(v_a_2054_);
v___x_2074_ = l_Lean_Expr_sort___override(v___x_2073_);
lean_inc(v___y_2071_);
lean_inc_ref(v___y_2070_);
lean_inc_ref(v_alpha_2067_);
v___x_2075_ = l_Lean_mkArrow(v_alpha_2067_, v___x_2074_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref(v___x_2075_);
v___f_2077_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed), 20, 14);
lean_closure_set(v___f_2077_, 0, v___x_2055_);
lean_closure_set(v___f_2077_, 1, v_alpha_2067_);
lean_closure_set(v___f_2077_, 2, v___x_2056_);
lean_closure_set(v___f_2077_, 3, v___x_2057_);
lean_closure_set(v___f_2077_, 4, v_numDiscrs_2058_);
lean_closure_set(v___f_2077_, 5, v___f_2059_);
lean_closure_set(v___f_2077_, 6, v_a_2054_);
lean_closure_set(v___f_2077_, 7, v_a_2060_);
lean_closure_set(v___f_2077_, 8, v_levelParams_2061_);
lean_closure_set(v___f_2077_, 9, v_matcherName_2062_);
lean_closure_set(v___f_2077_, 10, v___x_2063_);
lean_closure_set(v___f_2077_, 11, v_matcherInfo_2064_);
lean_closure_set(v___f_2077_, 12, v___x_2065_);
lean_closure_set(v___f_2077_, 13, v_uElimPos_x3f_2066_);
v___x_2078_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__1));
v___x_2079_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2078_, v_a_2076_, v___f_2077_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
return v___x_2079_;
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec_ref(v_alpha_2067_);
lean_dec(v_uElimPos_x3f_2066_);
lean_dec(v___x_2065_);
lean_dec_ref(v_matcherInfo_2064_);
lean_dec_ref(v___x_2063_);
lean_dec(v_matcherName_2062_);
lean_dec(v_levelParams_2061_);
lean_dec(v_a_2060_);
lean_dec_ref(v___f_2059_);
lean_dec(v_numDiscrs_2058_);
lean_dec(v___x_2057_);
lean_dec_ref(v___x_2056_);
lean_dec(v___x_2055_);
lean_dec(v_a_2054_);
v_a_2080_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2075_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2075_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed(lean_object** _args){
lean_object* v_a_2088_ = _args[0];
lean_object* v___x_2089_ = _args[1];
lean_object* v___x_2090_ = _args[2];
lean_object* v___x_2091_ = _args[3];
lean_object* v_numDiscrs_2092_ = _args[4];
lean_object* v___f_2093_ = _args[5];
lean_object* v_a_2094_ = _args[6];
lean_object* v_levelParams_2095_ = _args[7];
lean_object* v_matcherName_2096_ = _args[8];
lean_object* v___x_2097_ = _args[9];
lean_object* v_matcherInfo_2098_ = _args[10];
lean_object* v___x_2099_ = _args[11];
lean_object* v_uElimPos_x3f_2100_ = _args[12];
lean_object* v_alpha_2101_ = _args[13];
lean_object* v___y_2102_ = _args[14];
lean_object* v___y_2103_ = _args[15];
lean_object* v___y_2104_ = _args[16];
lean_object* v___y_2105_ = _args[17];
lean_object* v___y_2106_ = _args[18];
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(v_a_2088_, v___x_2089_, v___x_2090_, v___x_2091_, v_numDiscrs_2092_, v___f_2093_, v_a_2094_, v_levelParams_2095_, v_matcherName_2096_, v___x_2097_, v_matcherInfo_2098_, v___x_2099_, v_uElimPos_x3f_2100_, v_alpha_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(lean_object* v_numParams_2117_, lean_object* v___x_2118_, lean_object* v___x_2119_, lean_object* v_numDiscrs_2120_, lean_object* v___f_2121_, lean_object* v_levelParams_2122_, lean_object* v_matcherName_2123_, lean_object* v_matcherInfo_2124_, lean_object* v___x_2125_, lean_object* v_uElimPos_x3f_2126_, lean_object* v_xs_2127_, lean_object* v_x_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__1));
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
v___x_2135_ = l_Lean_Core_mkFreshUserName(v___x_2134_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref(v___x_2135_);
v___x_2137_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__3));
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
v___x_2138_ = l_Lean_Core_mkFreshUserName(v___x_2137_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___f_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___x_2138_);
v___x_2140_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2117_);
lean_inc_ref(v_xs_2127_);
v___x_2141_ = l_Array_toSubarray___redArg(v_xs_2127_, v___x_2140_, v_numParams_2117_);
v___x_2142_ = lean_array_get(v___x_2118_, v_xs_2127_, v_numParams_2117_);
lean_dec(v_numParams_2117_);
lean_dec_ref(v_xs_2127_);
lean_inc(v_a_2136_);
v___f_2143_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed), 19, 13);
lean_closure_set(v___f_2143_, 0, v_a_2139_);
lean_closure_set(v___f_2143_, 1, v___x_2140_);
lean_closure_set(v___f_2143_, 2, v___x_2142_);
lean_closure_set(v___f_2143_, 3, v___x_2119_);
lean_closure_set(v___f_2143_, 4, v_numDiscrs_2120_);
lean_closure_set(v___f_2143_, 5, v___f_2121_);
lean_closure_set(v___f_2143_, 6, v_a_2136_);
lean_closure_set(v___f_2143_, 7, v_levelParams_2122_);
lean_closure_set(v___f_2143_, 8, v_matcherName_2123_);
lean_closure_set(v___f_2143_, 9, v___x_2141_);
lean_closure_set(v___f_2143_, 10, v_matcherInfo_2124_);
lean_closure_set(v___f_2143_, 11, v___x_2125_);
lean_closure_set(v___f_2143_, 12, v_uElimPos_x3f_2126_);
v___x_2144_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__5));
v___x_2145_ = l_Lean_Level_param___override(v_a_2136_);
v___x_2146_ = l_Lean_Expr_sort___override(v___x_2145_);
v___x_2147_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2144_, v___x_2146_, v___f_2143_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2147_;
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_a_2136_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec_ref(v_xs_2127_);
lean_dec(v_uElimPos_x3f_2126_);
lean_dec(v___x_2125_);
lean_dec_ref(v_matcherInfo_2124_);
lean_dec(v_matcherName_2123_);
lean_dec(v_levelParams_2122_);
lean_dec_ref(v___f_2121_);
lean_dec(v_numDiscrs_2120_);
lean_dec(v___x_2119_);
lean_dec_ref(v___x_2118_);
lean_dec(v_numParams_2117_);
v_a_2148_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2138_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2138_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec_ref(v_xs_2127_);
lean_dec(v_uElimPos_x3f_2126_);
lean_dec(v___x_2125_);
lean_dec_ref(v_matcherInfo_2124_);
lean_dec(v_matcherName_2123_);
lean_dec(v_levelParams_2122_);
lean_dec_ref(v___f_2121_);
lean_dec(v_numDiscrs_2120_);
lean_dec(v___x_2119_);
lean_dec_ref(v___x_2118_);
lean_dec(v_numParams_2117_);
v_a_2156_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2135_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2135_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed(lean_object** _args){
lean_object* v_numParams_2164_ = _args[0];
lean_object* v___x_2165_ = _args[1];
lean_object* v___x_2166_ = _args[2];
lean_object* v_numDiscrs_2167_ = _args[3];
lean_object* v___f_2168_ = _args[4];
lean_object* v_levelParams_2169_ = _args[5];
lean_object* v_matcherName_2170_ = _args[6];
lean_object* v_matcherInfo_2171_ = _args[7];
lean_object* v___x_2172_ = _args[8];
lean_object* v_uElimPos_x3f_2173_ = _args[9];
lean_object* v_xs_2174_ = _args[10];
lean_object* v_x_2175_ = _args[11];
lean_object* v___y_2176_ = _args[12];
lean_object* v___y_2177_ = _args[13];
lean_object* v___y_2178_ = _args[14];
lean_object* v___y_2179_ = _args[15];
lean_object* v___y_2180_ = _args[16];
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(v_numParams_2164_, v___x_2165_, v___x_2166_, v_numDiscrs_2167_, v___f_2168_, v_levelParams_2169_, v_matcherName_2170_, v_matcherInfo_2171_, v___x_2172_, v_uElimPos_x3f_2173_, v_xs_2174_, v_x_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec_ref(v_x_2175_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(lean_object* v_ref_2182_, lean_object* v_msg_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_fileName_2189_; lean_object* v_fileMap_2190_; lean_object* v_options_2191_; lean_object* v_currRecDepth_2192_; lean_object* v_maxRecDepth_2193_; lean_object* v_ref_2194_; lean_object* v_currNamespace_2195_; lean_object* v_openDecls_2196_; lean_object* v_initHeartbeats_2197_; lean_object* v_maxHeartbeats_2198_; lean_object* v_quotContext_2199_; lean_object* v_currMacroScope_2200_; uint8_t v_diag_2201_; lean_object* v_cancelTk_x3f_2202_; uint8_t v_suppressElabErrors_2203_; lean_object* v_inheritedTraceOptions_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2213_; 
v_fileName_2189_ = lean_ctor_get(v___y_2186_, 0);
v_fileMap_2190_ = lean_ctor_get(v___y_2186_, 1);
v_options_2191_ = lean_ctor_get(v___y_2186_, 2);
v_currRecDepth_2192_ = lean_ctor_get(v___y_2186_, 3);
v_maxRecDepth_2193_ = lean_ctor_get(v___y_2186_, 4);
v_ref_2194_ = lean_ctor_get(v___y_2186_, 5);
v_currNamespace_2195_ = lean_ctor_get(v___y_2186_, 6);
v_openDecls_2196_ = lean_ctor_get(v___y_2186_, 7);
v_initHeartbeats_2197_ = lean_ctor_get(v___y_2186_, 8);
v_maxHeartbeats_2198_ = lean_ctor_get(v___y_2186_, 9);
v_quotContext_2199_ = lean_ctor_get(v___y_2186_, 10);
v_currMacroScope_2200_ = lean_ctor_get(v___y_2186_, 11);
v_diag_2201_ = lean_ctor_get_uint8(v___y_2186_, sizeof(void*)*14);
v_cancelTk_x3f_2202_ = lean_ctor_get(v___y_2186_, 12);
v_suppressElabErrors_2203_ = lean_ctor_get_uint8(v___y_2186_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2204_ = lean_ctor_get(v___y_2186_, 13);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___y_2186_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2206_ = v___y_2186_;
v_isShared_2207_ = v_isSharedCheck_2213_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_inheritedTraceOptions_2204_);
lean_inc(v_cancelTk_x3f_2202_);
lean_inc(v_currMacroScope_2200_);
lean_inc(v_quotContext_2199_);
lean_inc(v_maxHeartbeats_2198_);
lean_inc(v_initHeartbeats_2197_);
lean_inc(v_openDecls_2196_);
lean_inc(v_currNamespace_2195_);
lean_inc(v_ref_2194_);
lean_inc(v_maxRecDepth_2193_);
lean_inc(v_currRecDepth_2192_);
lean_inc(v_options_2191_);
lean_inc(v_fileMap_2190_);
lean_inc(v_fileName_2189_);
lean_dec(v___y_2186_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2213_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v_ref_2208_; lean_object* v___x_2210_; 
v_ref_2208_ = l_Lean_replaceRef(v_ref_2182_, v_ref_2194_);
lean_dec(v_ref_2194_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 5, v_ref_2208_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_fileName_2189_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_fileMap_2190_);
lean_ctor_set(v_reuseFailAlloc_2212_, 2, v_options_2191_);
lean_ctor_set(v_reuseFailAlloc_2212_, 3, v_currRecDepth_2192_);
lean_ctor_set(v_reuseFailAlloc_2212_, 4, v_maxRecDepth_2193_);
lean_ctor_set(v_reuseFailAlloc_2212_, 5, v_ref_2208_);
lean_ctor_set(v_reuseFailAlloc_2212_, 6, v_currNamespace_2195_);
lean_ctor_set(v_reuseFailAlloc_2212_, 7, v_openDecls_2196_);
lean_ctor_set(v_reuseFailAlloc_2212_, 8, v_initHeartbeats_2197_);
lean_ctor_set(v_reuseFailAlloc_2212_, 9, v_maxHeartbeats_2198_);
lean_ctor_set(v_reuseFailAlloc_2212_, 10, v_quotContext_2199_);
lean_ctor_set(v_reuseFailAlloc_2212_, 11, v_currMacroScope_2200_);
lean_ctor_set(v_reuseFailAlloc_2212_, 12, v_cancelTk_x3f_2202_);
lean_ctor_set(v_reuseFailAlloc_2212_, 13, v_inheritedTraceOptions_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2212_, sizeof(void*)*14, v_diag_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2212_, sizeof(void*)*14 + 1, v_suppressElabErrors_2203_);
v___x_2210_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_2183_, v___y_2184_, v___y_2185_, v___x_2210_, v___y_2187_);
lean_dec_ref(v___x_2210_);
return v___x_2211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2214_, lean_object* v_msg_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2214_, v_msg_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v_ref_2214_);
return v_res_2221_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
lean_ctor_set(v___x_2227_, 2, v___x_2226_);
lean_ctor_set(v___x_2227_, 3, v___x_2225_);
lean_ctor_set(v___x_2227_, 4, v___x_2225_);
lean_ctor_set(v___x_2227_, 5, v___x_2225_);
lean_ctor_set(v___x_2227_, 6, v___x_2225_);
lean_ctor_set(v___x_2227_, 7, v___x_2225_);
lean_ctor_set(v___x_2227_, 8, v___x_2225_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = lean_unsigned_to_nat(32u);
v___x_2229_ = lean_mk_empty_array_with_capacity(v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
return v___x_2230_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2231_ = ((size_t)5ULL);
v___x_2232_ = lean_unsigned_to_nat(0u);
v___x_2233_ = lean_unsigned_to_nat(32u);
v___x_2234_ = lean_mk_empty_array_with_capacity(v___x_2233_);
v___x_2235_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3);
v___x_2236_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set(v___x_2236_, 1, v___x_2234_);
lean_ctor_set(v___x_2236_, 2, v___x_2232_);
lean_ctor_set(v___x_2236_, 3, v___x_2232_);
lean_ctor_set_usize(v___x_2236_, 4, v___x_2231_);
return v___x_2236_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2237_ = lean_box(1);
v___x_2238_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4);
v___x_2239_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v___x_2238_);
lean_ctor_set(v___x_2240_, 2, v___x_2237_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__6));
v___x_2243_ = l_Lean_stringToMessageData(v___x_2242_);
return v___x_2243_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__8));
v___x_2246_ = l_Lean_stringToMessageData(v___x_2245_);
return v___x_2246_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__10));
v___x_2249_ = l_Lean_stringToMessageData(v___x_2248_);
return v___x_2249_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__12));
v___x_2252_ = l_Lean_stringToMessageData(v___x_2251_);
return v___x_2252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__14));
v___x_2255_ = l_Lean_stringToMessageData(v___x_2254_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16));
v___x_2258_ = l_Lean_stringToMessageData(v___x_2257_);
return v___x_2258_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18));
v___x_2261_ = l_Lean_stringToMessageData(v___x_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2262_, lean_object* v_declHint_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; lean_object* v_env_2267_; uint8_t v___x_2268_; 
v___x_2266_ = lean_st_ref_get(v___y_2264_);
v_env_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc_ref(v_env_2267_);
lean_dec(v___x_2266_);
v___x_2268_ = l_Lean_Name_isAnonymous(v_declHint_2263_);
if (v___x_2268_ == 0)
{
uint8_t v_isExporting_2269_; 
v_isExporting_2269_ = lean_ctor_get_uint8(v_env_2267_, sizeof(void*)*8);
if (v_isExporting_2269_ == 0)
{
lean_object* v___x_2270_; 
lean_dec_ref(v_env_2267_);
lean_dec(v_declHint_2263_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v_msg_2262_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
lean_inc_ref(v_env_2267_);
v___x_2271_ = l_Lean_Environment_setExporting(v_env_2267_, v___x_2268_);
lean_inc(v_declHint_2263_);
lean_inc_ref(v___x_2271_);
v___x_2272_ = l_Lean_Environment_contains(v___x_2271_, v_declHint_2263_, v_isExporting_2269_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; 
lean_dec_ref(v___x_2271_);
lean_dec_ref(v_env_2267_);
lean_dec(v_declHint_2263_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v_msg_2262_);
return v___x_2273_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v_c_2279_; lean_object* v___x_2280_; 
v___x_2274_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2275_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2276_ = l_Lean_Options_empty;
v___x_2277_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2271_);
lean_ctor_set(v___x_2277_, 1, v___x_2274_);
lean_ctor_set(v___x_2277_, 2, v___x_2275_);
lean_ctor_set(v___x_2277_, 3, v___x_2276_);
lean_inc(v_declHint_2263_);
v___x_2278_ = l_Lean_MessageData_ofConstName(v_declHint_2263_, v___x_2268_);
v_c_2279_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2279_, 0, v___x_2277_);
lean_ctor_set(v_c_2279_, 1, v___x_2278_);
v___x_2280_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2267_, v_declHint_2263_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec_ref(v_env_2267_);
lean_dec(v_declHint_2263_);
v___x_2281_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v_c_2279_);
v___x_2283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = l_Lean_MessageData_note(v___x_2284_);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v_msg_2262_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
else
{
lean_object* v_val_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2323_; 
v_val_2288_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2290_ = v___x_2280_;
v_isShared_2291_ = v_isSharedCheck_2323_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_val_2288_);
lean_dec(v___x_2280_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2323_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v_mod_2295_; uint8_t v___x_2296_; 
v___x_2292_ = lean_box(0);
v___x_2293_ = l_Lean_Environment_header(v_env_2267_);
lean_dec_ref(v_env_2267_);
v___x_2294_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2293_);
v_mod_2295_ = lean_array_get(v___x_2292_, v___x_2294_, v_val_2288_);
lean_dec(v_val_2288_);
lean_dec_ref(v___x_2294_);
v___x_2296_ = l_Lean_isPrivateName(v_declHint_2263_);
lean_dec(v_declHint_2263_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v_c_2279_);
v___x_2299_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = l_Lean_MessageData_ofName(v_mod_2295_);
v___x_2302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2300_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = l_Lean_MessageData_note(v___x_2304_);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v_msg_2262_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set_tag(v___x_2290_, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2306_);
v___x_2308_ = v___x_2290_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2310_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v_c_2279_);
v___x_2312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = l_Lean_MessageData_ofName(v_mod_2295_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_MessageData_note(v___x_2317_);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v_msg_2262_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set_tag(v___x_2290_, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2319_);
v___x_2321_ = v___x_2290_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2324_; 
lean_dec_ref(v_env_2267_);
lean_dec(v_declHint_2263_);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v_msg_2262_);
return v___x_2324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2325_, lean_object* v_declHint_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2325_, v_declHint_2326_, v___y_2327_);
lean_dec(v___y_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(lean_object* v_msg_2330_, lean_object* v_declHint_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2347_; 
v___x_2337_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2330_, v_declHint_2331_, v___y_2335_);
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2347_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2347_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2342_ = l_Lean_unknownIdentifierMessageTag;
v___x_2343_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v_a_2338_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2343_);
v___x_2345_ = v___x_2340_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11___boxed(lean_object* v_msg_2348_, lean_object* v_declHint_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2348_, v_declHint_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_ref_2356_, lean_object* v_msg_2357_, lean_object* v_declHint_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; lean_object* v_a_2365_; lean_object* v___x_2366_; 
v___x_2364_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2357_, v_declHint_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref(v___x_2364_);
v___x_2366_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2356_, v_a_2365_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_ref_2367_, lean_object* v_msg_2368_, lean_object* v_declHint_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2367_, v_msg_2368_, v_declHint_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v_ref_2367_);
return v_res_2375_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_2378_ = l_Lean_stringToMessageData(v___x_2377_);
return v___x_2378_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_2381_ = l_Lean_stringToMessageData(v___x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_2382_, lean_object* v_constName_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2389_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_2390_ = 0;
lean_inc(v_constName_2383_);
v___x_2391_ = l_Lean_MessageData_ofConstName(v_constName_2383_, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2389_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2382_, v___x_2394_, v_constName_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_2396_, lean_object* v_constName_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2396_, v_constName_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v_ref_2396_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(lean_object* v_constName_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_ref_2410_; lean_object* v___x_2411_; 
v_ref_2410_ = lean_ctor_get(v___y_2407_, 5);
lean_inc(v_ref_2410_);
v___x_2411_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2410_, v_constName_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v_ref_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(lean_object* v_constName_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; lean_object* v_env_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = lean_st_ref_get(v___y_2423_);
v_env_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc_ref(v_env_2426_);
lean_dec(v___x_2425_);
v___x_2427_ = 0;
lean_inc(v_constName_2419_);
v___x_2428_ = l_Lean_Environment_findConstVal_x3f(v_env_2426_, v_constName_2419_, v___x_2427_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2429_;
}
else
{
lean_object* v_val_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec_ref(v___y_2422_);
lean_dec(v_constName_2419_);
v_val_2430_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2428_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_val_2430_);
lean_dec(v___x_2428_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set_tag(v___x_2432_, 0);
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_val_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0___boxed(lean_object* v_constName_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_constName_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(lean_object* v_matcherName_2445_, lean_object* v_matcherInfo_2446_, lean_object* v___x_2447_, lean_object* v___f_2448_, lean_object* v___x_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
lean_inc_ref(v___y_2452_);
lean_inc(v_matcherName_2445_);
v___x_2455_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_matcherName_2445_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v_levelParams_2457_; lean_object* v_type_2458_; lean_object* v_numParams_2459_; lean_object* v_numDiscrs_2460_; lean_object* v_uElimPos_x3f_2461_; lean_object* v___x_2462_; lean_object* v___f_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; lean_object* v___x_2467_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref(v___x_2455_);
v_levelParams_2457_ = lean_ctor_get(v_a_2456_, 1);
lean_inc(v_levelParams_2457_);
v_type_2458_ = lean_ctor_get(v_a_2456_, 2);
lean_inc_ref(v_type_2458_);
lean_dec(v_a_2456_);
v_numParams_2459_ = lean_ctor_get(v_matcherInfo_2446_, 0);
lean_inc(v_numParams_2459_);
v_numDiscrs_2460_ = lean_ctor_get(v_matcherInfo_2446_, 1);
lean_inc(v_numDiscrs_2460_);
v_uElimPos_x3f_2461_ = lean_ctor_get(v_matcherInfo_2446_, 3);
lean_inc(v_uElimPos_x3f_2461_);
v___x_2462_ = lean_unsigned_to_nat(1u);
lean_inc(v_numParams_2459_);
v___f_2463_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed), 17, 10);
lean_closure_set(v___f_2463_, 0, v_numParams_2459_);
lean_closure_set(v___f_2463_, 1, v___x_2447_);
lean_closure_set(v___f_2463_, 2, v___x_2462_);
lean_closure_set(v___f_2463_, 3, v_numDiscrs_2460_);
lean_closure_set(v___f_2463_, 4, v___f_2448_);
lean_closure_set(v___f_2463_, 5, v_levelParams_2457_);
lean_closure_set(v___f_2463_, 6, v_matcherName_2445_);
lean_closure_set(v___f_2463_, 7, v_matcherInfo_2446_);
lean_closure_set(v___f_2463_, 8, v___x_2449_);
lean_closure_set(v___f_2463_, 9, v_uElimPos_x3f_2461_);
v___x_2464_ = lean_nat_add(v_numParams_2459_, v___x_2462_);
lean_dec(v_numParams_2459_);
v___x_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
v___x_2466_ = 0;
v___x_2467_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_2458_, v___x_2465_, v___f_2463_, v___x_2466_, v___x_2466_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2467_;
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___x_2449_);
lean_dec_ref(v___f_2448_);
lean_dec_ref(v___x_2447_);
lean_dec_ref(v_matcherInfo_2446_);
lean_dec(v_matcherName_2445_);
v_a_2468_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2455_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2455_);
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
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed(lean_object* v_matcherName_2476_, lean_object* v_matcherInfo_2477_, lean_object* v___x_2478_, lean_object* v___f_2479_, lean_object* v___x_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(v_matcherName_2476_, v_matcherInfo_2477_, v___x_2478_, v___f_2479_, v___x_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11(lean_object* v___x_2487_, lean_object* v_e_2488_){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = l_Lean_indentD(v_e_2488_);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2487_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(lean_object* v___f_2491_, lean_object* v___f_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2491_, v___f_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
v_a_2507_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2498_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2498_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed(lean_object* v___f_2515_, lean_object* v___f_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(v___f_2515_, v___f_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
return v_res_2522_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__3));
v___x_2529_ = l_Lean_stringToMessageData(v___x_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(lean_object* v_matcherName_2530_, lean_object* v_matcherInfo_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v___x_2537_; lean_object* v_env_2538_; lean_object* v___f_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___f_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___f_2548_; lean_object* v___f_2549_; lean_object* v___x_2550_; 
v___x_2537_ = lean_st_ref_get(v_a_2535_);
v_env_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc_ref(v_env_2538_);
lean_dec(v___x_2537_);
v___f_2539_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__0));
v___x_2540_ = l_Lean_instInhabitedExpr;
lean_inc(v_matcherName_2530_);
v___x_2541_ = l_Lean_mkPrivateName(v_env_2538_, v_matcherName_2530_);
lean_dec_ref(v_env_2538_);
v___x_2542_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__2));
v___x_2543_ = l_Lean_Name_append(v___x_2541_, v___x_2542_);
lean_inc(v___x_2543_);
lean_inc(v_matcherName_2530_);
v___f_2544_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed), 10, 5);
lean_closure_set(v___f_2544_, 0, v_matcherName_2530_);
lean_closure_set(v___f_2544_, 1, v_matcherInfo_2531_);
lean_closure_set(v___f_2544_, 2, v___x_2540_);
lean_closure_set(v___f_2544_, 3, v___f_2539_);
lean_closure_set(v___f_2544_, 4, v___x_2543_);
v___x_2545_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4);
lean_inc(v_matcherName_2530_);
v___x_2546_ = l_Lean_MessageData_ofName(v_matcherName_2530_);
v___x_2547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2545_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___f_2548_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_2548_, 0, v___x_2547_);
v___f_2549_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed), 7, 2);
lean_closure_set(v___f_2549_, 0, v___f_2544_);
lean_closure_set(v___f_2549_, 1, v___f_2548_);
lean_inc(v___x_2543_);
v___x_2550_ = l_Lean_Meta_realizeConst(v_matcherName_2530_, v___x_2543_, v___f_2549_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; 
v_unused_2558_ = lean_ctor_get(v___x_2550_, 0);
lean_dec(v_unused_2558_);
v___x_2552_ = v___x_2550_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_dec(v___x_2550_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2543_);
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2543_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v___x_2543_);
v_a_2559_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2550_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2550_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___boxed(lean_object* v_matcherName_2567_, lean_object* v_matcherInfo_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_2567_, v_matcherInfo_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(lean_object* v_as_2575_, lean_object* v_as_x27_2576_, lean_object* v_b_2577_, lean_object* v_a_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_2576_, v_b_2577_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___boxed(lean_object* v_as_2585_, lean_object* v_as_x27_2586_, lean_object* v_b_2587_, lean_object* v_a_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(v_as_2585_, v_as_x27_2586_, v_b_2587_, v_a_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v_as_2585_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(lean_object* v_00_u03b1_2595_, lean_object* v_name_2596_, uint8_t v_bi_2597_, lean_object* v_type_2598_, lean_object* v_k_2599_, uint8_t v_kind_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_2596_, v_bi_2597_, v_type_2598_, v_k_2599_, v_kind_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2607_, lean_object* v_name_2608_, lean_object* v_bi_2609_, lean_object* v_type_2610_, lean_object* v_k_2611_, lean_object* v_kind_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
uint8_t v_bi_boxed_2618_; uint8_t v_kind_boxed_2619_; lean_object* v_res_2620_; 
v_bi_boxed_2618_ = lean_unbox(v_bi_2609_);
v_kind_boxed_2619_ = lean_unbox(v_kind_2612_);
v_res_2620_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(v_00_u03b1_2607_, v_name_2608_, v_bi_boxed_2618_, v_type_2610_, v_k_2611_, v_kind_boxed_2619_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(lean_object* v_00_u03b1_2621_, lean_object* v_name_2622_, lean_object* v_type_2623_, lean_object* v_k_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_2622_, v_type_2623_, v_k_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___boxed(lean_object* v_00_u03b1_2631_, lean_object* v_name_2632_, lean_object* v_type_2633_, lean_object* v_k_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(v_00_u03b1_2631_, v_name_2632_, v_type_2633_, v_k_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(lean_object* v_00_u03b1_2641_, lean_object* v_constName_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2649_, lean_object* v_constName_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(v_00_u03b1_2649_, v_constName_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2657_, lean_object* v_ref_2658_, lean_object* v_constName_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2658_, v_constName_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2666_, lean_object* v_ref_2667_, lean_object* v_constName_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(v_00_u03b1_2666_, v_ref_2667_, v_constName_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v_ref_2667_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b1_2675_, lean_object* v_ref_2676_, lean_object* v_msg_2677_, lean_object* v_declHint_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2676_, v_msg_2677_, v_declHint_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b1_2685_, lean_object* v_ref_2686_, lean_object* v_msg_2687_, lean_object* v_declHint_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(v_00_u03b1_2685_, v_ref_2686_, v_msg_2687_, v_declHint_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v_ref_2686_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(lean_object* v_msg_2695_, lean_object* v_declHint_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2695_, v_declHint_2696_, v___y_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_2703_, lean_object* v_declHint_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(v_msg_2703_, v_declHint_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_2711_, lean_object* v_ref_2712_, lean_object* v_msg_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2712_, v_msg_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_2720_, lean_object* v_ref_2721_, lean_object* v_msg_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(v_00_u03b1_2720_, v_ref_2721_, v_msg_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v_ref_2721_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(lean_object* v_msg_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___f_2739_; lean_object* v___x_47246__overap_2740_; lean_object* v___x_2741_; 
v___f_2739_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0));
v___x_47246__overap_2740_ = lean_panic_fn(v___f_2739_, v_msg_2730_);
v___x_2741_ = lean_apply_8(v___x_47246__overap_2740_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, lean_box(0));
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___boxed(lean_object* v_msg_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v_msg_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(lean_object* v_k_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v_b_2756_, lean_object* v_c_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_apply_10(v_k_2752_, v_b_2756_, v_c_2757_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, lean_box(0));
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed(lean_object* v_k_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v_b_2768_, lean_object* v_c_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(v_k_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v_b_2768_, v_c_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(lean_object* v_e_2776_, lean_object* v_k_2777_, uint8_t v_cleanupAnnotations_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v___f_2787_; uint8_t v___x_2788_; uint8_t v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___f_2787_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2787_, 0, v_k_2777_);
lean_closure_set(v___f_2787_, 1, v___y_2779_);
lean_closure_set(v___f_2787_, 2, v___y_2780_);
lean_closure_set(v___f_2787_, 3, v___y_2781_);
v___x_2788_ = 1;
v___x_2789_ = 0;
v___x_2790_ = lean_box(0);
v___x_2791_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2776_, v___x_2788_, v___x_2789_, v___x_2788_, v___x_2789_, v___x_2790_, v___f_2787_, v_cleanupAnnotations_2778_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
if (lean_obj_tag(v___x_2791_) == 0)
{
return v___x_2791_;
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___boxed(lean_object* v_e_2800_, lean_object* v_k_2801_, lean_object* v_cleanupAnnotations_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2811_; lean_object* v_res_2812_; 
v_cleanupAnnotations_boxed_2811_ = lean_unbox(v_cleanupAnnotations_2802_);
v_res_2812_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2800_, v_k_2801_, v_cleanupAnnotations_boxed_2811_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(lean_object* v_00_u03b1_2813_, lean_object* v_e_2814_, lean_object* v_k_2815_, uint8_t v_cleanupAnnotations_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2814_, v_k_2815_, v_cleanupAnnotations_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___boxed(lean_object* v_00_u03b1_2826_, lean_object* v_e_2827_, lean_object* v_k_2828_, lean_object* v_cleanupAnnotations_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2838_; lean_object* v_res_2839_; 
v_cleanupAnnotations_boxed_2838_ = lean_unbox(v_cleanupAnnotations_2829_);
v_res_2839_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(v_00_u03b1_2826_, v_e_2827_, v_k_2828_, v_cleanupAnnotations_boxed_2838_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(uint8_t v___x_2840_, uint8_t v___x_2841_, uint8_t v___x_2842_, lean_object* v_xs_2843_, lean_object* v_motiveBody_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; lean_object* v___x_2860_; 
v___x_2853_ = l_Lean_Expr_bindingDomain_x21(v_motiveBody_2844_);
v___x_2854_ = l_Lean_Expr_bindingName_x21(v___x_2853_);
v___x_2855_ = l_Lean_Expr_bindingDomain_x21(v___x_2853_);
v___x_2856_ = l_Lean_Expr_bindingBody_x21(v___x_2853_);
lean_dec_ref(v___x_2853_);
v___x_2857_ = l_Lean_Expr_bindingDomain_x21(v___x_2856_);
lean_dec_ref(v___x_2856_);
v___x_2858_ = l_Lean_Expr_lam___override(v___x_2854_, v___x_2855_, v___x_2857_, v___x_2840_);
v___x_2859_ = 1;
v___x_2860_ = l_Lean_Meta_mkLambdaFVars(v_xs_2843_, v___x_2858_, v___x_2841_, v___x_2842_, v___x_2841_, v___x_2842_, v___x_2859_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed(lean_object* v___x_2861_, lean_object* v___x_2862_, lean_object* v___x_2863_, lean_object* v_xs_2864_, lean_object* v_motiveBody_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
uint8_t v___x_55058__boxed_2874_; uint8_t v___x_55059__boxed_2875_; uint8_t v___x_55060__boxed_2876_; lean_object* v_res_2877_; 
v___x_55058__boxed_2874_ = lean_unbox(v___x_2861_);
v___x_55059__boxed_2875_ = lean_unbox(v___x_2862_);
v___x_55060__boxed_2876_ = lean_unbox(v___x_2863_);
v_res_2877_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(v___x_55058__boxed_2874_, v___x_55059__boxed_2875_, v___x_55060__boxed_2876_, v_xs_2864_, v_motiveBody_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v_motiveBody_2865_);
lean_dec_ref(v_xs_2864_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(size_t v_sz_2878_, size_t v_i_2879_, lean_object* v_bs_2880_){
_start:
{
uint8_t v___x_2881_; 
v___x_2881_ = lean_usize_dec_lt(v_i_2879_, v_sz_2878_);
if (v___x_2881_ == 0)
{
return v_bs_2880_;
}
else
{
lean_object* v_v_2882_; lean_object* v___x_2883_; lean_object* v_bs_x27_2884_; lean_object* v___x_2885_; size_t v___x_2886_; size_t v___x_2887_; lean_object* v___x_2888_; 
v_v_2882_ = lean_array_uget(v_bs_2880_, v_i_2879_);
v___x_2883_ = lean_unsigned_to_nat(0u);
v_bs_x27_2884_ = lean_array_uset(v_bs_2880_, v_i_2879_, v___x_2883_);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_v_2882_);
v___x_2886_ = ((size_t)1ULL);
v___x_2887_ = lean_usize_add(v_i_2879_, v___x_2886_);
v___x_2888_ = lean_array_uset(v_bs_x27_2884_, v_i_2879_, v___x_2885_);
v_i_2879_ = v___x_2887_;
v_bs_2880_ = v___x_2888_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4___boxed(lean_object* v_sz_2890_, lean_object* v_i_2891_, lean_object* v_bs_2892_){
_start:
{
size_t v_sz_boxed_2893_; size_t v_i_boxed_2894_; lean_object* v_res_2895_; 
v_sz_boxed_2893_ = lean_unbox_usize(v_sz_2890_);
lean_dec(v_sz_2890_);
v_i_boxed_2894_ = lean_unbox_usize(v_i_2891_);
lean_dec(v_i_2891_);
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_boxed_2893_, v_i_boxed_2894_, v_bs_2892_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(lean_object* v_msg_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_ref_2902_; lean_object* v___x_2903_; lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2912_; 
v_ref_2902_ = lean_ctor_get(v___y_2899_, 5);
v___x_2903_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2910_; 
lean_inc(v_ref_2902_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_ref_2902_);
lean_ctor_set(v___x_2908_, 1, v_a_2904_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set_tag(v___x_2906_, 1);
lean_ctor_set(v___x_2906_, 0, v___x_2908_);
v___x_2910_ = v___x_2906_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg___boxed(lean_object* v_msg_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(lean_object* v_declName_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; lean_object* v_env_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2923_ = lean_st_ref_get(v___y_2921_);
v_env_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc_ref(v_env_2924_);
lean_dec(v___x_2923_);
v___x_2925_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2924_, v_declName_2920_);
v___x_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg___boxed(lean_object* v_declName_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_2927_, v___y_2928_);
lean_dec(v___y_2928_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(lean_object* v_ref_2931_, lean_object* v_msg_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_fileName_2941_; lean_object* v_fileMap_2942_; lean_object* v_options_2943_; lean_object* v_currRecDepth_2944_; lean_object* v_maxRecDepth_2945_; lean_object* v_ref_2946_; lean_object* v_currNamespace_2947_; lean_object* v_openDecls_2948_; lean_object* v_initHeartbeats_2949_; lean_object* v_maxHeartbeats_2950_; lean_object* v_quotContext_2951_; lean_object* v_currMacroScope_2952_; uint8_t v_diag_2953_; lean_object* v_cancelTk_x3f_2954_; uint8_t v_suppressElabErrors_2955_; lean_object* v_inheritedTraceOptions_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2965_; 
v_fileName_2941_ = lean_ctor_get(v___y_2938_, 0);
v_fileMap_2942_ = lean_ctor_get(v___y_2938_, 1);
v_options_2943_ = lean_ctor_get(v___y_2938_, 2);
v_currRecDepth_2944_ = lean_ctor_get(v___y_2938_, 3);
v_maxRecDepth_2945_ = lean_ctor_get(v___y_2938_, 4);
v_ref_2946_ = lean_ctor_get(v___y_2938_, 5);
v_currNamespace_2947_ = lean_ctor_get(v___y_2938_, 6);
v_openDecls_2948_ = lean_ctor_get(v___y_2938_, 7);
v_initHeartbeats_2949_ = lean_ctor_get(v___y_2938_, 8);
v_maxHeartbeats_2950_ = lean_ctor_get(v___y_2938_, 9);
v_quotContext_2951_ = lean_ctor_get(v___y_2938_, 10);
v_currMacroScope_2952_ = lean_ctor_get(v___y_2938_, 11);
v_diag_2953_ = lean_ctor_get_uint8(v___y_2938_, sizeof(void*)*14);
v_cancelTk_x3f_2954_ = lean_ctor_get(v___y_2938_, 12);
v_suppressElabErrors_2955_ = lean_ctor_get_uint8(v___y_2938_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2956_ = lean_ctor_get(v___y_2938_, 13);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___y_2938_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2958_ = v___y_2938_;
v_isShared_2959_ = v_isSharedCheck_2965_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_inheritedTraceOptions_2956_);
lean_inc(v_cancelTk_x3f_2954_);
lean_inc(v_currMacroScope_2952_);
lean_inc(v_quotContext_2951_);
lean_inc(v_maxHeartbeats_2950_);
lean_inc(v_initHeartbeats_2949_);
lean_inc(v_openDecls_2948_);
lean_inc(v_currNamespace_2947_);
lean_inc(v_ref_2946_);
lean_inc(v_maxRecDepth_2945_);
lean_inc(v_currRecDepth_2944_);
lean_inc(v_options_2943_);
lean_inc(v_fileMap_2942_);
lean_inc(v_fileName_2941_);
lean_dec(v___y_2938_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2965_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v_ref_2960_; lean_object* v___x_2962_; 
v_ref_2960_ = l_Lean_replaceRef(v_ref_2931_, v_ref_2946_);
lean_dec(v_ref_2946_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 5, v_ref_2960_);
v___x_2962_ = v___x_2958_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_fileName_2941_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_fileMap_2942_);
lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_options_2943_);
lean_ctor_set(v_reuseFailAlloc_2964_, 3, v_currRecDepth_2944_);
lean_ctor_set(v_reuseFailAlloc_2964_, 4, v_maxRecDepth_2945_);
lean_ctor_set(v_reuseFailAlloc_2964_, 5, v_ref_2960_);
lean_ctor_set(v_reuseFailAlloc_2964_, 6, v_currNamespace_2947_);
lean_ctor_set(v_reuseFailAlloc_2964_, 7, v_openDecls_2948_);
lean_ctor_set(v_reuseFailAlloc_2964_, 8, v_initHeartbeats_2949_);
lean_ctor_set(v_reuseFailAlloc_2964_, 9, v_maxHeartbeats_2950_);
lean_ctor_set(v_reuseFailAlloc_2964_, 10, v_quotContext_2951_);
lean_ctor_set(v_reuseFailAlloc_2964_, 11, v_currMacroScope_2952_);
lean_ctor_set(v_reuseFailAlloc_2964_, 12, v_cancelTk_x3f_2954_);
lean_ctor_set(v_reuseFailAlloc_2964_, 13, v_inheritedTraceOptions_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, sizeof(void*)*14, v_diag_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_2964_, sizeof(void*)*14 + 1, v_suppressElabErrors_2955_);
v___x_2962_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2932_, v___y_2936_, v___y_2937_, v___x_2962_, v___y_2939_);
lean_dec_ref(v___x_2962_);
return v___x_2963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2966_, lean_object* v_msg_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_2966_, v_msg_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec(v_ref_2966_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2977_, lean_object* v_declHint_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v___x_2981_; lean_object* v_env_2982_; uint8_t v___x_2983_; 
v___x_2981_ = lean_st_ref_get(v___y_2979_);
v_env_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc_ref(v_env_2982_);
lean_dec(v___x_2981_);
v___x_2983_ = l_Lean_Name_isAnonymous(v_declHint_2978_);
if (v___x_2983_ == 0)
{
uint8_t v_isExporting_2984_; 
v_isExporting_2984_ = lean_ctor_get_uint8(v_env_2982_, sizeof(void*)*8);
if (v_isExporting_2984_ == 0)
{
lean_object* v___x_2985_; 
lean_dec_ref(v_env_2982_);
lean_dec(v_declHint_2978_);
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_msg_2977_);
return v___x_2985_;
}
else
{
lean_object* v___x_2986_; uint8_t v___x_2987_; 
lean_inc_ref(v_env_2982_);
v___x_2986_ = l_Lean_Environment_setExporting(v_env_2982_, v___x_2983_);
lean_inc(v_declHint_2978_);
lean_inc_ref(v___x_2986_);
v___x_2987_ = l_Lean_Environment_contains(v___x_2986_, v_declHint_2978_, v_isExporting_2984_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; 
lean_dec_ref(v___x_2986_);
lean_dec_ref(v_env_2982_);
lean_dec(v_declHint_2978_);
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v_msg_2977_);
return v___x_2988_;
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v_c_2996_; lean_object* v___x_2997_; 
v___x_2989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2990_ = lean_unsigned_to_nat(32u);
v___x_2991_ = lean_mk_empty_array_with_capacity(v___x_2990_);
lean_dec_ref(v___x_2991_);
v___x_2992_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2993_ = l_Lean_Options_empty;
v___x_2994_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2986_);
lean_ctor_set(v___x_2994_, 1, v___x_2989_);
lean_ctor_set(v___x_2994_, 2, v___x_2992_);
lean_ctor_set(v___x_2994_, 3, v___x_2993_);
lean_inc(v_declHint_2978_);
v___x_2995_ = l_Lean_MessageData_ofConstName(v_declHint_2978_, v___x_2983_);
v_c_2996_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2996_, 0, v___x_2994_);
lean_ctor_set(v_c_2996_, 1, v___x_2995_);
v___x_2997_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2982_, v_declHint_2978_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec_ref(v_env_2982_);
lean_dec(v_declHint_2978_);
v___x_2998_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
lean_ctor_set(v___x_2999_, 1, v_c_2996_);
v___x_3000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_3001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
v___x_3002_ = l_Lean_MessageData_note(v___x_3001_);
v___x_3003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3003_, 0, v_msg_2977_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
return v___x_3004_;
}
else
{
lean_object* v_val_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3040_; 
v_val_3005_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3007_ = v___x_2997_;
v_isShared_3008_ = v_isSharedCheck_3040_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_val_3005_);
lean_dec(v___x_2997_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3040_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v_mod_3012_; uint8_t v___x_3013_; 
v___x_3009_ = lean_box(0);
v___x_3010_ = l_Lean_Environment_header(v_env_2982_);
lean_dec_ref(v_env_2982_);
v___x_3011_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3010_);
v_mod_3012_ = lean_array_get(v___x_3009_, v___x_3011_, v_val_3005_);
lean_dec(v_val_3005_);
lean_dec_ref(v___x_3011_);
v___x_3013_ = l_Lean_isPrivateName(v_declHint_2978_);
lean_dec(v_declHint_2978_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3014_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_3015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
lean_ctor_set(v___x_3015_, 1, v_c_2996_);
v___x_3016_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_3017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = l_Lean_MessageData_ofName(v_mod_3012_);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_3021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = l_Lean_MessageData_note(v___x_3021_);
v___x_3023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3023_, 0, v_msg_2977_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set_tag(v___x_3007_, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3023_);
v___x_3025_ = v___x_3007_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
v___x_3027_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_3028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v_c_2996_);
v___x_3029_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_3030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = l_Lean_MessageData_ofName(v_mod_3012_);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = l_Lean_MessageData_note(v___x_3034_);
v___x_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3036_, 0, v_msg_2977_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set_tag(v___x_3007_, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3036_);
v___x_3038_ = v___x_3007_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3041_; 
lean_dec_ref(v_env_2982_);
lean_dec(v_declHint_2978_);
v___x_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3041_, 0, v_msg_2977_);
return v___x_3041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_3042_, lean_object* v_declHint_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3042_, v_declHint_3043_, v___y_3044_);
lean_dec(v___y_3044_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(lean_object* v_msg_3047_, lean_object* v_declHint_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3057_; lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3067_; 
v___x_3057_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3047_, v_declHint_3048_, v___y_3055_);
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3067_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3067_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3062_ = l_Lean_unknownIdentifierMessageTag;
v___x_3063_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v_a_3058_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3063_);
v___x_3065_ = v___x_3060_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11___boxed(lean_object* v_msg_3068_, lean_object* v_declHint_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3068_, v_declHint_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object* v_ref_3079_, lean_object* v_msg_3080_, lean_object* v_declHint_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v___x_3090_; lean_object* v_a_3091_; lean_object* v___x_3092_; 
v___x_3090_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3080_, v_declHint_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref(v___x_3090_);
v___x_3092_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3079_, v_a_3091_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_ref_3093_, lean_object* v_msg_3094_, lean_object* v_declHint_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3093_, v_msg_3094_, v_declHint_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec(v_ref_3093_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(lean_object* v_ref_3105_, lean_object* v_constName_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; uint8_t v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3115_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3116_ = 0;
lean_inc(v_constName_3106_);
v___x_3117_ = l_Lean_MessageData_ofConstName(v_constName_3106_, v___x_3116_);
v___x_3118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3115_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
v___x_3119_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3118_);
lean_ctor_set(v___x_3120_, 1, v___x_3119_);
v___x_3121_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3105_, v___x_3120_, v_constName_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_ref_3122_, lean_object* v_constName_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3122_, v_constName_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec(v_ref_3122_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_ref_3142_; lean_object* v___x_3143_; 
v_ref_3142_ = lean_ctor_get(v___y_3139_, 5);
lean_inc(v_ref_3142_);
v___x_3143_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3142_, v_constName_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v_ref_3142_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(lean_object* v_constName_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v___x_3163_; lean_object* v_env_3164_; uint8_t v___x_3165_; lean_object* v___x_3166_; 
v___x_3163_ = lean_st_ref_get(v___y_3161_);
v_env_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc_ref(v_env_3164_);
lean_dec(v___x_3163_);
v___x_3165_ = 0;
lean_inc(v_constName_3154_);
v___x_3166_ = l_Lean_Environment_find_x3f(v_env_3164_, v_constName_3154_, v___x_3165_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
return v___x_3167_;
}
else
{
lean_object* v_val_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref(v___y_3160_);
lean_dec(v_constName_3154_);
v_val_3168_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3166_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_val_3168_);
lean_dec(v___x_3166_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set_tag(v___x_3170_, 0);
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_val_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0___boxed(lean_object* v_constName_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_constName_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
return v_res_3185_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(lean_object* v_msg_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v_toApplicative_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3266_; 
v___x_3200_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0);
v___x_3201_ = l_ReaderT_instMonad___redArg(v___x_3200_);
v_toApplicative_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; 
v_unused_3267_ = lean_ctor_get(v___x_3201_, 1);
lean_dec(v_unused_3267_);
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3266_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_toApplicative_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3266_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v_toFunctor_3206_; lean_object* v_toSeq_3207_; lean_object* v_toSeqLeft_3208_; lean_object* v_toSeqRight_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3264_; 
v_toFunctor_3206_ = lean_ctor_get(v_toApplicative_3202_, 0);
v_toSeq_3207_ = lean_ctor_get(v_toApplicative_3202_, 2);
v_toSeqLeft_3208_ = lean_ctor_get(v_toApplicative_3202_, 3);
v_toSeqRight_3209_ = lean_ctor_get(v_toApplicative_3202_, 4);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_toApplicative_3202_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; 
v_unused_3265_ = lean_ctor_get(v_toApplicative_3202_, 1);
lean_dec(v_unused_3265_);
v___x_3211_ = v_toApplicative_3202_;
v_isShared_3212_ = v_isSharedCheck_3264_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_toSeqRight_3209_);
lean_inc(v_toSeqLeft_3208_);
lean_inc(v_toSeq_3207_);
lean_inc(v_toFunctor_3206_);
lean_dec(v_toApplicative_3202_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3264_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___f_3213_; lean_object* v___f_3214_; lean_object* v___f_3215_; lean_object* v___f_3216_; lean_object* v___x_3217_; lean_object* v___f_3218_; lean_object* v___f_3219_; lean_object* v___f_3220_; lean_object* v___x_3222_; 
v___f_3213_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__1));
v___f_3214_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3206_);
v___f_3215_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3215_, 0, v_toFunctor_3206_);
v___f_3216_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3216_, 0, v_toFunctor_3206_);
v___x_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___f_3215_);
lean_ctor_set(v___x_3217_, 1, v___f_3216_);
v___f_3218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3218_, 0, v_toSeqRight_3209_);
v___f_3219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3219_, 0, v_toSeqLeft_3208_);
v___f_3220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3220_, 0, v_toSeq_3207_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 4, v___f_3218_);
lean_ctor_set(v___x_3211_, 3, v___f_3219_);
lean_ctor_set(v___x_3211_, 2, v___f_3220_);
lean_ctor_set(v___x_3211_, 1, v___f_3213_);
lean_ctor_set(v___x_3211_, 0, v___x_3217_);
v___x_3222_ = v___x_3211_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3217_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v___f_3213_);
lean_ctor_set(v_reuseFailAlloc_3263_, 2, v___f_3220_);
lean_ctor_set(v_reuseFailAlloc_3263_, 3, v___f_3219_);
lean_ctor_set(v_reuseFailAlloc_3263_, 4, v___f_3218_);
v___x_3222_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3224_; 
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v___f_3214_);
lean_ctor_set(v___x_3204_, 0, v___x_3222_);
v___x_3224_ = v___x_3204_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___f_3214_);
v___x_3224_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3225_; lean_object* v_toApplicative_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3260_; 
v___x_3225_ = l_ReaderT_instMonad___redArg(v___x_3224_);
v_toApplicative_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3260_ == 0)
{
lean_object* v_unused_3261_; 
v_unused_3261_ = lean_ctor_get(v___x_3225_, 1);
lean_dec(v_unused_3261_);
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3260_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_toApplicative_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3260_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_toFunctor_3230_; lean_object* v_toSeq_3231_; lean_object* v_toSeqLeft_3232_; lean_object* v_toSeqRight_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3258_; 
v_toFunctor_3230_ = lean_ctor_get(v_toApplicative_3226_, 0);
v_toSeq_3231_ = lean_ctor_get(v_toApplicative_3226_, 2);
v_toSeqLeft_3232_ = lean_ctor_get(v_toApplicative_3226_, 3);
v_toSeqRight_3233_ = lean_ctor_get(v_toApplicative_3226_, 4);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_toApplicative_3226_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; 
v_unused_3259_ = lean_ctor_get(v_toApplicative_3226_, 1);
lean_dec(v_unused_3259_);
v___x_3235_ = v_toApplicative_3226_;
v_isShared_3236_ = v_isSharedCheck_3258_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_toSeqRight_3233_);
lean_inc(v_toSeqLeft_3232_);
lean_inc(v_toSeq_3231_);
lean_inc(v_toFunctor_3230_);
lean_dec(v_toApplicative_3226_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3258_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___f_3237_; lean_object* v___f_3238_; lean_object* v___f_3239_; lean_object* v___f_3240_; lean_object* v___x_3241_; lean_object* v___f_3242_; lean_object* v___f_3243_; lean_object* v___f_3244_; lean_object* v___x_3246_; 
v___f_3237_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__3));
v___f_3238_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3230_);
v___f_3239_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3239_, 0, v_toFunctor_3230_);
v___f_3240_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3240_, 0, v_toFunctor_3230_);
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___f_3239_);
lean_ctor_set(v___x_3241_, 1, v___f_3240_);
v___f_3242_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3242_, 0, v_toSeqRight_3233_);
v___f_3243_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3243_, 0, v_toSeqLeft_3232_);
v___f_3244_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3244_, 0, v_toSeq_3231_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 4, v___f_3242_);
lean_ctor_set(v___x_3235_, 3, v___f_3243_);
lean_ctor_set(v___x_3235_, 2, v___f_3244_);
lean_ctor_set(v___x_3235_, 1, v___f_3237_);
lean_ctor_set(v___x_3235_, 0, v___x_3241_);
v___x_3246_ = v___x_3235_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v___f_3237_);
lean_ctor_set(v_reuseFailAlloc_3257_, 2, v___f_3244_);
lean_ctor_set(v_reuseFailAlloc_3257_, 3, v___f_3243_);
lean_ctor_set(v_reuseFailAlloc_3257_, 4, v___f_3242_);
v___x_3246_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3248_; 
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 1, v___f_3238_);
lean_ctor_set(v___x_3228_, 0, v___x_3246_);
v___x_3248_ = v___x_3228_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___f_3238_);
v___x_3248_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_49367__overap_3254_; lean_object* v___x_3255_; 
v___x_3249_ = l_ReaderT_instMonad___redArg(v___x_3248_);
v___x_3250_ = l_ReaderT_instMonad___redArg(v___x_3249_);
v___x_3251_ = l_ReaderT_instMonad___redArg(v___x_3250_);
v___x_3252_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3253_ = l_instInhabitedOfMonad___redArg(v___x_3251_, v___x_3252_);
v___x_49367__overap_3254_ = lean_panic_fn(v___x_3253_, v_msg_3191_);
v___x_3255_ = lean_apply_8(v___x_49367__overap_3254_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, lean_box(0));
return v___x_3255_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___boxed(lean_object* v_msg_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v_msg_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
return v_res_3277_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__2));
v___x_3282_ = lean_unsigned_to_nat(53u);
v___x_3283_ = lean_unsigned_to_nat(62u);
v___x_3284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__1));
v___x_3285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__0));
v___x_3286_ = l_mkPanicMessageWithDecl(v___x_3285_, v___x_3284_, v___x_3283_, v___x_3282_, v___x_3281_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(size_t v_sz_3287_, size_t v_i_3288_, lean_object* v_bs_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
uint8_t v___x_3298_; 
v___x_3298_ = lean_usize_dec_lt(v_i_3288_, v_sz_3287_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; 
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
v___x_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3299_, 0, v_bs_3289_);
return v___x_3299_;
}
else
{
lean_object* v_v_3300_; lean_object* v___x_3301_; 
v_v_3300_ = lean_array_uget_borrowed(v_bs_3289_, v_i_3288_);
lean_inc_ref(v___y_3295_);
lean_inc(v_v_3300_);
v___x_3301_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_v_3300_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3303_; lean_object* v_bs_x27_3304_; lean_object* v_a_3306_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref(v___x_3301_);
v___x_3303_ = lean_unsigned_to_nat(0u);
v_bs_x27_3304_ = lean_array_uset(v_bs_3289_, v_i_3288_, v___x_3303_);
if (lean_obj_tag(v_a_3302_) == 6)
{
lean_object* v_val_3311_; lean_object* v_numFields_3312_; uint8_t v___x_3313_; lean_object* v___x_3314_; 
v_val_3311_ = lean_ctor_get(v_a_3302_, 0);
lean_inc_ref(v_val_3311_);
lean_dec_ref(v_a_3302_);
v_numFields_3312_ = lean_ctor_get(v_val_3311_, 4);
lean_inc(v_numFields_3312_);
lean_dec_ref(v_val_3311_);
v___x_3313_ = 0;
v___x_3314_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3314_, 0, v_numFields_3312_);
lean_ctor_set(v___x_3314_, 1, v___x_3303_);
lean_ctor_set_uint8(v___x_3314_, sizeof(void*)*2, v___x_3313_);
v_a_3306_ = v___x_3314_;
goto v___jp_3305_;
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec(v_a_3302_);
v___x_3315_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3);
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3295_);
lean_inc(v___y_3294_);
lean_inc_ref(v___y_3293_);
lean_inc(v___y_3292_);
lean_inc_ref(v___y_3291_);
lean_inc(v___y_3290_);
v___x_3316_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v___x_3315_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref(v___x_3316_);
v_a_3306_ = v_a_3317_;
goto v___jp_3305_;
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec_ref(v_bs_x27_3304_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
v_a_3318_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3316_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3316_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
v___jp_3305_:
{
size_t v___x_3307_; size_t v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = ((size_t)1ULL);
v___x_3308_ = lean_usize_add(v_i_3288_, v___x_3307_);
v___x_3309_ = lean_array_uset(v_bs_x27_3304_, v_i_3288_, v_a_3306_);
v_i_3288_ = v___x_3308_;
v_bs_3289_ = v___x_3309_;
goto _start;
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v_bs_3289_);
v_a_3326_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3301_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3301_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___boxed(lean_object* v_sz_3334_, lean_object* v_i_3335_, lean_object* v_bs_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
size_t v_sz_boxed_3345_; size_t v_i_boxed_3346_; lean_object* v_res_3347_; 
v_sz_boxed_3345_ = lean_unbox_usize(v_sz_3334_);
lean_dec(v_sz_3334_);
v_i_boxed_3346_ = lean_unbox_usize(v_i_3335_);
lean_dec(v_i_3335_);
v_res_3347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_boxed_3345_, v_i_boxed_3346_, v_bs_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
return v_res_3347_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = lean_box(0);
v___x_3349_ = lean_unsigned_to_nat(16u);
v___x_3350_ = lean_mk_array(v___x_3349_, v___x_3348_);
return v___x_3350_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3351_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0);
v___x_3352_ = lean_unsigned_to_nat(0u);
v___x_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
lean_ctor_set(v___x_3353_, 1, v___x_3351_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(lean_object* v_e_3356_, uint8_t v_alsoCasesOn_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
uint8_t v___x_3369_; 
v___x_3369_ = l_Lean_Expr_isApp(v_e_3356_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v_e_3356_);
v___x_3370_ = lean_box(0);
v___x_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3370_);
return v___x_3371_;
}
else
{
lean_object* v___x_3372_; 
v___x_3372_ = l_Lean_Expr_getAppFn(v_e_3356_);
if (lean_obj_tag(v___x_3372_) == 4)
{
lean_object* v_declName_3373_; lean_object* v_us_3374_; lean_object* v___x_3375_; lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3530_; 
v_declName_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_declName_3373_);
v_us_3374_ = lean_ctor_get(v___x_3372_, 1);
lean_inc(v_us_3374_);
lean_dec_ref(v___x_3372_);
lean_inc(v_declName_3373_);
v___x_3375_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3373_, v___y_3364_);
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3378_ = v___x_3375_;
v_isShared_3379_ = v_isSharedCheck_3530_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3375_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3530_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
if (lean_obj_tag(v_a_3376_) == 1)
{
lean_object* v_val_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
v_val_3380_ = lean_ctor_get(v_a_3376_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_a_3376_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3382_ = v_a_3376_;
v_isShared_3383_ = v_isSharedCheck_3422_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_val_3380_);
lean_dec(v_a_3376_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3422_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v_dummy_3384_; lean_object* v_nargs_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v_args_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v_dummy_3384_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_3385_ = l_Lean_Expr_getAppNumArgs(v_e_3356_);
lean_inc(v_nargs_3385_);
v___x_3386_ = lean_mk_array(v_nargs_3385_, v_dummy_3384_);
v___x_3387_ = lean_unsigned_to_nat(1u);
v___x_3388_ = lean_nat_sub(v_nargs_3385_, v___x_3387_);
lean_dec(v_nargs_3385_);
v_args_3389_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3356_, v___x_3386_, v___x_3388_);
v___x_3390_ = lean_array_get_size(v_args_3389_);
v___x_3391_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_3380_);
v___x_3392_ = lean_nat_dec_lt(v___x_3390_, v___x_3391_);
lean_dec(v___x_3391_);
if (v___x_3392_ == 0)
{
lean_object* v_numParams_3393_; lean_object* v_numDiscrs_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3413_; 
v_numParams_3393_ = lean_ctor_get(v_val_3380_, 0);
v_numDiscrs_3394_ = lean_ctor_get(v_val_3380_, 1);
v___x_3395_ = lean_array_mk(v_us_3374_);
v___x_3396_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3393_);
v___x_3397_ = l_Array_extract___redArg(v_args_3389_, v___x_3396_, v_numParams_3393_);
v___x_3398_ = l_Lean_instInhabitedExpr;
v___x_3399_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3380_);
v___x_3400_ = lean_array_get(v___x_3398_, v_args_3389_, v___x_3399_);
lean_dec(v___x_3399_);
v___x_3401_ = lean_nat_add(v_numParams_3393_, v___x_3387_);
v___x_3402_ = lean_nat_add(v___x_3401_, v_numDiscrs_3394_);
lean_inc(v___x_3402_);
lean_inc_ref(v_args_3389_);
v___x_3403_ = l_Array_toSubarray___redArg(v_args_3389_, v___x_3401_, v___x_3402_);
v___x_3404_ = l_Subarray_copy___redArg(v___x_3403_);
v___x_3405_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3380_);
v___x_3406_ = lean_nat_add(v___x_3402_, v___x_3405_);
lean_dec(v___x_3405_);
lean_inc(v___x_3406_);
lean_inc_ref(v_args_3389_);
v___x_3407_ = l_Array_toSubarray___redArg(v_args_3389_, v___x_3402_, v___x_3406_);
v___x_3408_ = l_Subarray_copy___redArg(v___x_3407_);
v___x_3409_ = l_Array_toSubarray___redArg(v_args_3389_, v___x_3406_, v___x_3390_);
v___x_3410_ = l_Subarray_copy___redArg(v___x_3409_);
v___x_3411_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3411_, 0, v_val_3380_);
lean_ctor_set(v___x_3411_, 1, v_declName_3373_);
lean_ctor_set(v___x_3411_, 2, v___x_3395_);
lean_ctor_set(v___x_3411_, 3, v___x_3397_);
lean_ctor_set(v___x_3411_, 4, v___x_3400_);
lean_ctor_set(v___x_3411_, 5, v___x_3404_);
lean_ctor_set(v___x_3411_, 6, v___x_3408_);
lean_ctor_set(v___x_3411_, 7, v___x_3410_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3411_);
v___x_3413_ = v___x_3382_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3415_; 
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___x_3413_);
v___x_3415_ = v___x_3378_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
lean_dec_ref(v_args_3389_);
lean_del_object(v___x_3382_);
lean_dec(v_val_3380_);
lean_dec(v_us_3374_);
lean_dec(v_declName_3373_);
v___x_3418_ = lean_box(0);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___x_3418_);
v___x_3420_ = v___x_3378_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
else
{
lean_object* v___x_3423_; 
lean_del_object(v___x_3378_);
lean_dec(v_a_3376_);
v___x_3423_ = lean_st_ref_get(v___y_3364_);
if (v_alsoCasesOn_3357_ == 0)
{
lean_dec(v___x_3423_);
lean_dec(v_us_3374_);
lean_dec(v_declName_3373_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v_e_3356_);
goto v___jp_3366_;
}
else
{
lean_object* v_env_3424_; uint8_t v___x_3425_; 
v_env_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc_ref(v_env_3424_);
lean_dec(v___x_3423_);
lean_inc(v_declName_3373_);
v___x_3425_ = l_Lean_isCasesOnRecursor(v_env_3424_, v_declName_3373_);
if (v___x_3425_ == 0)
{
lean_dec(v_us_3374_);
lean_dec(v_declName_3373_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v_e_3356_);
goto v___jp_3366_;
}
else
{
lean_object* v_indName_3426_; lean_object* v___x_3427_; 
v_indName_3426_ = l_Lean_Name_getPrefix(v_declName_3373_);
lean_inc_ref(v___y_3363_);
v___x_3427_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_indName_3426_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3521_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3430_ = v___x_3427_;
v_isShared_3431_ = v_isSharedCheck_3521_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3521_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
if (lean_obj_tag(v_a_3428_) == 5)
{
lean_object* v_val_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3516_; 
v_val_3432_ = lean_ctor_get(v_a_3428_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_a_3428_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3434_ = v_a_3428_;
v_isShared_3435_ = v_isSharedCheck_3516_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_val_3432_);
lean_dec(v_a_3428_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3516_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v_toConstantVal_3436_; lean_object* v_numParams_3437_; lean_object* v_numIndices_3438_; lean_object* v_ctors_3439_; lean_object* v_nargs_3440_; lean_object* v_dummy_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v_args_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
v_toConstantVal_3436_ = lean_ctor_get(v_val_3432_, 0);
lean_inc_ref(v_toConstantVal_3436_);
v_numParams_3437_ = lean_ctor_get(v_val_3432_, 1);
lean_inc(v_numParams_3437_);
v_numIndices_3438_ = lean_ctor_get(v_val_3432_, 2);
lean_inc(v_numIndices_3438_);
v_ctors_3439_ = lean_ctor_get(v_val_3432_, 4);
lean_inc(v_ctors_3439_);
v_nargs_3440_ = l_Lean_Expr_getAppNumArgs(v_e_3356_);
v_dummy_3441_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_3440_);
v___x_3442_ = lean_mk_array(v_nargs_3440_, v_dummy_3441_);
v___x_3443_ = lean_unsigned_to_nat(1u);
v___x_3444_ = lean_nat_sub(v_nargs_3440_, v___x_3443_);
lean_dec(v_nargs_3440_);
v_args_3445_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3356_, v___x_3442_, v___x_3444_);
v___x_3446_ = lean_nat_add(v_numParams_3437_, v___x_3443_);
v___x_3447_ = lean_nat_add(v___x_3446_, v_numIndices_3438_);
v___x_3448_ = lean_nat_add(v___x_3447_, v___x_3443_);
lean_dec(v___x_3447_);
v___x_3449_ = l_Lean_InductiveVal_numCtors(v_val_3432_);
lean_dec_ref(v_val_3432_);
v___x_3450_ = lean_nat_add(v___x_3448_, v___x_3449_);
lean_dec(v___x_3449_);
v___x_3451_ = lean_array_get_size(v_args_3445_);
v___x_3452_ = lean_nat_dec_le(v___x_3450_, v___x_3451_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3455_; 
lean_dec(v___x_3450_);
lean_dec(v___x_3448_);
lean_dec(v___x_3446_);
lean_dec_ref(v_args_3445_);
lean_dec(v_ctors_3439_);
lean_dec(v_numIndices_3438_);
lean_dec(v_numParams_3437_);
lean_dec_ref(v_toConstantVal_3436_);
lean_del_object(v___x_3434_);
lean_dec(v_us_3374_);
lean_dec(v_declName_3373_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
v___x_3453_ = lean_box(0);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3453_);
v___x_3455_ = v___x_3430_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
else
{
lean_object* v___x_3457_; lean_object* v_params_3458_; lean_object* v___x_3459_; lean_object* v_motive_3460_; lean_object* v_discrs_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v_discrInfos_3464_; lean_object* v_alts_3465_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v_lower_3507_; lean_object* v_upper_3508_; uint8_t v___x_3515_; 
lean_del_object(v___x_3430_);
v___x_3457_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3437_);
lean_inc_ref(v_args_3445_);
v_params_3458_ = l_Array_toSubarray___redArg(v_args_3445_, v___x_3457_, v_numParams_3437_);
v___x_3459_ = l_Lean_instInhabitedExpr;
v_motive_3460_ = lean_array_get(v___x_3459_, v_args_3445_, v_numParams_3437_);
lean_dec(v_numParams_3437_);
lean_inc(v___x_3448_);
lean_inc_ref(v_args_3445_);
v_discrs_3461_ = l_Array_toSubarray___redArg(v_args_3445_, v___x_3446_, v___x_3448_);
v___x_3462_ = lean_nat_add(v_numIndices_3438_, v___x_3443_);
lean_dec(v_numIndices_3438_);
v___x_3463_ = lean_box(0);
v_discrInfos_3464_ = lean_mk_array(v___x_3462_, v___x_3463_);
lean_inc(v___x_3450_);
lean_inc_ref(v_args_3445_);
v_alts_3465_ = l_Array_toSubarray___redArg(v_args_3445_, v___x_3448_, v___x_3450_);
v___x_3515_ = lean_nat_dec_le(v___x_3450_, v___x_3457_);
if (v___x_3515_ == 0)
{
v_lower_3507_ = v___x_3450_;
v_upper_3508_ = v___x_3451_;
goto v___jp_3506_;
}
else
{
lean_dec(v___x_3450_);
v_lower_3507_ = v___x_3457_;
v_upper_3508_ = v___x_3451_;
goto v___jp_3506_;
}
v___jp_3466_:
{
lean_object* v___x_3469_; size_t v_sz_3470_; size_t v___x_3471_; lean_object* v___x_3472_; 
v___x_3469_ = lean_array_mk(v_ctors_3439_);
v_sz_3470_ = lean_array_size(v___x_3469_);
v___x_3471_ = ((size_t)0ULL);
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_3470_, v___x_3471_, v___x_3469_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3497_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3475_ = v___x_3472_;
v_isShared_3476_ = v_isSharedCheck_3497_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3497_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v_start_3477_; lean_object* v_stop_3478_; lean_object* v_start_3479_; lean_object* v_stop_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
v_start_3477_ = lean_ctor_get(v_params_3458_, 1);
lean_inc(v_start_3477_);
v_stop_3478_ = lean_ctor_get(v_params_3458_, 2);
lean_inc(v_stop_3478_);
v_start_3479_ = lean_ctor_get(v_discrs_3461_, 1);
lean_inc(v_start_3479_);
v_stop_3480_ = lean_ctor_get(v_discrs_3461_, 2);
lean_inc(v_stop_3480_);
v___x_3481_ = lean_nat_sub(v_stop_3478_, v_start_3477_);
lean_dec(v_start_3477_);
lean_dec(v_stop_3478_);
v___x_3482_ = lean_nat_sub(v_stop_3480_, v_start_3479_);
lean_dec(v_start_3479_);
lean_dec(v_stop_3480_);
v___x_3483_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1);
v___x_3484_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3481_);
lean_ctor_set(v___x_3484_, 1, v___x_3482_);
lean_ctor_set(v___x_3484_, 2, v_a_3473_);
lean_ctor_set(v___x_3484_, 3, v___y_3468_);
lean_ctor_set(v___x_3484_, 4, v_discrInfos_3464_);
lean_ctor_set(v___x_3484_, 5, v___x_3483_);
v___x_3485_ = lean_array_mk(v_us_3374_);
v___x_3486_ = l_Subarray_copy___redArg(v_params_3458_);
v___x_3487_ = l_Subarray_copy___redArg(v_discrs_3461_);
v___x_3488_ = l_Subarray_copy___redArg(v_alts_3465_);
v___x_3489_ = l_Subarray_copy___redArg(v___y_3467_);
v___x_3490_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3484_);
lean_ctor_set(v___x_3490_, 1, v_declName_3373_);
lean_ctor_set(v___x_3490_, 2, v___x_3485_);
lean_ctor_set(v___x_3490_, 3, v___x_3486_);
lean_ctor_set(v___x_3490_, 4, v_motive_3460_);
lean_ctor_set(v___x_3490_, 5, v___x_3487_);
lean_ctor_set(v___x_3490_, 6, v___x_3488_);
lean_ctor_set(v___x_3490_, 7, v___x_3489_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 1);
lean_ctor_set(v___x_3434_, 0, v___x_3490_);
v___x_3492_ = v___x_3434_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3492_);
v___x_3494_ = v___x_3475_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec_ref(v_alts_3465_);
lean_dec_ref(v_discrInfos_3464_);
lean_dec_ref(v_discrs_3461_);
lean_dec(v_motive_3460_);
lean_dec_ref(v_params_3458_);
lean_del_object(v___x_3434_);
lean_dec(v_us_3374_);
lean_dec(v_declName_3373_);
v_a_3498_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3472_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3472_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
v___jp_3506_:
{
lean_object* v_levelParams_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; 
v_levelParams_3509_ = lean_ctor_get(v_toConstantVal_3436_, 1);
lean_inc(v_levelParams_3509_);
lean_dec_ref(v_toConstantVal_3436_);
v___x_3510_ = l_Array_toSubarray___redArg(v_args_3445_, v_lower_3507_, v_upper_3508_);
v___x_3511_ = l_List_lengthTR___redArg(v_levelParams_3509_);
lean_dec(v_levelParams_3509_);
v___x_3512_ = l_List_lengthTR___redArg(v_us_3374_);
v___x_3513_ = lean_nat_dec_eq(v___x_3511_, v___x_3512_);
lean_dec(v___x_3512_);
lean_dec(v___x_3511_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; 
v___x_3514_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__2));
v___y_3467_ = v___x_3510_;
v___y_3468_ = v___x_3514_;
goto v___jp_3466_;
}
else
{
v___y_3467_ = v___x_3510_;
v___y_3468_ = v___x_3463_;
goto v___jp_3466_;
}
}
}
}
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
lean_dec(v_a_3428_);
lean_dec(v_us_3374_);
lean_dec(v_declName_3373_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v_e_3356_);
v___x_3517_ = lean_box(0);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3517_);
v___x_3519_ = v___x_3430_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec(v_us_3374_);
lean_dec(v_declName_3373_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v_e_3356_);
v_a_3522_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3427_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3427_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
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
lean_dec_ref(v___x_3372_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v_e_3356_);
goto v___jp_3366_;
}
}
v___jp_3366_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = lean_box(0);
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
return v___x_3368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___boxed(lean_object* v_e_3531_, lean_object* v_alsoCasesOn_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
uint8_t v_alsoCasesOn_boxed_3541_; lean_object* v_res_3542_; 
v_alsoCasesOn_boxed_3541_ = lean_unbox(v_alsoCasesOn_3532_);
v_res_3542_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3531_, v_alsoCasesOn_boxed_3541_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
return v_res_3542_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__1));
v___x_3547_ = l_Lean_stringToMessageData(v___x_3546_);
return v___x_3547_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3(void){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = lean_unsigned_to_nat(1u);
v___x_3549_ = l_Lean_Expr_bvar___override(v___x_3548_);
return v___x_3549_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3552_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__5));
v___x_3553_ = lean_unsigned_to_nat(2u);
v___x_3554_ = lean_unsigned_to_nat(181u);
v___x_3555_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__4));
v___x_3556_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_3557_ = l_mkPanicMessageWithDecl(v___x_3556_, v___x_3555_, v___x_3554_, v___x_3553_, v___x_3552_);
return v___x_3557_;
}
}
static uint64_t _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7(void){
_start:
{
uint8_t v___x_3558_; uint64_t v___x_3559_; 
v___x_3558_ = 0;
v___x_3559_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(lean_object* v_e_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
lean_object* v_e_3569_; uint8_t v___x_3570_; lean_object* v___x_3571_; 
v_e_3569_ = l_Lean_Expr_headBeta(v_e_3560_);
v___x_3570_ = 1;
lean_inc(v_a_3567_);
lean_inc_ref(v_a_3566_);
lean_inc(v_a_3565_);
lean_inc_ref(v_a_3564_);
lean_inc(v_a_3563_);
lean_inc_ref(v_a_3562_);
lean_inc(v_a_3561_);
v___x_3571_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3569_, v___x_3570_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3861_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3861_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3861_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
if (lean_obj_tag(v_a_3572_) == 1)
{
lean_object* v_val_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3856_; 
v_val_3576_ = lean_ctor_get(v_a_3572_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v_a_3572_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3578_ = v_a_3572_;
v_isShared_3579_ = v_isSharedCheck_3856_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_val_3576_);
lean_dec(v_a_3572_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3856_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v_toMatcherInfo_3580_; lean_object* v_matcherName_3581_; lean_object* v_params_3582_; lean_object* v_motive_3583_; lean_object* v_discrs_3584_; lean_object* v_alts_3585_; lean_object* v_remaining_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; 
v_toMatcherInfo_3580_ = lean_ctor_get(v_val_3576_, 0);
lean_inc_ref(v_toMatcherInfo_3580_);
v_matcherName_3581_ = lean_ctor_get(v_val_3576_, 1);
lean_inc(v_matcherName_3581_);
v_params_3582_ = lean_ctor_get(v_val_3576_, 3);
lean_inc_ref(v_params_3582_);
v_motive_3583_ = lean_ctor_get(v_val_3576_, 4);
lean_inc_ref(v_motive_3583_);
v_discrs_3584_ = lean_ctor_get(v_val_3576_, 5);
lean_inc_ref(v_discrs_3584_);
v_alts_3585_ = lean_ctor_get(v_val_3576_, 6);
lean_inc_ref(v_alts_3585_);
v_remaining_3586_ = lean_ctor_get(v_val_3576_, 7);
lean_inc_ref(v_remaining_3586_);
v___x_3587_ = lean_unsigned_to_nat(0u);
v___x_3588_ = lean_array_get_size(v_remaining_3586_);
v___x_3589_ = lean_nat_dec_lt(v___x_3587_, v___x_3588_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; lean_object* v___x_3592_; 
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_val_3576_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v___x_3590_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3590_);
v___x_3592_ = v___x_3574_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
else
{
lean_object* v___x_3594_; uint8_t v___x_3595_; 
v___x_3594_ = lean_array_fget_borrowed(v_remaining_3586_, v___x_3587_);
v___x_3595_ = l_Lean_Expr_isLambda(v___x_3594_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3598_; 
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_val_3576_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v___x_3596_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3596_);
v___x_3598_ = v___x_3574_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
else
{
lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3600_ = l_Lean_Expr_bindingBody_x21(v___x_3594_);
v___x_3601_ = l_Lean_Expr_isLambda(v___x_3600_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
lean_dec_ref(v___x_3600_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_val_3576_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v___x_3602_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3602_);
v___x_3604_ = v___x_3574_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
else
{
lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3606_ = l_Lean_Expr_bindingBody_x21(v___x_3600_);
lean_dec_ref(v___x_3600_);
v___x_3607_ = l_Lean_Expr_isApp(v___x_3606_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
lean_dec_ref(v___x_3606_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_val_3576_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v___x_3608_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3608_);
v___x_3610_ = v___x_3574_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
else
{
uint8_t v___x_3612_; 
v___x_3612_ = lean_expr_has_loose_bvar(v___x_3606_, v___x_3587_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v_a_3616_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3613_ = l_Lean_Expr_appArg_x21(v___x_3606_);
v___x_3614_ = lean_unsigned_to_nat(1u);
v___x_3670_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3);
v___x_3671_ = lean_expr_eqv(v___x_3613_, v___x_3670_);
lean_dec_ref(v___x_3613_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3674_; 
lean_dec_ref(v___x_3606_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_val_3576_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v___x_3672_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3672_);
v___x_3674_ = v___x_3574_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3672_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
else
{
lean_object* v___x_3676_; uint8_t v___x_3677_; 
v___x_3676_ = l_Lean_Expr_appFn_x21(v___x_3606_);
lean_dec_ref(v___x_3606_);
v___x_3677_ = lean_expr_has_loose_bvar(v___x_3676_, v___x_3614_);
if (v___x_3677_ == 0)
{
lean_object* v___x_3678_; 
lean_del_object(v___x_3574_);
lean_inc(v_a_3567_);
lean_inc_ref(v_a_3566_);
lean_inc(v_a_3565_);
lean_inc_ref(v_a_3564_);
lean_inc_ref(v___x_3676_);
v___x_3678_ = lean_infer_type(v___x_3676_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; uint8_t v_foApprox_3681_; uint8_t v_ctxApprox_3682_; uint8_t v_quasiPatternApprox_3683_; uint8_t v_constApprox_3684_; uint8_t v_isDefEqStuckEx_3685_; uint8_t v_unificationHints_3686_; uint8_t v_proofIrrelevance_3687_; uint8_t v_assignSyntheticOpaque_3688_; uint8_t v_offsetCnstrs_3689_; uint8_t v_etaStruct_3690_; uint8_t v_univApprox_3691_; uint8_t v_iota_3692_; uint8_t v_beta_3693_; uint8_t v_proj_3694_; uint8_t v_zeta_3695_; uint8_t v_zetaDelta_3696_; uint8_t v_zetaUnused_3697_; uint8_t v_zetaHave_3698_; uint8_t v_trackZetaDelta_3699_; lean_object* v_zetaDeltaSet_3700_; lean_object* v_lctx_3701_; lean_object* v_localInstances_3702_; lean_object* v_defEqCtx_x3f_3703_; lean_object* v_synthPendingDepth_3704_; lean_object* v_canUnfold_x3f_3705_; uint8_t v_univApprox_3706_; uint8_t v_inTypeClassResolution_3707_; uint8_t v_cacheInferType_3708_; uint8_t v___x_3709_; lean_object* v_a_3711_; lean_object* v_config_3820_; uint64_t v___x_3821_; uint64_t v___x_3822_; uint64_t v___x_3823_; uint64_t v___x_3824_; uint64_t v___x_3825_; uint64_t v_key_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref(v___x_3678_);
v___x_3680_ = l_Lean_Meta_Context_config(v_a_3564_);
v_foApprox_3681_ = lean_ctor_get_uint8(v___x_3680_, 0);
v_ctxApprox_3682_ = lean_ctor_get_uint8(v___x_3680_, 1);
v_quasiPatternApprox_3683_ = lean_ctor_get_uint8(v___x_3680_, 2);
v_constApprox_3684_ = lean_ctor_get_uint8(v___x_3680_, 3);
v_isDefEqStuckEx_3685_ = lean_ctor_get_uint8(v___x_3680_, 4);
v_unificationHints_3686_ = lean_ctor_get_uint8(v___x_3680_, 5);
v_proofIrrelevance_3687_ = lean_ctor_get_uint8(v___x_3680_, 6);
v_assignSyntheticOpaque_3688_ = lean_ctor_get_uint8(v___x_3680_, 7);
v_offsetCnstrs_3689_ = lean_ctor_get_uint8(v___x_3680_, 8);
v_etaStruct_3690_ = lean_ctor_get_uint8(v___x_3680_, 10);
v_univApprox_3691_ = lean_ctor_get_uint8(v___x_3680_, 11);
v_iota_3692_ = lean_ctor_get_uint8(v___x_3680_, 12);
v_beta_3693_ = lean_ctor_get_uint8(v___x_3680_, 13);
v_proj_3694_ = lean_ctor_get_uint8(v___x_3680_, 14);
v_zeta_3695_ = lean_ctor_get_uint8(v___x_3680_, 15);
v_zetaDelta_3696_ = lean_ctor_get_uint8(v___x_3680_, 16);
v_zetaUnused_3697_ = lean_ctor_get_uint8(v___x_3680_, 17);
v_zetaHave_3698_ = lean_ctor_get_uint8(v___x_3680_, 18);
v_trackZetaDelta_3699_ = lean_ctor_get_uint8(v_a_3564_, sizeof(void*)*7);
v_zetaDeltaSet_3700_ = lean_ctor_get(v_a_3564_, 1);
v_lctx_3701_ = lean_ctor_get(v_a_3564_, 2);
v_localInstances_3702_ = lean_ctor_get(v_a_3564_, 3);
v_defEqCtx_x3f_3703_ = lean_ctor_get(v_a_3564_, 4);
v_synthPendingDepth_3704_ = lean_ctor_get(v_a_3564_, 5);
v_canUnfold_x3f_3705_ = lean_ctor_get(v_a_3564_, 6);
v_univApprox_3706_ = lean_ctor_get_uint8(v_a_3564_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3707_ = lean_ctor_get_uint8(v_a_3564_, sizeof(void*)*7 + 2);
v_cacheInferType_3708_ = lean_ctor_get_uint8(v_a_3564_, sizeof(void*)*7 + 3);
v___x_3709_ = 0;
v_config_3820_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_config_3820_, 0, v_foApprox_3681_);
lean_ctor_set_uint8(v_config_3820_, 1, v_ctxApprox_3682_);
lean_ctor_set_uint8(v_config_3820_, 2, v_quasiPatternApprox_3683_);
lean_ctor_set_uint8(v_config_3820_, 3, v_constApprox_3684_);
lean_ctor_set_uint8(v_config_3820_, 4, v_isDefEqStuckEx_3685_);
lean_ctor_set_uint8(v_config_3820_, 5, v_unificationHints_3686_);
lean_ctor_set_uint8(v_config_3820_, 6, v_proofIrrelevance_3687_);
lean_ctor_set_uint8(v_config_3820_, 7, v_assignSyntheticOpaque_3688_);
lean_ctor_set_uint8(v_config_3820_, 8, v_offsetCnstrs_3689_);
lean_ctor_set_uint8(v_config_3820_, 9, v___x_3709_);
lean_ctor_set_uint8(v_config_3820_, 10, v_etaStruct_3690_);
lean_ctor_set_uint8(v_config_3820_, 11, v_univApprox_3691_);
lean_ctor_set_uint8(v_config_3820_, 12, v_iota_3692_);
lean_ctor_set_uint8(v_config_3820_, 13, v_beta_3693_);
lean_ctor_set_uint8(v_config_3820_, 14, v_proj_3694_);
lean_ctor_set_uint8(v_config_3820_, 15, v_zeta_3695_);
lean_ctor_set_uint8(v_config_3820_, 16, v_zetaDelta_3696_);
lean_ctor_set_uint8(v_config_3820_, 17, v_zetaUnused_3697_);
lean_ctor_set_uint8(v_config_3820_, 18, v_zetaHave_3698_);
v___x_3821_ = l_Lean_Meta_Context_configKey(v_a_3564_);
v___x_3822_ = 2ULL;
v___x_3823_ = lean_uint64_shift_right(v___x_3821_, v___x_3822_);
v___x_3824_ = lean_uint64_shift_left(v___x_3823_, v___x_3822_);
v___x_3825_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7);
v_key_3826_ = lean_uint64_lor(v___x_3824_, v___x_3825_);
v___x_3827_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3827_, 0, v_config_3820_);
lean_ctor_set_uint64(v___x_3827_, sizeof(void*)*1, v_key_3826_);
lean_inc(v_canUnfold_x3f_3705_);
lean_inc(v_synthPendingDepth_3704_);
lean_inc(v_defEqCtx_x3f_3703_);
lean_inc_ref(v_localInstances_3702_);
lean_inc_ref(v_lctx_3701_);
lean_inc(v_zetaDeltaSet_3700_);
v___x_3828_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
lean_ctor_set(v___x_3828_, 1, v_zetaDeltaSet_3700_);
lean_ctor_set(v___x_3828_, 2, v_lctx_3701_);
lean_ctor_set(v___x_3828_, 3, v_localInstances_3702_);
lean_ctor_set(v___x_3828_, 4, v_defEqCtx_x3f_3703_);
lean_ctor_set(v___x_3828_, 5, v_synthPendingDepth_3704_);
lean_ctor_set(v___x_3828_, 6, v_canUnfold_x3f_3705_);
lean_ctor_set_uint8(v___x_3828_, sizeof(void*)*7, v_trackZetaDelta_3699_);
lean_ctor_set_uint8(v___x_3828_, sizeof(void*)*7 + 1, v_univApprox_3706_);
lean_ctor_set_uint8(v___x_3828_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3707_);
lean_ctor_set_uint8(v___x_3828_, sizeof(void*)*7 + 3, v_cacheInferType_3708_);
lean_inc(v_a_3567_);
lean_inc_ref(v_a_3566_);
lean_inc(v_a_3565_);
v___x_3829_ = l_Lean_Meta_whnfForall(v_a_3679_, v___x_3828_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref(v___x_3829_);
v_a_3711_ = v_a_3830_;
goto v___jp_3710_;
}
else
{
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3831_; 
v_a_3831_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3831_);
lean_dec_ref(v___x_3829_);
v_a_3711_ = v_a_3831_;
goto v___jp_3710_;
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec_ref(v___x_3680_);
lean_dec_ref(v___x_3676_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_val_3576_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v_a_3832_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3829_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3829_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
v___jp_3710_:
{
uint8_t v___x_3712_; 
v___x_3712_ = l_Lean_Expr_isForall(v_a_3711_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_dec_ref(v_a_3711_);
lean_dec_ref(v___x_3680_);
lean_dec_ref(v___x_3676_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_val_3576_);
v___x_3713_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6);
v___x_3714_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v___x_3713_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
return v___x_3714_;
}
else
{
lean_object* v___x_3715_; 
lean_inc(v_a_3567_);
lean_inc_ref(v_a_3566_);
lean_inc(v_a_3565_);
lean_inc_ref(v_a_3564_);
v___x_3715_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_val_3576_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3811_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3718_ = v___x_3715_;
v_isShared_3719_ = v_isSharedCheck_3811_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3715_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3811_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
if (lean_obj_tag(v_a_3716_) == 1)
{
lean_object* v_val_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___f_3725_; lean_object* v___x_3726_; 
lean_del_object(v___x_3718_);
v_val_3720_ = lean_ctor_get(v_a_3716_, 0);
lean_inc(v_val_3720_);
lean_dec_ref(v_a_3716_);
v___x_3721_ = 0;
v___x_3722_ = lean_box(v___x_3721_);
v___x_3723_ = lean_box(v___x_3677_);
v___x_3724_ = lean_box(v___x_3570_);
v___f_3725_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3725_, 0, v___x_3722_);
lean_closure_set(v___f_3725_, 1, v___x_3723_);
lean_closure_set(v___f_3725_, 2, v___x_3724_);
lean_inc(v_a_3567_);
lean_inc_ref(v_a_3566_);
lean_inc(v_a_3565_);
lean_inc_ref(v_a_3564_);
v___x_3726_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_motive_3583_, v___f_3725_, v___x_3677_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3728_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref(v___x_3726_);
lean_inc(v_a_3567_);
lean_inc_ref(v_a_3566_);
lean_inc(v_a_3565_);
lean_inc_ref(v_a_3564_);
v___x_3728_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_3581_, v_toMatcherInfo_3580_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_a_3729_; uint8_t v_foApprox_3730_; uint8_t v_ctxApprox_3731_; uint8_t v_quasiPatternApprox_3732_; uint8_t v_constApprox_3733_; uint8_t v_isDefEqStuckEx_3734_; uint8_t v_unificationHints_3735_; uint8_t v_proofIrrelevance_3736_; uint8_t v_assignSyntheticOpaque_3737_; uint8_t v_offsetCnstrs_3738_; uint8_t v_etaStruct_3739_; uint8_t v_univApprox_3740_; uint8_t v_iota_3741_; uint8_t v_beta_3742_; uint8_t v_proj_3743_; uint8_t v_zeta_3744_; uint8_t v_zetaDelta_3745_; uint8_t v_zetaUnused_3746_; uint8_t v_zetaHave_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3790_; 
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_a_3729_);
lean_dec_ref(v___x_3728_);
v_foApprox_3730_ = lean_ctor_get_uint8(v___x_3680_, 0);
v_ctxApprox_3731_ = lean_ctor_get_uint8(v___x_3680_, 1);
v_quasiPatternApprox_3732_ = lean_ctor_get_uint8(v___x_3680_, 2);
v_constApprox_3733_ = lean_ctor_get_uint8(v___x_3680_, 3);
v_isDefEqStuckEx_3734_ = lean_ctor_get_uint8(v___x_3680_, 4);
v_unificationHints_3735_ = lean_ctor_get_uint8(v___x_3680_, 5);
v_proofIrrelevance_3736_ = lean_ctor_get_uint8(v___x_3680_, 6);
v_assignSyntheticOpaque_3737_ = lean_ctor_get_uint8(v___x_3680_, 7);
v_offsetCnstrs_3738_ = lean_ctor_get_uint8(v___x_3680_, 8);
v_etaStruct_3739_ = lean_ctor_get_uint8(v___x_3680_, 10);
v_univApprox_3740_ = lean_ctor_get_uint8(v___x_3680_, 11);
v_iota_3741_ = lean_ctor_get_uint8(v___x_3680_, 12);
v_beta_3742_ = lean_ctor_get_uint8(v___x_3680_, 13);
v_proj_3743_ = lean_ctor_get_uint8(v___x_3680_, 14);
v_zeta_3744_ = lean_ctor_get_uint8(v___x_3680_, 15);
v_zetaDelta_3745_ = lean_ctor_get_uint8(v___x_3680_, 16);
v_zetaUnused_3746_ = lean_ctor_get_uint8(v___x_3680_, 17);
v_zetaHave_3747_ = lean_ctor_get_uint8(v___x_3680_, 18);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3749_ = v___x_3680_;
v_isShared_3750_ = v_isSharedCheck_3790_;
goto v_resetjp_3748_;
}
else
{
lean_dec(v___x_3680_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3790_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; size_t v_sz_3765_; lean_object* v_config_3767_; 
v___x_3751_ = l_Lean_Expr_bindingDomain_x21(v_a_3711_);
v___x_3752_ = l_Lean_Expr_bindingName_x21(v_a_3711_);
v___x_3753_ = l_Lean_Expr_bindingBody_x21(v_a_3711_);
lean_dec_ref(v_a_3711_);
lean_inc_ref(v___x_3751_);
v___x_3754_ = l_Lean_Expr_lam___override(v___x_3752_, v___x_3751_, v___x_3753_, v___x_3721_);
v___x_3755_ = lean_unsigned_to_nat(5u);
v___x_3756_ = lean_mk_empty_array_with_capacity(v___x_3755_);
v___x_3757_ = lean_array_push(v___x_3756_, v_val_3720_);
v___x_3758_ = lean_array_push(v___x_3757_, v___x_3751_);
v___x_3759_ = lean_array_push(v___x_3758_, v___x_3754_);
v___x_3760_ = lean_array_push(v___x_3759_, v___x_3676_);
v___x_3761_ = lean_array_push(v___x_3760_, v_a_3727_);
v___x_3762_ = l_Array_append___redArg(v_params_3582_, v___x_3761_);
lean_dec_ref(v___x_3761_);
v___x_3763_ = l_Array_append___redArg(v___x_3762_, v_discrs_3584_);
lean_dec_ref(v_discrs_3584_);
v___x_3764_ = l_Array_append___redArg(v___x_3763_, v_alts_3585_);
lean_dec_ref(v_alts_3585_);
v_sz_3765_ = lean_array_size(v___x_3764_);
if (v_isShared_3750_ == 0)
{
v_config_3767_ = v___x_3749_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 0, v_foApprox_3730_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 1, v_ctxApprox_3731_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 2, v_quasiPatternApprox_3732_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 3, v_constApprox_3733_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 4, v_isDefEqStuckEx_3734_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 5, v_unificationHints_3735_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 6, v_proofIrrelevance_3736_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 7, v_assignSyntheticOpaque_3737_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 8, v_offsetCnstrs_3738_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 10, v_etaStruct_3739_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 11, v_univApprox_3740_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 12, v_iota_3741_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 13, v_beta_3742_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 14, v_proj_3743_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 15, v_zeta_3744_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 16, v_zetaDelta_3745_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 17, v_zetaUnused_3746_);
lean_ctor_set_uint8(v_reuseFailAlloc_3789_, 18, v_zetaHave_3747_);
v_config_3767_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
uint64_t v___x_3768_; uint64_t v___x_3769_; uint64_t v___x_3770_; size_t v___x_3771_; lean_object* v___x_3772_; uint64_t v___x_3773_; uint64_t v___x_3774_; uint64_t v_key_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
lean_ctor_set_uint8(v_config_3767_, 9, v___x_3709_);
v___x_3768_ = l_Lean_Meta_Context_configKey(v_a_3564_);
v___x_3769_ = 2ULL;
v___x_3770_ = lean_uint64_shift_right(v___x_3768_, v___x_3769_);
v___x_3771_ = ((size_t)0ULL);
v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_3765_, v___x_3771_, v___x_3764_);
v___x_3773_ = lean_uint64_shift_left(v___x_3770_, v___x_3769_);
v___x_3774_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7);
v_key_3775_ = lean_uint64_lor(v___x_3773_, v___x_3774_);
v___x_3776_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3776_, 0, v_config_3767_);
lean_ctor_set_uint64(v___x_3776_, sizeof(void*)*1, v_key_3775_);
lean_inc(v_canUnfold_x3f_3705_);
lean_inc(v_synthPendingDepth_3704_);
lean_inc(v_defEqCtx_x3f_3703_);
lean_inc_ref(v_localInstances_3702_);
lean_inc_ref(v_lctx_3701_);
lean_inc(v_zetaDeltaSet_3700_);
v___x_3777_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
lean_ctor_set(v___x_3777_, 1, v_zetaDeltaSet_3700_);
lean_ctor_set(v___x_3777_, 2, v_lctx_3701_);
lean_ctor_set(v___x_3777_, 3, v_localInstances_3702_);
lean_ctor_set(v___x_3777_, 4, v_defEqCtx_x3f_3703_);
lean_ctor_set(v___x_3777_, 5, v_synthPendingDepth_3704_);
lean_ctor_set(v___x_3777_, 6, v_canUnfold_x3f_3705_);
lean_ctor_set_uint8(v___x_3777_, sizeof(void*)*7, v_trackZetaDelta_3699_);
lean_ctor_set_uint8(v___x_3777_, sizeof(void*)*7 + 1, v_univApprox_3706_);
lean_ctor_set_uint8(v___x_3777_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3707_);
lean_ctor_set_uint8(v___x_3777_, sizeof(void*)*7 + 3, v_cacheInferType_3708_);
lean_inc(v_a_3567_);
lean_inc_ref(v_a_3566_);
lean_inc(v_a_3565_);
v___x_3778_ = l_Lean_Meta_mkAppOptM(v_a_3729_, v___x_3772_, v___x_3777_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3778_);
v_a_3616_ = v_a_3779_;
goto v___jp_3615_;
}
else
{
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3780_; 
v_a_3780_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3780_);
lean_dec_ref(v___x_3778_);
v_a_3616_ = v_a_3780_;
goto v___jp_3615_;
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec_ref(v_remaining_3586_);
lean_del_object(v___x_3578_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
v_a_3781_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3778_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3778_);
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
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec(v_a_3727_);
lean_dec(v_val_3720_);
lean_dec_ref(v_a_3711_);
lean_dec_ref(v___x_3680_);
lean_dec_ref(v___x_3676_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_params_3582_);
lean_del_object(v___x_3578_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
v_a_3791_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3728_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3728_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec(v_val_3720_);
lean_dec_ref(v_a_3711_);
lean_dec_ref(v___x_3680_);
lean_dec_ref(v___x_3676_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
v_a_3799_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3726_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3726_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3711_);
lean_dec_ref(v___x_3680_);
lean_dec_ref(v___x_3676_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v___x_3807_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v___x_3807_);
v___x_3809_ = v___x_3718_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_a_3711_);
lean_dec_ref(v___x_3680_);
lean_dec_ref(v___x_3676_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v_a_3812_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3715_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3715_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_dec_ref(v___x_3676_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_val_3576_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v_a_3840_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3678_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3678_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
else
{
lean_object* v___x_3848_; lean_object* v___x_3850_; 
lean_dec_ref(v___x_3676_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_val_3576_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v___x_3848_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3848_);
v___x_3850_ = v___x_3574_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
v___jp_3615_:
{
lean_object* v___x_3617_; 
lean_inc(v_a_3567_);
lean_inc_ref(v_a_3566_);
lean_inc(v_a_3565_);
lean_inc_ref(v_a_3564_);
lean_inc_ref(v_a_3616_);
v___x_3617_ = lean_infer_type(v_a_3616_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref(v___x_3617_);
v___x_3619_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_3620_ = lean_unsigned_to_nat(3u);
v___x_3621_ = l_Lean_Expr_isAppOfArity(v_a_3618_, v___x_3619_, v___x_3620_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; 
lean_dec(v_a_3618_);
lean_dec_ref(v_remaining_3586_);
lean_del_object(v___x_3578_);
lean_inc(v_a_3567_);
lean_inc_ref(v_a_3566_);
lean_inc(v_a_3565_);
lean_inc_ref(v_a_3564_);
v___x_3622_ = lean_infer_type(v_a_3616_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref(v___x_3622_);
v___x_3624_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2);
v___x_3625_ = l_Lean_indentExpr(v_a_3623_);
v___x_3626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3624_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v___x_3626_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
return v___x_3627_;
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
v_a_3628_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3622_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3622_);
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
else
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3636_ = l_Lean_Expr_appArg_x21(v_a_3618_);
lean_dec(v_a_3618_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v_a_3616_);
v___x_3638_ = v___x_3578_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3616_);
v___x_3638_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3639_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3639_, 0, v___x_3636_);
lean_ctor_set(v___x_3639_, 1, v___x_3638_);
lean_ctor_set_uint8(v___x_3639_, sizeof(void*)*2, v___x_3570_);
v___x_3640_ = l_Array_toSubarray___redArg(v_remaining_3586_, v___x_3614_, v___x_3588_);
v___x_3641_ = l_Subarray_copy___redArg(v___x_3640_);
v___x_3642_ = l_Lean_Meta_Simp_Result_addExtraArgs(v___x_3639_, v___x_3641_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
lean_dec_ref(v___x_3641_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3652_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3645_ = v___x_3642_;
v_isShared_3646_ = v_isSharedCheck_3652_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3652_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3647_, 0, v_a_3643_);
v___x_3648_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3648_);
v___x_3650_ = v___x_3645_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
v_a_3653_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3642_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3642_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_dec_ref(v_a_3616_);
lean_dec_ref(v_remaining_3586_);
lean_del_object(v___x_3578_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
v_a_3662_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3617_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3617_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
}
else
{
lean_object* v___x_3852_; lean_object* v___x_3854_; 
lean_dec_ref(v___x_3606_);
lean_dec_ref(v_remaining_3586_);
lean_dec_ref(v_alts_3585_);
lean_dec_ref(v_discrs_3584_);
lean_dec_ref(v_motive_3583_);
lean_dec_ref(v_params_3582_);
lean_dec(v_matcherName_3581_);
lean_dec_ref(v_toMatcherInfo_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_val_3576_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v___x_3852_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3852_);
v___x_3854_ = v___x_3574_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
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
lean_object* v___x_3857_; lean_object* v___x_3859_; 
lean_dec(v_a_3572_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v___x_3857_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3857_);
v___x_3859_ = v___x_3574_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3857_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
v_a_3862_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3571_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3571_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed(lean_object* v_e_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(v_e_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(lean_object* v_declName_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3880_, v___y_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___boxed(lean_object* v_declName_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(v_declName_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(lean_object* v_00_u03b1_3900_, lean_object* v_msg_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_3901_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___boxed(lean_object* v_00_u03b1_3911_, lean_object* v_msg_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(v_00_u03b1_3911_, v_msg_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3913_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3922_, lean_object* v_constName_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3933_, lean_object* v_constName_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(v_00_u03b1_3933_, v_constName_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b1_3944_, lean_object* v_ref_3945_, lean_object* v_constName_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3945_, v_constName_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b1_3956_, lean_object* v_ref_3957_, lean_object* v_constName_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(v_00_u03b1_3956_, v_ref_3957_, v_constName_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
lean_dec(v___y_3965_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec(v___y_3959_);
lean_dec(v_ref_3957_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3968_, lean_object* v_ref_3969_, lean_object* v_msg_3970_, lean_object* v_declHint_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3969_, v_msg_3970_, v_declHint_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3981_, lean_object* v_ref_3982_, lean_object* v_msg_3983_, lean_object* v_declHint_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_3981_, v_ref_3982_, v_msg_3983_, v_declHint_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec(v___y_3991_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec(v_ref_3982_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_3994_, lean_object* v_declHint_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3994_, v_declHint_3995_, v___y_4002_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_4005_, lean_object* v_declHint_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(v_msg_4005_, v_declHint_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(lean_object* v_00_u03b1_4016_, lean_object* v_ref_4017_, lean_object* v_msg_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_4017_, v_msg_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___boxed(lean_object* v_00_u03b1_4028_, lean_object* v_ref_4029_, lean_object* v_msg_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(v_00_u03b1_4028_, v_ref_4029_, v_msg_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
lean_dec(v___y_4037_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec(v_ref_4029_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4085_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_));
v___x_4086_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_));
v___x_4087_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed), 9, 0);
v___x_4088_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4085_, v___x_4086_, v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9____boxed(lean_object* v_a_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_();
return v_res_4090_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2(void){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4100_ = lean_box(0);
v___x_4101_ = lean_unsigned_to_nat(16u);
v___x_4102_ = lean_mk_array(v___x_4101_, v___x_4100_);
return v___x_4102_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3(void){
_start:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4103_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2);
v___x_4104_ = lean_unsigned_to_nat(0u);
v___x_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
lean_ctor_set(v___x_4105_, 1, v___x_4103_);
return v___x_4105_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4(void){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4106_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5(void){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
return v___x_4108_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6(void){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; lean_object* v___x_4112_; 
v___x_4109_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4110_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3);
v___x_4111_ = 1;
v___x_4112_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4112_, 0, v___x_4110_);
lean_ctor_set(v___x_4112_, 1, v___x_4109_);
lean_ctor_set_uint8(v___x_4112_, sizeof(void*)*2, v___x_4111_);
return v___x_4112_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7(void){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4113_ = lean_unsigned_to_nat(0u);
v___x_4114_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
lean_ctor_set(v___x_4115_, 1, v___x_4113_);
return v___x_4115_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8(void){
_start:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4116_ = lean_unsigned_to_nat(32u);
v___x_4117_ = lean_mk_empty_array_with_capacity(v___x_4116_);
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
return v___x_4118_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9(void){
_start:
{
size_t v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4119_ = ((size_t)5ULL);
v___x_4120_ = lean_unsigned_to_nat(0u);
v___x_4121_ = lean_unsigned_to_nat(32u);
v___x_4122_ = lean_mk_empty_array_with_capacity(v___x_4121_);
v___x_4123_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8);
v___x_4124_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
lean_ctor_set(v___x_4124_, 1, v___x_4122_);
lean_ctor_set(v___x_4124_, 2, v___x_4120_);
lean_ctor_set(v___x_4124_, 3, v___x_4120_);
lean_ctor_set_usize(v___x_4124_, 4, v___x_4119_);
return v___x_4124_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10(void){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4125_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9);
v___x_4126_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4127_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
lean_ctor_set(v___x_4127_, 2, v___x_4126_);
lean_ctor_set(v___x_4127_, 3, v___x_4125_);
return v___x_4127_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11(void){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4128_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10);
v___x_4129_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7);
v___x_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
lean_ctor_set(v___x_4130_, 1, v___x_4128_);
return v___x_4130_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12));
v___x_4133_ = l_Lean_stringToMessageData(v___x_4132_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object* v_declName_4134_, lean_object* v_mvarId_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
uint8_t v___x_4141_; uint8_t v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; uint8_t v_foApprox_4146_; uint8_t v_ctxApprox_4147_; uint8_t v_quasiPatternApprox_4148_; uint8_t v_constApprox_4149_; uint8_t v_isDefEqStuckEx_4150_; uint8_t v_unificationHints_4151_; uint8_t v_proofIrrelevance_4152_; uint8_t v_assignSyntheticOpaque_4153_; uint8_t v_offsetCnstrs_4154_; uint8_t v_etaStruct_4155_; uint8_t v_univApprox_4156_; uint8_t v_iota_4157_; uint8_t v_beta_4158_; uint8_t v_proj_4159_; uint8_t v_zeta_4160_; uint8_t v_zetaDelta_4161_; uint8_t v_zetaUnused_4162_; uint8_t v_zetaHave_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4278_; 
v___x_4141_ = 0;
v___x_4142_ = 1;
v___x_4143_ = lean_box(0);
v___x_4144_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0));
v___x_4145_ = l_Lean_Meta_Context_config(v_a_4136_);
v_foApprox_4146_ = lean_ctor_get_uint8(v___x_4145_, 0);
v_ctxApprox_4147_ = lean_ctor_get_uint8(v___x_4145_, 1);
v_quasiPatternApprox_4148_ = lean_ctor_get_uint8(v___x_4145_, 2);
v_constApprox_4149_ = lean_ctor_get_uint8(v___x_4145_, 3);
v_isDefEqStuckEx_4150_ = lean_ctor_get_uint8(v___x_4145_, 4);
v_unificationHints_4151_ = lean_ctor_get_uint8(v___x_4145_, 5);
v_proofIrrelevance_4152_ = lean_ctor_get_uint8(v___x_4145_, 6);
v_assignSyntheticOpaque_4153_ = lean_ctor_get_uint8(v___x_4145_, 7);
v_offsetCnstrs_4154_ = lean_ctor_get_uint8(v___x_4145_, 8);
v_etaStruct_4155_ = lean_ctor_get_uint8(v___x_4145_, 10);
v_univApprox_4156_ = lean_ctor_get_uint8(v___x_4145_, 11);
v_iota_4157_ = lean_ctor_get_uint8(v___x_4145_, 12);
v_beta_4158_ = lean_ctor_get_uint8(v___x_4145_, 13);
v_proj_4159_ = lean_ctor_get_uint8(v___x_4145_, 14);
v_zeta_4160_ = lean_ctor_get_uint8(v___x_4145_, 15);
v_zetaDelta_4161_ = lean_ctor_get_uint8(v___x_4145_, 16);
v_zetaUnused_4162_ = lean_ctor_get_uint8(v___x_4145_, 17);
v_zetaHave_4163_ = lean_ctor_get_uint8(v___x_4145_, 18);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4165_ = v___x_4145_;
v_isShared_4166_ = v_isSharedCheck_4278_;
goto v_resetjp_4164_;
}
else
{
lean_dec(v___x_4145_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4278_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
uint8_t v_trackZetaDelta_4167_; lean_object* v_zetaDeltaSet_4168_; lean_object* v_lctx_4169_; lean_object* v_localInstances_4170_; lean_object* v_defEqCtx_x3f_4171_; lean_object* v_synthPendingDepth_4172_; lean_object* v_canUnfold_x3f_4173_; uint8_t v_univApprox_4174_; uint8_t v_inTypeClassResolution_4175_; uint8_t v_cacheInferType_4176_; lean_object* v___x_4177_; uint8_t v___x_4178_; lean_object* v_config_4180_; 
v_trackZetaDelta_4167_ = lean_ctor_get_uint8(v_a_4136_, sizeof(void*)*7);
v_zetaDeltaSet_4168_ = lean_ctor_get(v_a_4136_, 1);
lean_inc(v_zetaDeltaSet_4168_);
v_lctx_4169_ = lean_ctor_get(v_a_4136_, 2);
lean_inc_ref(v_lctx_4169_);
v_localInstances_4170_ = lean_ctor_get(v_a_4136_, 3);
lean_inc_ref(v_localInstances_4170_);
v_defEqCtx_x3f_4171_ = lean_ctor_get(v_a_4136_, 4);
lean_inc(v_defEqCtx_x3f_4171_);
v_synthPendingDepth_4172_ = lean_ctor_get(v_a_4136_, 5);
lean_inc(v_synthPendingDepth_4172_);
v_canUnfold_x3f_4173_ = lean_ctor_get(v_a_4136_, 6);
lean_inc(v_canUnfold_x3f_4173_);
v_univApprox_4174_ = lean_ctor_get_uint8(v_a_4136_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4175_ = lean_ctor_get_uint8(v_a_4136_, sizeof(void*)*7 + 2);
v_cacheInferType_4176_ = lean_ctor_get_uint8(v_a_4136_, sizeof(void*)*7 + 3);
v___x_4177_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1));
v___x_4178_ = 0;
if (v_isShared_4166_ == 0)
{
v_config_4180_ = v___x_4165_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 0, v_foApprox_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 1, v_ctxApprox_4147_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 2, v_quasiPatternApprox_4148_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 3, v_constApprox_4149_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 4, v_isDefEqStuckEx_4150_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 5, v_unificationHints_4151_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 6, v_proofIrrelevance_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 7, v_assignSyntheticOpaque_4153_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 8, v_offsetCnstrs_4154_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 10, v_etaStruct_4155_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 11, v_univApprox_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 12, v_iota_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 13, v_beta_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 14, v_proj_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 15, v_zeta_4160_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 16, v_zetaDelta_4161_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 17, v_zetaUnused_4162_);
lean_ctor_set_uint8(v_reuseFailAlloc_4277_, 18, v_zetaHave_4163_);
v_config_4180_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
uint64_t v___x_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4269_; 
lean_ctor_set_uint8(v_config_4180_, 9, v___x_4178_);
v___x_4181_ = l_Lean_Meta_Context_configKey(v_a_4136_);
v_isSharedCheck_4269_ = !lean_is_exclusive(v_a_4136_);
if (v_isSharedCheck_4269_ == 0)
{
lean_object* v_unused_4270_; lean_object* v_unused_4271_; lean_object* v_unused_4272_; lean_object* v_unused_4273_; lean_object* v_unused_4274_; lean_object* v_unused_4275_; lean_object* v_unused_4276_; 
v_unused_4270_ = lean_ctor_get(v_a_4136_, 6);
lean_dec(v_unused_4270_);
v_unused_4271_ = lean_ctor_get(v_a_4136_, 5);
lean_dec(v_unused_4271_);
v_unused_4272_ = lean_ctor_get(v_a_4136_, 4);
lean_dec(v_unused_4272_);
v_unused_4273_ = lean_ctor_get(v_a_4136_, 3);
lean_dec(v_unused_4273_);
v_unused_4274_ = lean_ctor_get(v_a_4136_, 2);
lean_dec(v_unused_4274_);
v_unused_4275_ = lean_ctor_get(v_a_4136_, 1);
lean_dec(v_unused_4275_);
v_unused_4276_ = lean_ctor_get(v_a_4136_, 0);
lean_dec(v_unused_4276_);
v___x_4183_ = v_a_4136_;
v_isShared_4184_ = v_isSharedCheck_4269_;
goto v_resetjp_4182_;
}
else
{
lean_dec(v_a_4136_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4269_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
uint64_t v___x_4185_; uint64_t v___x_4186_; lean_object* v___x_4187_; uint64_t v___x_4188_; uint64_t v___x_4189_; uint64_t v_key_4190_; lean_object* v___x_4191_; lean_object* v___x_4193_; 
v___x_4185_ = 2ULL;
v___x_4186_ = lean_uint64_shift_right(v___x_4181_, v___x_4185_);
v___x_4187_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6);
v___x_4188_ = lean_uint64_shift_left(v___x_4186_, v___x_4185_);
v___x_4189_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7);
v_key_4190_ = lean_uint64_lor(v___x_4188_, v___x_4189_);
v___x_4191_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4191_, 0, v_config_4180_);
lean_ctor_set_uint64(v___x_4191_, sizeof(void*)*1, v_key_4190_);
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 0, v___x_4191_);
v___x_4193_ = v___x_4183_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4191_);
lean_ctor_set(v_reuseFailAlloc_4268_, 1, v_zetaDeltaSet_4168_);
lean_ctor_set(v_reuseFailAlloc_4268_, 2, v_lctx_4169_);
lean_ctor_set(v_reuseFailAlloc_4268_, 3, v_localInstances_4170_);
lean_ctor_set(v_reuseFailAlloc_4268_, 4, v_defEqCtx_x3f_4171_);
lean_ctor_set(v_reuseFailAlloc_4268_, 5, v_synthPendingDepth_4172_);
lean_ctor_set(v_reuseFailAlloc_4268_, 6, v_canUnfold_x3f_4173_);
lean_ctor_set_uint8(v_reuseFailAlloc_4268_, sizeof(void*)*7, v_trackZetaDelta_4167_);
lean_ctor_set_uint8(v_reuseFailAlloc_4268_, sizeof(void*)*7 + 1, v_univApprox_4174_);
lean_ctor_set_uint8(v_reuseFailAlloc_4268_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4175_);
lean_ctor_set_uint8(v_reuseFailAlloc_4268_, sizeof(void*)*7 + 3, v_cacheInferType_4176_);
v___x_4193_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_4144_, v___x_4177_, v___x_4187_, v___x_4193_, v_a_4138_, v_a_4139_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref(v___x_4194_);
v___x_4196_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_));
v___x_4197_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_4177_, v___x_4196_, v___x_4141_, v_a_4138_, v_a_4139_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref(v___x_4197_);
v___x_4199_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11);
lean_inc(v_a_4139_);
lean_inc_ref(v_a_4138_);
lean_inc(v_a_4137_);
lean_inc_ref(v___x_4193_);
v___x_4200_ = l_Lean_Meta_simpTarget(v_mvarId_4135_, v_a_4195_, v_a_4198_, v___x_4143_, v___x_4142_, v___x_4199_, v___x_4193_, v_a_4137_, v_a_4138_, v_a_4139_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4243_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4203_ = v___x_4200_;
v_isShared_4204_ = v_isSharedCheck_4243_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4200_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4243_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v_fst_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4241_; 
v_fst_4205_ = lean_ctor_get(v_a_4201_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_a_4201_);
if (v_isSharedCheck_4241_ == 0)
{
lean_object* v_unused_4242_; 
v_unused_4242_ = lean_ctor_get(v_a_4201_, 1);
lean_dec(v_unused_4242_);
v___x_4207_ = v_a_4201_;
v_isShared_4208_ = v_isSharedCheck_4241_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_fst_4205_);
lean_dec(v_a_4201_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4241_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
if (lean_obj_tag(v_fst_4205_) == 0)
{
lean_object* v___x_4209_; lean_object* v___x_4211_; 
lean_del_object(v___x_4207_);
lean_dec_ref(v___x_4193_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec(v_declName_4134_);
v___x_4209_ = lean_box(0);
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 0, v___x_4209_);
v___x_4211_ = v___x_4203_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4209_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
else
{
lean_object* v_val_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4217_; 
lean_del_object(v___x_4203_);
v_val_4213_ = lean_ctor_get(v_fst_4205_, 0);
lean_inc(v_val_4213_);
lean_dec_ref(v_fst_4205_);
v___x_4214_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13);
v___x_4215_ = l_Lean_MessageData_ofConstName(v_declName_4134_, v___x_4141_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set_tag(v___x_4207_, 7);
lean_ctor_set(v___x_4207_, 1, v___x_4215_);
lean_ctor_set(v___x_4207_, 0, v___x_4214_);
v___x_4217_ = v___x_4207_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4240_, 1, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___f_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4218_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_4219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4217_);
lean_ctor_set(v___x_4219_, 1, v___x_4218_);
v___f_4220_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4220_, 0, v___x_4219_);
v___x_4221_ = lean_box(v___x_4142_);
v___x_4222_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___boxed), 7, 2);
lean_closure_set(v___x_4222_, 0, v_val_4213_);
lean_closure_set(v___x_4222_, 1, v___x_4221_);
v___x_4223_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4222_, v___f_4220_, v___x_4193_, v_a_4137_, v_a_4138_, v_a_4139_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4223_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4223_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
v_a_4232_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4223_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4223_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
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
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec_ref(v___x_4193_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec(v_declName_4134_);
v_a_4244_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4200_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4200_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec(v_a_4195_);
lean_dec_ref(v___x_4193_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec(v_mvarId_4135_);
lean_dec(v_declName_4134_);
v_a_4252_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4197_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4197_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_dec_ref(v___x_4193_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec(v_mvarId_4135_);
lean_dec(v_declName_4134_);
v_a_4260_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4194_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4194_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___boxed(lean_object* v_declName_4279_, lean_object* v_mvarId_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4279_, v_mvarId_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg(lean_object* v_cls_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_options_4293_; uint8_t v_hasTrace_4294_; 
v_options_4293_ = lean_ctor_get(v___y_4291_, 2);
v_hasTrace_4294_ = lean_ctor_get_uint8(v_options_4293_, sizeof(void*)*1);
if (v_hasTrace_4294_ == 0)
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
lean_dec(v_cls_4290_);
v___x_4295_ = lean_box(v_hasTrace_4294_);
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
return v___x_4296_;
}
else
{
lean_object* v_inheritedTraceOptions_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_inheritedTraceOptions_4297_ = lean_ctor_get(v___y_4291_, 13);
v___x_4298_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg___closed__1));
v___x_4299_ = l_Lean_Name_append(v___x_4298_, v_cls_4290_);
v___x_4300_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4297_, v_options_4293_, v___x_4299_);
lean_dec(v___x_4299_);
v___x_4301_ = lean_box(v___x_4300_);
v___x_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
return v___x_4302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg___boxed(lean_object* v_cls_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg(v_cls_4303_, v___y_4304_);
lean_dec_ref(v___y_4304_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(lean_object* v_cls_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg(v_cls_4307_, v___y_4310_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___boxed(lean_object* v_cls_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v_cls_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___redArg(lean_object* v_e_4321_, lean_object* v_k_4322_, uint8_t v_cleanupAnnotations_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
lean_object* v___f_4329_; uint8_t v___x_4330_; uint8_t v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___f_4329_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4329_, 0, v_k_4322_);
v___x_4330_ = 1;
v___x_4331_ = 0;
v___x_4332_ = lean_box(0);
v___x_4333_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4321_, v___x_4330_, v___x_4331_, v___x_4330_, v___x_4331_, v___x_4332_, v___f_4329_, v_cleanupAnnotations_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4333_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4333_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
v_a_4342_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4333_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4333_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___redArg___boxed(lean_object* v_e_4350_, lean_object* v_k_4351_, lean_object* v_cleanupAnnotations_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4358_; lean_object* v_res_4359_; 
v_cleanupAnnotations_boxed_4358_ = lean_unbox(v_cleanupAnnotations_4352_);
v_res_4359_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___redArg(v_e_4350_, v_k_4351_, v_cleanupAnnotations_boxed_4358_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(lean_object* v_00_u03b1_4360_, lean_object* v_e_4361_, lean_object* v_k_4362_, uint8_t v_cleanupAnnotations_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___redArg(v_e_4361_, v_k_4362_, v_cleanupAnnotations_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed(lean_object* v_00_u03b1_4370_, lean_object* v_e_4371_, lean_object* v_k_4372_, lean_object* v_cleanupAnnotations_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4379_; lean_object* v_res_4380_; 
v_cleanupAnnotations_boxed_4379_ = lean_unbox(v_cleanupAnnotations_4373_);
v_res_4380_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_00_u03b1_4370_, v_e_4371_, v_k_4372_, v_cleanupAnnotations_boxed_4379_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
return v_res_4380_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(lean_object* v_opts_4381_, lean_object* v_opt_4382_){
_start:
{
lean_object* v_name_4383_; lean_object* v_defValue_4384_; lean_object* v_map_4385_; lean_object* v___x_4386_; 
v_name_4383_ = lean_ctor_get(v_opt_4382_, 0);
v_defValue_4384_ = lean_ctor_get(v_opt_4382_, 1);
v_map_4385_ = lean_ctor_get(v_opts_4381_, 0);
v___x_4386_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4385_, v_name_4383_);
if (lean_obj_tag(v___x_4386_) == 0)
{
uint8_t v___x_4387_; 
v___x_4387_ = lean_unbox(v_defValue_4384_);
return v___x_4387_;
}
else
{
lean_object* v_val_4388_; 
v_val_4388_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_val_4388_);
lean_dec_ref(v___x_4386_);
if (lean_obj_tag(v_val_4388_) == 1)
{
uint8_t v_v_4389_; 
v_v_4389_ = lean_ctor_get_uint8(v_val_4388_, 0);
lean_dec_ref(v_val_4388_);
return v_v_4389_;
}
else
{
uint8_t v___x_4390_; 
lean_dec(v_val_4388_);
v___x_4390_ = lean_unbox(v_defValue_4384_);
return v___x_4390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4___boxed(lean_object* v_opts_4391_, lean_object* v_opt_4392_){
_start:
{
uint8_t v_res_4393_; lean_object* v_r_4394_; 
v_res_4393_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_opts_4391_, v_opt_4392_);
lean_dec_ref(v_opt_4392_);
lean_dec_ref(v_opts_4391_);
v_r_4394_ = lean_box(v_res_4393_);
return v_r_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(lean_object* v_opts_4395_, lean_object* v_opt_4396_){
_start:
{
lean_object* v_name_4397_; lean_object* v_defValue_4398_; lean_object* v_map_4399_; lean_object* v___x_4400_; 
v_name_4397_ = lean_ctor_get(v_opt_4396_, 0);
v_defValue_4398_ = lean_ctor_get(v_opt_4396_, 1);
v_map_4399_ = lean_ctor_get(v_opts_4395_, 0);
v___x_4400_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4399_, v_name_4397_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_inc(v_defValue_4398_);
return v_defValue_4398_;
}
else
{
lean_object* v_val_4401_; 
v_val_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc(v_val_4401_);
lean_dec_ref(v___x_4400_);
if (lean_obj_tag(v_val_4401_) == 3)
{
lean_object* v_v_4402_; 
v_v_4402_ = lean_ctor_get(v_val_4401_, 0);
lean_inc(v_v_4402_);
lean_dec_ref(v_val_4401_);
return v_v_4402_;
}
else
{
lean_dec(v_val_4401_);
lean_inc(v_defValue_4398_);
return v_defValue_4398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___boxed(lean_object* v_opts_4403_, lean_object* v_opt_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(v_opts_4403_, v_opt_4404_);
lean_dec_ref(v_opt_4404_);
lean_dec_ref(v_opts_4403_);
return v_res_4405_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4406_; double v___x_4407_; 
v___x_4406_ = lean_unsigned_to_nat(0u);
v___x_4407_ = lean_float_of_nat(v___x_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_object* v_cls_4411_, lean_object* v_msg_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v_ref_4418_; lean_object* v___x_4419_; lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4464_; 
v_ref_4418_ = lean_ctor_get(v___y_4415_, 5);
v___x_4419_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4422_ = v___x_4419_;
v_isShared_4423_ = v_isSharedCheck_4464_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4419_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4464_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4424_; lean_object* v_traceState_4425_; lean_object* v_env_4426_; lean_object* v_nextMacroScope_4427_; lean_object* v_ngen_4428_; lean_object* v_auxDeclNGen_4429_; lean_object* v_cache_4430_; lean_object* v_messages_4431_; lean_object* v_infoState_4432_; lean_object* v_snapshotTasks_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4463_; 
v___x_4424_ = lean_st_ref_take(v___y_4416_);
v_traceState_4425_ = lean_ctor_get(v___x_4424_, 4);
v_env_4426_ = lean_ctor_get(v___x_4424_, 0);
v_nextMacroScope_4427_ = lean_ctor_get(v___x_4424_, 1);
v_ngen_4428_ = lean_ctor_get(v___x_4424_, 2);
v_auxDeclNGen_4429_ = lean_ctor_get(v___x_4424_, 3);
v_cache_4430_ = lean_ctor_get(v___x_4424_, 5);
v_messages_4431_ = lean_ctor_get(v___x_4424_, 6);
v_infoState_4432_ = lean_ctor_get(v___x_4424_, 7);
v_snapshotTasks_4433_ = lean_ctor_get(v___x_4424_, 8);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4435_ = v___x_4424_;
v_isShared_4436_ = v_isSharedCheck_4463_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_snapshotTasks_4433_);
lean_inc(v_infoState_4432_);
lean_inc(v_messages_4431_);
lean_inc(v_cache_4430_);
lean_inc(v_traceState_4425_);
lean_inc(v_auxDeclNGen_4429_);
lean_inc(v_ngen_4428_);
lean_inc(v_nextMacroScope_4427_);
lean_inc(v_env_4426_);
lean_dec(v___x_4424_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4463_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
uint64_t v_tid_4437_; lean_object* v_traces_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4462_; 
v_tid_4437_ = lean_ctor_get_uint64(v_traceState_4425_, sizeof(void*)*1);
v_traces_4438_ = lean_ctor_get(v_traceState_4425_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_traceState_4425_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4440_ = v_traceState_4425_;
v_isShared_4441_ = v_isSharedCheck_4462_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_traces_4438_);
lean_dec(v_traceState_4425_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4462_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4442_; double v___x_4443_; uint8_t v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4452_; 
v___x_4442_ = lean_box(0);
v___x_4443_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__0);
v___x_4444_ = 0;
v___x_4445_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__1));
v___x_4446_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4446_, 0, v_cls_4411_);
lean_ctor_set(v___x_4446_, 1, v___x_4442_);
lean_ctor_set(v___x_4446_, 2, v___x_4445_);
lean_ctor_set_float(v___x_4446_, sizeof(void*)*3, v___x_4443_);
lean_ctor_set_float(v___x_4446_, sizeof(void*)*3 + 8, v___x_4443_);
lean_ctor_set_uint8(v___x_4446_, sizeof(void*)*3 + 16, v___x_4444_);
v___x_4447_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___closed__2));
v___x_4448_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4446_);
lean_ctor_set(v___x_4448_, 1, v_a_4420_);
lean_ctor_set(v___x_4448_, 2, v___x_4447_);
lean_inc(v_ref_4418_);
v___x_4449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4449_, 0, v_ref_4418_);
lean_ctor_set(v___x_4449_, 1, v___x_4448_);
v___x_4450_ = l_Lean_PersistentArray_push___redArg(v_traces_4438_, v___x_4449_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 0, v___x_4450_);
v___x_4452_ = v___x_4440_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4450_);
lean_ctor_set_uint64(v_reuseFailAlloc_4461_, sizeof(void*)*1, v_tid_4437_);
v___x_4452_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
lean_object* v___x_4454_; 
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 4, v___x_4452_);
v___x_4454_ = v___x_4435_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_env_4426_);
lean_ctor_set(v_reuseFailAlloc_4460_, 1, v_nextMacroScope_4427_);
lean_ctor_set(v_reuseFailAlloc_4460_, 2, v_ngen_4428_);
lean_ctor_set(v_reuseFailAlloc_4460_, 3, v_auxDeclNGen_4429_);
lean_ctor_set(v_reuseFailAlloc_4460_, 4, v___x_4452_);
lean_ctor_set(v_reuseFailAlloc_4460_, 5, v_cache_4430_);
lean_ctor_set(v_reuseFailAlloc_4460_, 6, v_messages_4431_);
lean_ctor_set(v_reuseFailAlloc_4460_, 7, v_infoState_4432_);
lean_ctor_set(v_reuseFailAlloc_4460_, 8, v_snapshotTasks_4433_);
v___x_4454_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4458_; 
v___x_4455_ = lean_st_ref_set(v___y_4416_, v___x_4454_);
v___x_4456_ = lean_box(0);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v___x_4456_);
v___x_4458_ = v___x_4422_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4456_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed(lean_object* v_cls_4465_, lean_object* v_msg_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(v_cls_4465_, v_msg_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
return v_res_4472_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4480_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__3));
v___x_4481_ = l_Lean_stringToMessageData(v___x_4480_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object* v_levelParams_4482_, lean_object* v_declName_4483_, lean_object* v_wfPreprocessProof_4484_, lean_object* v___x_4485_, lean_object* v_unaryPreDefName_4486_, lean_object* v_xs_4487_, lean_object* v_body_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4494_ = lean_box(0);
lean_inc(v_levelParams_4482_);
v___x_4495_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4482_, v___x_4494_);
lean_inc(v_declName_4483_);
v___x_4496_ = l_Lean_mkConst(v_declName_4483_, v___x_4495_);
v___x_4497_ = l_Lean_mkAppN(v___x_4496_, v_xs_4487_);
lean_inc(v___y_4492_);
lean_inc_ref(v___y_4491_);
lean_inc(v___y_4490_);
lean_inc_ref(v___y_4489_);
v___x_4498_ = l_Lean_Meta_mkEq(v___x_4497_, v_body_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref(v___x_4498_);
v___x_4500_ = lean_box(0);
lean_inc_ref(v___y_4489_);
lean_inc(v_a_4499_);
v___x_4501_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4499_, v___x_4500_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4503_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref(v___x_4501_);
lean_inc(v___y_4492_);
lean_inc_ref(v___y_4491_);
lean_inc(v___y_4490_);
lean_inc_ref(v___y_4489_);
v___x_4503_ = l_Lean_Meta_Simp_Result_addExtraArgs(v_wfPreprocessProof_4484_, v_xs_4487_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; uint8_t v___x_4507_; lean_object* v_mvarId_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref(v___x_4503_);
v___x_4505_ = l_Lean_Expr_appFn_x21(v_a_4499_);
v___x_4506_ = lean_box(0);
v___x_4507_ = 1;
v___x_4587_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4587_, 0, v___x_4505_);
lean_ctor_set(v___x_4587_, 1, v___x_4506_);
lean_ctor_set_uint8(v___x_4587_, sizeof(void*)*2, v___x_4507_);
lean_inc(v___y_4492_);
lean_inc_ref(v___y_4491_);
lean_inc(v___y_4490_);
lean_inc_ref(v___y_4489_);
v___x_4588_ = l_Lean_Meta_Simp_mkCongr(v___x_4587_, v_a_4504_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4588_) == 0)
{
lean_object* v_a_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v_a_4589_ = lean_ctor_get(v___x_4588_, 0);
lean_inc(v_a_4589_);
lean_dec_ref(v___x_4588_);
v___x_4590_ = l_Lean_Expr_mvarId_x21(v_a_4502_);
lean_inc(v___y_4492_);
lean_inc_ref(v___y_4491_);
lean_inc(v___y_4490_);
lean_inc_ref(v___y_4489_);
v___x_4591_ = l_Lean_Meta_applySimpResultToTarget(v___x_4590_, v_a_4499_, v_a_4589_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; uint8_t v___x_4593_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
lean_inc(v_a_4592_);
lean_dec_ref(v___x_4591_);
v___x_4593_ = lean_name_eq(v_declName_4483_, v_unaryPreDefName_4486_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; 
lean_inc(v___y_4492_);
lean_inc_ref(v___y_4491_);
lean_inc(v___y_4490_);
lean_inc_ref(v___y_4489_);
v___x_4594_ = l_Lean_Elab_Eqns_deltaLHS(v_a_4592_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
lean_inc(v_a_4595_);
lean_dec_ref(v___x_4594_);
v_mvarId_4509_ = v_a_4595_;
v___y_4510_ = v___y_4489_;
v___y_4511_ = v___y_4490_;
v___y_4512_ = v___y_4491_;
v___y_4513_ = v___y_4492_;
goto v___jp_4508_;
}
else
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
lean_dec(v_a_4502_);
lean_dec(v_a_4499_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___x_4485_);
lean_dec(v_declName_4483_);
lean_dec(v_levelParams_4482_);
v_a_4596_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4598_ = v___x_4594_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4594_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
else
{
v_mvarId_4509_ = v_a_4592_;
v___y_4510_ = v___y_4489_;
v___y_4511_ = v___y_4490_;
v___y_4512_ = v___y_4491_;
v___y_4513_ = v___y_4492_;
goto v___jp_4508_;
}
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
lean_dec(v_a_4502_);
lean_dec(v_a_4499_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___x_4485_);
lean_dec(v_declName_4483_);
lean_dec(v_levelParams_4482_);
v_a_4604_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___x_4591_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___x_4591_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
else
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4619_; 
lean_dec(v_a_4502_);
lean_dec(v_a_4499_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___x_4485_);
lean_dec(v_declName_4483_);
lean_dec(v_levelParams_4482_);
v_a_4612_ = lean_ctor_get(v___x_4588_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4588_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4614_ = v___x_4588_;
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4588_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4612_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
v___jp_4508_:
{
lean_object* v___x_4514_; 
lean_inc(v___y_4513_);
lean_inc_ref(v___y_4512_);
lean_inc(v___y_4511_);
lean_inc_ref(v___y_4510_);
v___x_4514_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v_a_4515_; lean_object* v___x_4516_; 
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
lean_inc(v_a_4515_);
lean_dec_ref(v___x_4514_);
lean_inc(v___y_4513_);
lean_inc_ref(v___y_4512_);
lean_inc(v___y_4511_);
lean_inc_ref(v___y_4510_);
v___x_4516_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4483_, v_a_4515_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_object* v___x_4517_; lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4578_; 
lean_dec_ref(v___x_4516_);
v___x_4517_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4502_, v___y_4511_);
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4520_ = v___x_4517_;
v_isShared_4521_ = v_isSharedCheck_4578_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4517_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4578_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
uint8_t v___x_4522_; uint8_t v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = 0;
v___x_4523_ = 1;
v___x_4524_ = l_Lean_Meta_mkForallFVars(v_xs_4487_, v_a_4499_, v___x_4522_, v___x_4507_, v___x_4507_, v___x_4523_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; lean_object* v___x_4526_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_a_4525_);
lean_dec_ref(v___x_4524_);
lean_inc(v___y_4513_);
lean_inc_ref(v___y_4512_);
lean_inc(v___y_4511_);
lean_inc_ref(v___y_4510_);
v___x_4526_ = l_Lean_Meta_letToHave(v_a_4525_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v_a_4527_; lean_object* v___x_4528_; 
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc(v_a_4527_);
lean_dec_ref(v___x_4526_);
v___x_4528_ = l_Lean_Meta_mkLambdaFVars(v_xs_4487_, v_a_4518_, v___x_4522_, v___x_4507_, v___x_4522_, v___x_4507_, v___x_4523_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v_a_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4534_; 
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
lean_inc(v_a_4529_);
lean_dec_ref(v___x_4528_);
lean_inc(v___x_4485_);
v___x_4530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4485_);
lean_ctor_set(v___x_4530_, 1, v_levelParams_4482_);
lean_ctor_set(v___x_4530_, 2, v_a_4527_);
lean_inc(v___x_4485_);
v___x_4531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4485_);
lean_ctor_set(v___x_4531_, 1, v___x_4494_);
v___x_4532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4532_, 0, v___x_4530_);
lean_ctor_set(v___x_4532_, 1, v_a_4529_);
lean_ctor_set(v___x_4532_, 2, v___x_4531_);
if (v_isShared_4521_ == 0)
{
lean_ctor_set_tag(v___x_4520_, 2);
lean_ctor_set(v___x_4520_, 0, v___x_4532_);
v___x_4534_ = v___x_4520_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4532_);
v___x_4534_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
lean_object* v___x_4535_; 
lean_inc(v___y_4513_);
lean_inc_ref(v___y_4512_);
v___x_4535_ = l_Lean_addDecl(v___x_4534_, v___x_4522_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v___x_4536_; 
lean_dec_ref(v___x_4535_);
lean_inc(v___y_4513_);
lean_inc_ref(v___y_4512_);
lean_inc(v___y_4511_);
lean_inc_ref(v___y_4510_);
lean_inc(v___x_4485_);
v___x_4536_ = l_Lean_inferDefEqAttr(v___x_4485_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v_a_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4552_; 
lean_dec_ref(v___x_4536_);
v___x_4537_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4538_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg(v___x_4537_, v___y_4512_);
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4541_ = v___x_4538_;
v_isShared_4542_ = v_isSharedCheck_4552_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_a_4539_);
lean_dec(v___x_4538_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4552_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
uint8_t v___x_4543_; 
v___x_4543_ = lean_unbox(v_a_4539_);
lean_dec(v_a_4539_);
if (v___x_4543_ == 0)
{
lean_object* v___x_4544_; lean_object* v___x_4546_; 
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___x_4485_);
v___x_4544_ = lean_box(0);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v___x_4544_);
v___x_4546_ = v___x_4541_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v___x_4544_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
else
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
lean_del_object(v___x_4541_);
v___x_4548_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4);
v___x_4549_ = l_Lean_MessageData_ofConstName(v___x_4485_, v___x_4522_);
v___x_4550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4548_);
lean_ctor_set(v___x_4550_, 1, v___x_4549_);
v___x_4551_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(v___x_4537_, v___x_4550_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
return v___x_4551_;
}
}
}
else
{
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___x_4485_);
return v___x_4536_;
}
}
else
{
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___x_4485_);
return v___x_4535_;
}
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec(v_a_4527_);
lean_del_object(v___x_4520_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___x_4485_);
lean_dec(v_levelParams_4482_);
v_a_4554_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4528_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4528_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_del_object(v___x_4520_);
lean_dec(v_a_4518_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___x_4485_);
lean_dec(v_levelParams_4482_);
v_a_4562_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4526_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4526_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_del_object(v___x_4520_);
lean_dec(v_a_4518_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___x_4485_);
lean_dec(v_levelParams_4482_);
v_a_4570_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4524_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4524_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
}
else
{
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v_a_4502_);
lean_dec(v_a_4499_);
lean_dec(v___x_4485_);
lean_dec(v_levelParams_4482_);
return v___x_4516_;
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v_a_4502_);
lean_dec(v_a_4499_);
lean_dec(v___x_4485_);
lean_dec(v_declName_4483_);
lean_dec(v_levelParams_4482_);
v_a_4579_ = lean_ctor_get(v___x_4514_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4514_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4514_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
else
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4627_; 
lean_dec(v_a_4502_);
lean_dec(v_a_4499_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___x_4485_);
lean_dec(v_declName_4483_);
lean_dec(v_levelParams_4482_);
v_a_4620_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4622_ = v___x_4503_;
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4503_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4620_);
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
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec(v_a_4499_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___x_4485_);
lean_dec_ref(v_wfPreprocessProof_4484_);
lean_dec(v_declName_4483_);
lean_dec(v_levelParams_4482_);
v_a_4628_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4501_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4501_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___x_4485_);
lean_dec_ref(v_wfPreprocessProof_4484_);
lean_dec(v_declName_4483_);
lean_dec(v_levelParams_4482_);
v_a_4636_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4498_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4498_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object* v_levelParams_4644_, lean_object* v_declName_4645_, lean_object* v_wfPreprocessProof_4646_, lean_object* v___x_4647_, lean_object* v_unaryPreDefName_4648_, lean_object* v_xs_4649_, lean_object* v_body_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l_Lean_Elab_WF_mkUnfoldEq___lam__0(v_levelParams_4644_, v_declName_4645_, v_wfPreprocessProof_4646_, v___x_4647_, v_unaryPreDefName_4648_, v_xs_4649_, v_body_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
lean_dec_ref(v_xs_4649_);
lean_dec(v_unaryPreDefName_4648_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(lean_object* v_o_4657_, lean_object* v_k_4658_, uint8_t v_v_4659_){
_start:
{
lean_object* v_map_4660_; uint8_t v_hasTrace_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4675_; 
v_map_4660_ = lean_ctor_get(v_o_4657_, 0);
v_hasTrace_4661_ = lean_ctor_get_uint8(v_o_4657_, sizeof(void*)*1);
v_isSharedCheck_4675_ = !lean_is_exclusive(v_o_4657_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4663_ = v_o_4657_;
v_isShared_4664_ = v_isSharedCheck_4675_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_map_4660_);
lean_dec(v_o_4657_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4675_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; 
v___x_4665_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4665_, 0, v_v_4659_);
lean_inc(v_k_4658_);
v___x_4666_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4658_, v___x_4665_, v_map_4660_);
if (v_hasTrace_4661_ == 0)
{
lean_object* v___x_4667_; uint8_t v___x_4668_; lean_object* v___x_4670_; 
v___x_4667_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg___closed__1));
v___x_4668_ = l_Lean_Name_isPrefixOf(v___x_4667_, v_k_4658_);
lean_dec(v_k_4658_);
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 0, v___x_4666_);
v___x_4670_ = v___x_4663_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v___x_4666_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
lean_ctor_set_uint8(v___x_4670_, sizeof(void*)*1, v___x_4668_);
return v___x_4670_;
}
}
else
{
lean_object* v___x_4673_; 
lean_dec(v_k_4658_);
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 0, v___x_4666_);
v___x_4673_ = v___x_4663_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v___x_4666_);
lean_ctor_set_uint8(v_reuseFailAlloc_4674_, sizeof(void*)*1, v_hasTrace_4661_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___boxed(lean_object* v_o_4676_, lean_object* v_k_4677_, lean_object* v_v_4678_){
_start:
{
uint8_t v_v_boxed_4679_; lean_object* v_res_4680_; 
v_v_boxed_4679_ = lean_unbox(v_v_4678_);
v_res_4680_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(v_o_4676_, v_k_4677_, v_v_boxed_4679_);
return v_res_4680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object* v_opts_4681_, lean_object* v_opt_4682_, uint8_t v_val_4683_){
_start:
{
lean_object* v_name_4684_; lean_object* v___x_4685_; 
v_name_4684_ = lean_ctor_get(v_opt_4682_, 0);
lean_inc(v_name_4684_);
lean_dec_ref(v_opt_4682_);
v___x_4685_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(v_opts_4681_, v_name_4684_, v_val_4683_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object* v_opts_4686_, lean_object* v_opt_4687_, lean_object* v_val_4688_){
_start:
{
uint8_t v_val_boxed_4689_; lean_object* v_res_4690_; 
v_val_boxed_4689_ = lean_unbox(v_val_4688_);
v_res_4690_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v_opts_4686_, v_opt_4687_, v_val_boxed_4689_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___lam__0(lean_object* v___y_4691_, uint8_t v_isExporting_4692_, lean_object* v___x_4693_, lean_object* v___y_4694_, lean_object* v___x_4695_, lean_object* v_a_x3f_4696_){
_start:
{
lean_object* v___x_4698_; lean_object* v_env_4699_; lean_object* v_nextMacroScope_4700_; lean_object* v_ngen_4701_; lean_object* v_auxDeclNGen_4702_; lean_object* v_traceState_4703_; lean_object* v_messages_4704_; lean_object* v_infoState_4705_; lean_object* v_snapshotTasks_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4731_; 
v___x_4698_ = lean_st_ref_take(v___y_4691_);
v_env_4699_ = lean_ctor_get(v___x_4698_, 0);
v_nextMacroScope_4700_ = lean_ctor_get(v___x_4698_, 1);
v_ngen_4701_ = lean_ctor_get(v___x_4698_, 2);
v_auxDeclNGen_4702_ = lean_ctor_get(v___x_4698_, 3);
v_traceState_4703_ = lean_ctor_get(v___x_4698_, 4);
v_messages_4704_ = lean_ctor_get(v___x_4698_, 6);
v_infoState_4705_ = lean_ctor_get(v___x_4698_, 7);
v_snapshotTasks_4706_ = lean_ctor_get(v___x_4698_, 8);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; 
v_unused_4732_ = lean_ctor_get(v___x_4698_, 5);
lean_dec(v_unused_4732_);
v___x_4708_ = v___x_4698_;
v_isShared_4709_ = v_isSharedCheck_4731_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_snapshotTasks_4706_);
lean_inc(v_infoState_4705_);
lean_inc(v_messages_4704_);
lean_inc(v_traceState_4703_);
lean_inc(v_auxDeclNGen_4702_);
lean_inc(v_ngen_4701_);
lean_inc(v_nextMacroScope_4700_);
lean_inc(v_env_4699_);
lean_dec(v___x_4698_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4731_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4710_; lean_object* v___x_4712_; 
v___x_4710_ = l_Lean_Environment_setExporting(v_env_4699_, v_isExporting_4692_);
if (v_isShared_4709_ == 0)
{
lean_ctor_set(v___x_4708_, 5, v___x_4693_);
lean_ctor_set(v___x_4708_, 0, v___x_4710_);
v___x_4712_ = v___x_4708_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4710_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_nextMacroScope_4700_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_ngen_4701_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_auxDeclNGen_4702_);
lean_ctor_set(v_reuseFailAlloc_4730_, 4, v_traceState_4703_);
lean_ctor_set(v_reuseFailAlloc_4730_, 5, v___x_4693_);
lean_ctor_set(v_reuseFailAlloc_4730_, 6, v_messages_4704_);
lean_ctor_set(v_reuseFailAlloc_4730_, 7, v_infoState_4705_);
lean_ctor_set(v_reuseFailAlloc_4730_, 8, v_snapshotTasks_4706_);
v___x_4712_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v_mctx_4715_; lean_object* v_zetaDeltaFVarIds_4716_; lean_object* v_postponed_4717_; lean_object* v_diag_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4728_; 
v___x_4713_ = lean_st_ref_set(v___y_4691_, v___x_4712_);
v___x_4714_ = lean_st_ref_take(v___y_4694_);
v_mctx_4715_ = lean_ctor_get(v___x_4714_, 0);
v_zetaDeltaFVarIds_4716_ = lean_ctor_get(v___x_4714_, 2);
v_postponed_4717_ = lean_ctor_get(v___x_4714_, 3);
v_diag_4718_ = lean_ctor_get(v___x_4714_, 4);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4728_ == 0)
{
lean_object* v_unused_4729_; 
v_unused_4729_ = lean_ctor_get(v___x_4714_, 1);
lean_dec(v_unused_4729_);
v___x_4720_ = v___x_4714_;
v_isShared_4721_ = v_isSharedCheck_4728_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_diag_4718_);
lean_inc(v_postponed_4717_);
lean_inc(v_zetaDeltaFVarIds_4716_);
lean_inc(v_mctx_4715_);
lean_dec(v___x_4714_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4728_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 1, v___x_4695_);
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_mctx_4715_);
lean_ctor_set(v_reuseFailAlloc_4727_, 1, v___x_4695_);
lean_ctor_set(v_reuseFailAlloc_4727_, 2, v_zetaDeltaFVarIds_4716_);
lean_ctor_set(v_reuseFailAlloc_4727_, 3, v_postponed_4717_);
lean_ctor_set(v_reuseFailAlloc_4727_, 4, v_diag_4718_);
v___x_4723_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; 
v___x_4724_ = lean_st_ref_set(v___y_4694_, v___x_4723_);
v___x_4725_ = lean_box(0);
v___x_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4725_);
return v___x_4726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v___y_4733_, lean_object* v_isExporting_4734_, lean_object* v___x_4735_, lean_object* v___y_4736_, lean_object* v___x_4737_, lean_object* v_a_x3f_4738_, lean_object* v___y_4739_){
_start:
{
uint8_t v_isExporting_boxed_4740_; lean_object* v_res_4741_; 
v_isExporting_boxed_4740_ = lean_unbox(v_isExporting_4734_);
v_res_4741_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___lam__0(v___y_4733_, v_isExporting_boxed_4740_, v___x_4735_, v___y_4736_, v___x_4737_, v_a_x3f_4738_);
lean_dec(v_a_x3f_4738_);
lean_dec(v___y_4736_);
lean_dec(v___y_4733_);
return v_res_4741_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_4742_; 
v___x_4742_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4742_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4743_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__0);
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; 
v___x_4745_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__1);
v___x_4746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4746_, 0, v___x_4745_);
lean_ctor_set(v___x_4746_, 1, v___x_4745_);
return v___x_4746_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4747_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__1);
v___x_4748_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4747_);
lean_ctor_set(v___x_4748_, 1, v___x_4747_);
lean_ctor_set(v___x_4748_, 2, v___x_4747_);
lean_ctor_set(v___x_4748_, 3, v___x_4747_);
lean_ctor_set(v___x_4748_, 4, v___x_4747_);
lean_ctor_set(v___x_4748_, 5, v___x_4747_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg(lean_object* v_x_4749_, uint8_t v_isExporting_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_){
_start:
{
lean_object* v___x_4756_; lean_object* v_env_4757_; uint8_t v_isExporting_4758_; lean_object* v___x_4759_; lean_object* v_env_4760_; lean_object* v_nextMacroScope_4761_; lean_object* v_ngen_4762_; lean_object* v_auxDeclNGen_4763_; lean_object* v_traceState_4764_; lean_object* v_messages_4765_; lean_object* v_infoState_4766_; lean_object* v_snapshotTasks_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4821_; 
v___x_4756_ = lean_st_ref_get(v___y_4754_);
v_env_4757_ = lean_ctor_get(v___x_4756_, 0);
lean_inc_ref(v_env_4757_);
lean_dec(v___x_4756_);
v_isExporting_4758_ = lean_ctor_get_uint8(v_env_4757_, sizeof(void*)*8);
lean_dec_ref(v_env_4757_);
v___x_4759_ = lean_st_ref_take(v___y_4754_);
v_env_4760_ = lean_ctor_get(v___x_4759_, 0);
v_nextMacroScope_4761_ = lean_ctor_get(v___x_4759_, 1);
v_ngen_4762_ = lean_ctor_get(v___x_4759_, 2);
v_auxDeclNGen_4763_ = lean_ctor_get(v___x_4759_, 3);
v_traceState_4764_ = lean_ctor_get(v___x_4759_, 4);
v_messages_4765_ = lean_ctor_get(v___x_4759_, 6);
v_infoState_4766_ = lean_ctor_get(v___x_4759_, 7);
v_snapshotTasks_4767_ = lean_ctor_get(v___x_4759_, 8);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4821_ == 0)
{
lean_object* v_unused_4822_; 
v_unused_4822_ = lean_ctor_get(v___x_4759_, 5);
lean_dec(v_unused_4822_);
v___x_4769_ = v___x_4759_;
v_isShared_4770_ = v_isSharedCheck_4821_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_snapshotTasks_4767_);
lean_inc(v_infoState_4766_);
lean_inc(v_messages_4765_);
lean_inc(v_traceState_4764_);
lean_inc(v_auxDeclNGen_4763_);
lean_inc(v_ngen_4762_);
lean_inc(v_nextMacroScope_4761_);
lean_inc(v_env_4760_);
lean_dec(v___x_4759_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4821_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4774_; 
v___x_4771_ = l_Lean_Environment_setExporting(v_env_4760_, v_isExporting_4750_);
v___x_4772_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 5, v___x_4772_);
lean_ctor_set(v___x_4769_, 0, v___x_4771_);
v___x_4774_ = v___x_4769_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4771_);
lean_ctor_set(v_reuseFailAlloc_4820_, 1, v_nextMacroScope_4761_);
lean_ctor_set(v_reuseFailAlloc_4820_, 2, v_ngen_4762_);
lean_ctor_set(v_reuseFailAlloc_4820_, 3, v_auxDeclNGen_4763_);
lean_ctor_set(v_reuseFailAlloc_4820_, 4, v_traceState_4764_);
lean_ctor_set(v_reuseFailAlloc_4820_, 5, v___x_4772_);
lean_ctor_set(v_reuseFailAlloc_4820_, 6, v_messages_4765_);
lean_ctor_set(v_reuseFailAlloc_4820_, 7, v_infoState_4766_);
lean_ctor_set(v_reuseFailAlloc_4820_, 8, v_snapshotTasks_4767_);
v___x_4774_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v_mctx_4777_; lean_object* v_zetaDeltaFVarIds_4778_; lean_object* v_postponed_4779_; lean_object* v_diag_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4818_; 
v___x_4775_ = lean_st_ref_set(v___y_4754_, v___x_4774_);
v___x_4776_ = lean_st_ref_take(v___y_4752_);
v_mctx_4777_ = lean_ctor_get(v___x_4776_, 0);
v_zetaDeltaFVarIds_4778_ = lean_ctor_get(v___x_4776_, 2);
v_postponed_4779_ = lean_ctor_get(v___x_4776_, 3);
v_diag_4780_ = lean_ctor_get(v___x_4776_, 4);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4818_ == 0)
{
lean_object* v_unused_4819_; 
v_unused_4819_ = lean_ctor_get(v___x_4776_, 1);
lean_dec(v_unused_4819_);
v___x_4782_ = v___x_4776_;
v_isShared_4783_ = v_isSharedCheck_4818_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_diag_4780_);
lean_inc(v_postponed_4779_);
lean_inc(v_zetaDeltaFVarIds_4778_);
lean_inc(v_mctx_4777_);
lean_dec(v___x_4776_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4818_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4784_; lean_object* v___x_4786_; 
v___x_4784_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__3);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 1, v___x_4784_);
v___x_4786_ = v___x_4782_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_mctx_4777_);
lean_ctor_set(v_reuseFailAlloc_4817_, 1, v___x_4784_);
lean_ctor_set(v_reuseFailAlloc_4817_, 2, v_zetaDeltaFVarIds_4778_);
lean_ctor_set(v_reuseFailAlloc_4817_, 3, v_postponed_4779_);
lean_ctor_set(v_reuseFailAlloc_4817_, 4, v_diag_4780_);
v___x_4786_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
lean_object* v___x_4787_; lean_object* v_r_4788_; 
v___x_4787_ = lean_st_ref_set(v___y_4752_, v___x_4786_);
lean_inc(v___y_4754_);
lean_inc(v___y_4752_);
v_r_4788_ = lean_apply_5(v_x_4749_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, lean_box(0));
if (lean_obj_tag(v_r_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4805_; 
v_a_4789_ = lean_ctor_get(v_r_4788_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v_r_4788_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4791_ = v_r_4788_;
v_isShared_4792_ = v_isSharedCheck_4805_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v_r_4788_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4805_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4794_; 
lean_inc(v_a_4789_);
if (v_isShared_4792_ == 0)
{
lean_ctor_set_tag(v___x_4791_, 1);
v___x_4794_ = v___x_4791_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4789_);
v___x_4794_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
lean_object* v___x_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
v___x_4795_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___lam__0(v___y_4754_, v_isExporting_4758_, v___x_4772_, v___y_4752_, v___x_4784_, v___x_4794_);
lean_dec_ref(v___x_4794_);
lean_dec(v___y_4752_);
lean_dec(v___y_4754_);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4802_ == 0)
{
lean_object* v_unused_4803_; 
v_unused_4803_ = lean_ctor_get(v___x_4795_, 0);
lean_dec(v_unused_4803_);
v___x_4797_ = v___x_4795_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_dec(v___x_4795_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 0, v_a_4789_);
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4789_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4815_; 
v_a_4806_ = lean_ctor_get(v_r_4788_, 0);
lean_inc(v_a_4806_);
lean_dec_ref(v_r_4788_);
v___x_4807_ = lean_box(0);
v___x_4808_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___lam__0(v___y_4754_, v_isExporting_4758_, v___x_4772_, v___y_4752_, v___x_4784_, v___x_4807_);
lean_dec(v___y_4752_);
lean_dec(v___y_4754_);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4808_);
if (v_isSharedCheck_4815_ == 0)
{
lean_object* v_unused_4816_; 
v_unused_4816_ = lean_ctor_get(v___x_4808_, 0);
lean_dec(v_unused_4816_);
v___x_4810_ = v___x_4808_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_dec(v___x_4808_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4813_; 
if (v_isShared_4811_ == 0)
{
lean_ctor_set_tag(v___x_4810_, 1);
lean_ctor_set(v___x_4810_, 0, v_a_4806_);
v___x_4813_ = v___x_4810_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4806_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___boxed(lean_object* v_x_4823_, lean_object* v_isExporting_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_){
_start:
{
uint8_t v_isExporting_boxed_4830_; lean_object* v_res_4831_; 
v_isExporting_boxed_4830_ = lean_unbox(v_isExporting_4824_);
v_res_4831_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg(v_x_4823_, v_isExporting_boxed_4830_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_);
return v_res_4831_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6___redArg(lean_object* v_x_4832_, uint8_t v_when_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_){
_start:
{
if (v_when_4833_ == 0)
{
lean_object* v___x_4839_; 
v___x_4839_ = lean_apply_5(v_x_4832_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, lean_box(0));
return v___x_4839_;
}
else
{
uint8_t v___x_4840_; lean_object* v___x_4841_; 
v___x_4840_ = 0;
v___x_4841_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg(v_x_4832_, v___x_4840_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
return v___x_4841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6___redArg___boxed(lean_object* v_x_4842_, lean_object* v_when_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_){
_start:
{
uint8_t v_when_boxed_4849_; lean_object* v_res_4850_; 
v_when_boxed_4849_ = lean_unbox(v_when_4843_);
v_res_4850_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6___redArg(v_x_4842_, v_when_boxed_4849_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t v___x_4851_, lean_object* v___x_4852_, uint8_t v___x_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v___x_4859_; lean_object* v_fileName_4860_; lean_object* v_fileMap_4861_; lean_object* v_options_4862_; lean_object* v_currRecDepth_4863_; lean_object* v_ref_4864_; lean_object* v_currNamespace_4865_; lean_object* v_openDecls_4866_; lean_object* v_initHeartbeats_4867_; lean_object* v_maxHeartbeats_4868_; lean_object* v_quotContext_4869_; lean_object* v_currMacroScope_4870_; lean_object* v_cancelTk_x3f_4871_; uint8_t v_suppressElabErrors_4872_; lean_object* v_inheritedTraceOptions_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4926_; 
v___x_4859_ = lean_st_ref_get(v___y_4857_);
v_fileName_4860_ = lean_ctor_get(v___y_4856_, 0);
v_fileMap_4861_ = lean_ctor_get(v___y_4856_, 1);
v_options_4862_ = lean_ctor_get(v___y_4856_, 2);
v_currRecDepth_4863_ = lean_ctor_get(v___y_4856_, 3);
v_ref_4864_ = lean_ctor_get(v___y_4856_, 5);
v_currNamespace_4865_ = lean_ctor_get(v___y_4856_, 6);
v_openDecls_4866_ = lean_ctor_get(v___y_4856_, 7);
v_initHeartbeats_4867_ = lean_ctor_get(v___y_4856_, 8);
v_maxHeartbeats_4868_ = lean_ctor_get(v___y_4856_, 9);
v_quotContext_4869_ = lean_ctor_get(v___y_4856_, 10);
v_currMacroScope_4870_ = lean_ctor_get(v___y_4856_, 11);
v_cancelTk_x3f_4871_ = lean_ctor_get(v___y_4856_, 12);
v_suppressElabErrors_4872_ = lean_ctor_get_uint8(v___y_4856_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4873_ = lean_ctor_get(v___y_4856_, 13);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___y_4856_);
if (v_isSharedCheck_4926_ == 0)
{
lean_object* v_unused_4927_; 
v_unused_4927_ = lean_ctor_get(v___y_4856_, 4);
lean_dec(v_unused_4927_);
v___x_4875_ = v___y_4856_;
v_isShared_4876_ = v_isSharedCheck_4926_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_inheritedTraceOptions_4873_);
lean_inc(v_cancelTk_x3f_4871_);
lean_inc(v_currMacroScope_4870_);
lean_inc(v_quotContext_4869_);
lean_inc(v_maxHeartbeats_4868_);
lean_inc(v_initHeartbeats_4867_);
lean_inc(v_openDecls_4866_);
lean_inc(v_currNamespace_4865_);
lean_inc(v_ref_4864_);
lean_inc(v_currRecDepth_4863_);
lean_inc(v_options_4862_);
lean_inc(v_fileMap_4861_);
lean_inc(v_fileName_4860_);
lean_dec(v___y_4856_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4926_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v_env_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; uint8_t v___x_4881_; lean_object* v_fileName_4883_; lean_object* v_fileMap_4884_; lean_object* v_currRecDepth_4885_; lean_object* v_ref_4886_; lean_object* v_currNamespace_4887_; lean_object* v_openDecls_4888_; lean_object* v_initHeartbeats_4889_; lean_object* v_maxHeartbeats_4890_; lean_object* v_quotContext_4891_; lean_object* v_currMacroScope_4892_; lean_object* v_cancelTk_x3f_4893_; uint8_t v_suppressElabErrors_4894_; lean_object* v_inheritedTraceOptions_4895_; lean_object* v___y_4896_; uint8_t v___y_4904_; uint8_t v___x_4925_; 
v_env_4877_ = lean_ctor_get(v___x_4859_, 0);
lean_inc_ref(v_env_4877_);
lean_dec(v___x_4859_);
v___x_4878_ = l_Lean_Meta_tactic_hygienic;
v___x_4879_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v_options_4862_, v___x_4878_, v___x_4851_);
v___x_4880_ = l_Lean_diagnostics;
v___x_4881_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v___x_4879_, v___x_4880_);
v___x_4925_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4877_);
lean_dec_ref(v_env_4877_);
if (v___x_4925_ == 0)
{
if (v___x_4881_ == 0)
{
v_fileName_4883_ = v_fileName_4860_;
v_fileMap_4884_ = v_fileMap_4861_;
v_currRecDepth_4885_ = v_currRecDepth_4863_;
v_ref_4886_ = v_ref_4864_;
v_currNamespace_4887_ = v_currNamespace_4865_;
v_openDecls_4888_ = v_openDecls_4866_;
v_initHeartbeats_4889_ = v_initHeartbeats_4867_;
v_maxHeartbeats_4890_ = v_maxHeartbeats_4868_;
v_quotContext_4891_ = v_quotContext_4869_;
v_currMacroScope_4892_ = v_currMacroScope_4870_;
v_cancelTk_x3f_4893_ = v_cancelTk_x3f_4871_;
v_suppressElabErrors_4894_ = v_suppressElabErrors_4872_;
v_inheritedTraceOptions_4895_ = v_inheritedTraceOptions_4873_;
v___y_4896_ = v___y_4857_;
goto v___jp_4882_;
}
else
{
v___y_4904_ = v___x_4925_;
goto v___jp_4903_;
}
}
else
{
v___y_4904_ = v___x_4881_;
goto v___jp_4903_;
}
v___jp_4882_:
{
lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4900_; 
v___x_4897_ = l_Lean_maxRecDepth;
v___x_4898_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(v___x_4879_, v___x_4897_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 13, v_inheritedTraceOptions_4895_);
lean_ctor_set(v___x_4875_, 12, v_cancelTk_x3f_4893_);
lean_ctor_set(v___x_4875_, 11, v_currMacroScope_4892_);
lean_ctor_set(v___x_4875_, 10, v_quotContext_4891_);
lean_ctor_set(v___x_4875_, 9, v_maxHeartbeats_4890_);
lean_ctor_set(v___x_4875_, 8, v_initHeartbeats_4889_);
lean_ctor_set(v___x_4875_, 7, v_openDecls_4888_);
lean_ctor_set(v___x_4875_, 6, v_currNamespace_4887_);
lean_ctor_set(v___x_4875_, 5, v_ref_4886_);
lean_ctor_set(v___x_4875_, 4, v___x_4898_);
lean_ctor_set(v___x_4875_, 3, v_currRecDepth_4885_);
lean_ctor_set(v___x_4875_, 2, v___x_4879_);
lean_ctor_set(v___x_4875_, 1, v_fileMap_4884_);
lean_ctor_set(v___x_4875_, 0, v_fileName_4883_);
v___x_4900_ = v___x_4875_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_fileName_4883_);
lean_ctor_set(v_reuseFailAlloc_4902_, 1, v_fileMap_4884_);
lean_ctor_set(v_reuseFailAlloc_4902_, 2, v___x_4879_);
lean_ctor_set(v_reuseFailAlloc_4902_, 3, v_currRecDepth_4885_);
lean_ctor_set(v_reuseFailAlloc_4902_, 4, v___x_4898_);
lean_ctor_set(v_reuseFailAlloc_4902_, 5, v_ref_4886_);
lean_ctor_set(v_reuseFailAlloc_4902_, 6, v_currNamespace_4887_);
lean_ctor_set(v_reuseFailAlloc_4902_, 7, v_openDecls_4888_);
lean_ctor_set(v_reuseFailAlloc_4902_, 8, v_initHeartbeats_4889_);
lean_ctor_set(v_reuseFailAlloc_4902_, 9, v_maxHeartbeats_4890_);
lean_ctor_set(v_reuseFailAlloc_4902_, 10, v_quotContext_4891_);
lean_ctor_set(v_reuseFailAlloc_4902_, 11, v_currMacroScope_4892_);
lean_ctor_set(v_reuseFailAlloc_4902_, 12, v_cancelTk_x3f_4893_);
lean_ctor_set(v_reuseFailAlloc_4902_, 13, v_inheritedTraceOptions_4895_);
v___x_4900_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
lean_object* v___x_4901_; 
lean_ctor_set_uint8(v___x_4900_, sizeof(void*)*14, v___x_4881_);
lean_ctor_set_uint8(v___x_4900_, sizeof(void*)*14 + 1, v_suppressElabErrors_4894_);
v___x_4901_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6___redArg(v___x_4852_, v___x_4853_, v___y_4854_, v___y_4855_, v___x_4900_, v___y_4896_);
return v___x_4901_;
}
}
v___jp_4903_:
{
if (v___y_4904_ == 0)
{
lean_object* v___x_4905_; lean_object* v_env_4906_; lean_object* v_nextMacroScope_4907_; lean_object* v_ngen_4908_; lean_object* v_auxDeclNGen_4909_; lean_object* v_traceState_4910_; lean_object* v_messages_4911_; lean_object* v_infoState_4912_; lean_object* v_snapshotTasks_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4923_; 
v___x_4905_ = lean_st_ref_take(v___y_4857_);
v_env_4906_ = lean_ctor_get(v___x_4905_, 0);
v_nextMacroScope_4907_ = lean_ctor_get(v___x_4905_, 1);
v_ngen_4908_ = lean_ctor_get(v___x_4905_, 2);
v_auxDeclNGen_4909_ = lean_ctor_get(v___x_4905_, 3);
v_traceState_4910_ = lean_ctor_get(v___x_4905_, 4);
v_messages_4911_ = lean_ctor_get(v___x_4905_, 6);
v_infoState_4912_ = lean_ctor_get(v___x_4905_, 7);
v_snapshotTasks_4913_ = lean_ctor_get(v___x_4905_, 8);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_4923_ == 0)
{
lean_object* v_unused_4924_; 
v_unused_4924_ = lean_ctor_get(v___x_4905_, 5);
lean_dec(v_unused_4924_);
v___x_4915_ = v___x_4905_;
v_isShared_4916_ = v_isSharedCheck_4923_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_snapshotTasks_4913_);
lean_inc(v_infoState_4912_);
lean_inc(v_messages_4911_);
lean_inc(v_traceState_4910_);
lean_inc(v_auxDeclNGen_4909_);
lean_inc(v_ngen_4908_);
lean_inc(v_nextMacroScope_4907_);
lean_inc(v_env_4906_);
lean_dec(v___x_4905_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4923_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4920_; 
v___x_4917_ = l_Lean_Kernel_enableDiag(v_env_4906_, v___x_4881_);
v___x_4918_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2);
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 5, v___x_4918_);
lean_ctor_set(v___x_4915_, 0, v___x_4917_);
v___x_4920_ = v___x_4915_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4917_);
lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_nextMacroScope_4907_);
lean_ctor_set(v_reuseFailAlloc_4922_, 2, v_ngen_4908_);
lean_ctor_set(v_reuseFailAlloc_4922_, 3, v_auxDeclNGen_4909_);
lean_ctor_set(v_reuseFailAlloc_4922_, 4, v_traceState_4910_);
lean_ctor_set(v_reuseFailAlloc_4922_, 5, v___x_4918_);
lean_ctor_set(v_reuseFailAlloc_4922_, 6, v_messages_4911_);
lean_ctor_set(v_reuseFailAlloc_4922_, 7, v_infoState_4912_);
lean_ctor_set(v_reuseFailAlloc_4922_, 8, v_snapshotTasks_4913_);
v___x_4920_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
lean_object* v___x_4921_; 
v___x_4921_ = lean_st_ref_set(v___y_4857_, v___x_4920_);
v_fileName_4883_ = v_fileName_4860_;
v_fileMap_4884_ = v_fileMap_4861_;
v_currRecDepth_4885_ = v_currRecDepth_4863_;
v_ref_4886_ = v_ref_4864_;
v_currNamespace_4887_ = v_currNamespace_4865_;
v_openDecls_4888_ = v_openDecls_4866_;
v_initHeartbeats_4889_ = v_initHeartbeats_4867_;
v_maxHeartbeats_4890_ = v_maxHeartbeats_4868_;
v_quotContext_4891_ = v_quotContext_4869_;
v_currMacroScope_4892_ = v_currMacroScope_4870_;
v_cancelTk_x3f_4893_ = v_cancelTk_x3f_4871_;
v_suppressElabErrors_4894_ = v_suppressElabErrors_4872_;
v_inheritedTraceOptions_4895_ = v_inheritedTraceOptions_4873_;
v___y_4896_ = v___y_4857_;
goto v___jp_4882_;
}
}
}
else
{
v_fileName_4883_ = v_fileName_4860_;
v_fileMap_4884_ = v_fileMap_4861_;
v_currRecDepth_4885_ = v_currRecDepth_4863_;
v_ref_4886_ = v_ref_4864_;
v_currNamespace_4887_ = v_currNamespace_4865_;
v_openDecls_4888_ = v_openDecls_4866_;
v_initHeartbeats_4889_ = v_initHeartbeats_4867_;
v_maxHeartbeats_4890_ = v_maxHeartbeats_4868_;
v_quotContext_4891_ = v_quotContext_4869_;
v_currMacroScope_4892_ = v_currMacroScope_4870_;
v_cancelTk_x3f_4893_ = v_cancelTk_x3f_4871_;
v_suppressElabErrors_4894_ = v_suppressElabErrors_4872_;
v_inheritedTraceOptions_4895_ = v_inheritedTraceOptions_4873_;
v___y_4896_ = v___y_4857_;
goto v___jp_4882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object* v___x_4928_, lean_object* v___x_4929_, lean_object* v___x_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
uint8_t v___x_10133__boxed_4936_; uint8_t v___x_10135__boxed_4937_; lean_object* v_res_4938_; 
v___x_10133__boxed_4936_ = lean_unbox(v___x_4928_);
v___x_10135__boxed_4937_ = lean_unbox(v___x_4930_);
v_res_4938_ = l_Lean_Elab_WF_mkUnfoldEq___lam__2(v___x_10133__boxed_4936_, v___x_4929_, v___x_10135__boxed_4937_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
return v_res_4938_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4940_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___closed__0));
v___x_4941_ = l_Lean_stringToMessageData(v___x_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object* v_preDef_4942_, lean_object* v_unaryPreDefName_4943_, lean_object* v_wfPreprocessProof_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_){
_start:
{
lean_object* v___x_4950_; lean_object* v_env_4951_; lean_object* v_levelParams_4952_; lean_object* v_declName_4953_; lean_object* v_value_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___f_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___f_4961_; uint8_t v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; uint8_t v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___f_4968_; lean_object* v___x_4969_; 
v___x_4950_ = lean_st_ref_get(v_a_4948_);
v_env_4951_ = lean_ctor_get(v___x_4950_, 0);
lean_inc_ref(v_env_4951_);
lean_dec(v___x_4950_);
v_levelParams_4952_ = lean_ctor_get(v_preDef_4942_, 1);
lean_inc(v_levelParams_4952_);
v_declName_4953_ = lean_ctor_get(v_preDef_4942_, 3);
lean_inc(v_declName_4953_);
v_value_4954_ = lean_ctor_get(v_preDef_4942_, 7);
lean_inc_ref(v_value_4954_);
lean_dec_ref(v_preDef_4942_);
v___x_4955_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_4953_);
v___x_4956_ = l_Lean_Meta_mkEqLikeNameFor(v_env_4951_, v_declName_4953_, v___x_4955_);
lean_inc(v___x_4956_);
v___f_4957_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4957_, 0, v_levelParams_4952_);
lean_closure_set(v___f_4957_, 1, v_declName_4953_);
lean_closure_set(v___f_4957_, 2, v_wfPreprocessProof_4944_);
lean_closure_set(v___f_4957_, 3, v___x_4956_);
lean_closure_set(v___f_4957_, 4, v_unaryPreDefName_4943_);
v___x_4958_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___closed__1, &l_Lean_Elab_WF_mkUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1);
v___x_4959_ = l_Lean_MessageData_ofName(v___x_4956_);
v___x_4960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4958_);
lean_ctor_set(v___x_4960_, 1, v___x_4959_);
v___f_4961_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4961_, 0, v___x_4960_);
v___x_4962_ = 0;
v___x_4963_ = lean_box(v___x_4962_);
v___x_4964_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed), 9, 4);
lean_closure_set(v___x_4964_, 0, lean_box(0));
lean_closure_set(v___x_4964_, 1, v_value_4954_);
lean_closure_set(v___x_4964_, 2, v___f_4957_);
lean_closure_set(v___x_4964_, 3, v___x_4963_);
v___x_4965_ = 1;
v___x_4966_ = lean_box(v___x_4962_);
v___x_4967_ = lean_box(v___x_4965_);
v___f_4968_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_4968_, 0, v___x_4966_);
lean_closure_set(v___f_4968_, 1, v___x_4964_);
lean_closure_set(v___f_4968_, 2, v___x_4967_);
v___x_4969_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4968_, v___f_4961_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4977_; 
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4972_ = v___x_4969_;
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4969_);
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
v_reuseFailAlloc_4976_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4985_; 
v_a_4978_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4980_ = v___x_4969_;
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4969_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
if (v_isShared_4981_ == 0)
{
v___x_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_a_4978_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___boxed(lean_object* v_preDef_4986_, lean_object* v_unaryPreDefName_4987_, lean_object* v_wfPreprocessProof_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l_Lean_Elab_WF_mkUnfoldEq(v_preDef_4986_, v_unaryPreDefName_4987_, v_wfPreprocessProof_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7(lean_object* v_00_u03b1_4995_, lean_object* v_x_4996_, uint8_t v_isExporting_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v___x_5003_; 
v___x_5003_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg(v_x_4996_, v_isExporting_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___boxed(lean_object* v_00_u03b1_5004_, lean_object* v_x_5005_, lean_object* v_isExporting_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_){
_start:
{
uint8_t v_isExporting_boxed_5012_; lean_object* v_res_5013_; 
v_isExporting_boxed_5012_ = lean_unbox(v_isExporting_5006_);
v_res_5013_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7(v_00_u03b1_5004_, v_x_5005_, v_isExporting_boxed_5012_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6(lean_object* v_00_u03b1_5014_, lean_object* v_x_5015_, uint8_t v_when_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6___redArg(v_x_5015_, v_when_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6___boxed(lean_object* v_00_u03b1_5023_, lean_object* v_x_5024_, lean_object* v_when_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
uint8_t v_when_boxed_5031_; lean_object* v_res_5032_; 
v_when_boxed_5031_ = lean_unbox(v_when_5025_);
v_res_5032_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6(v_00_u03b1_5023_, v_x_5024_, v_when_boxed_5031_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
return v_res_5032_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5034_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0));
v___x_5035_ = l_Lean_stringToMessageData(v___x_5034_);
return v___x_5035_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5041_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3));
v___x_5042_ = l_Lean_stringToMessageData(v___x_5041_);
return v___x_5042_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6(void){
_start:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5044_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5));
v___x_5045_ = l_Lean_stringToMessageData(v___x_5044_);
return v___x_5045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object* v_levelParams_5046_, lean_object* v_declName_5047_, lean_object* v___x_5048_, lean_object* v___x_5049_, lean_object* v___x_5050_, lean_object* v_xs_5051_, lean_object* v_body_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5058_ = lean_box(0);
lean_inc(v_levelParams_5046_);
v___x_5059_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_5046_, v___x_5058_);
v___x_5060_ = l_Lean_mkConst(v_declName_5047_, v___x_5059_);
v___x_5061_ = l_Lean_mkAppN(v___x_5060_, v_xs_5051_);
lean_inc(v___y_5056_);
lean_inc_ref(v___y_5055_);
lean_inc(v___y_5054_);
lean_inc_ref(v___y_5053_);
v___x_5062_ = l_Lean_Meta_mkEq(v___x_5061_, v_body_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
lean_dec_ref(v___x_5062_);
v___x_5064_ = lean_box(0);
lean_inc_ref(v___y_5053_);
lean_inc(v_a_5063_);
v___x_5065_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_5063_, v___x_5064_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; 
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
lean_dec_ref(v___x_5065_);
v___x_5067_ = l_Lean_Expr_mvarId_x21(v_a_5066_);
lean_inc(v___y_5056_);
lean_inc_ref(v___y_5055_);
lean_inc(v___y_5054_);
lean_inc_ref(v___y_5053_);
v___x_5068_ = l_Lean_Elab_Eqns_deltaLHS(v___x_5067_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
if (lean_obj_tag(v___x_5068_) == 0)
{
lean_object* v_a_5069_; uint8_t v___x_5070_; uint8_t v___x_5071_; lean_object* v___y_5073_; lean_object* v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___x_5138_; lean_object* v___x_5139_; 
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
lean_inc(v_a_5069_);
lean_dec_ref(v___x_5068_);
v___x_5070_ = 1;
v___x_5071_ = 0;
v___x_5138_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2));
lean_inc(v___y_5056_);
lean_inc_ref(v___y_5055_);
lean_inc(v___y_5054_);
lean_inc_ref(v___y_5053_);
lean_inc(v_a_5069_);
v___x_5139_ = l_Lean_MVarId_applyConst(v_a_5069_, v___x_5048_, v___x_5138_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; uint8_t v___x_5141_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
lean_inc(v_a_5140_);
lean_dec_ref(v___x_5139_);
v___x_5141_ = l_List_isEmpty___redArg(v_a_5140_);
lean_dec(v_a_5140_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; 
lean_dec(v_a_5066_);
lean_dec(v_a_5063_);
lean_dec(v___x_5049_);
lean_dec(v_levelParams_5046_);
v___x_5142_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4);
v___x_5143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5142_);
lean_ctor_set(v___x_5143_, 1, v___x_5050_);
v___x_5144_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6);
v___x_5145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5145_, 0, v___x_5143_);
lean_ctor_set(v___x_5145_, 1, v___x_5144_);
v___x_5146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5146_, 0, v_a_5069_);
v___x_5147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5147_, 0, v___x_5145_);
lean_ctor_set(v___x_5147_, 1, v___x_5146_);
v___x_5148_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5149_, 0, v___x_5147_);
lean_ctor_set(v___x_5149_, 1, v___x_5148_);
v___x_5150_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_5149_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
return v___x_5150_;
}
else
{
lean_dec(v_a_5069_);
lean_dec_ref(v___x_5050_);
v___y_5073_ = v___y_5053_;
v___y_5074_ = v___y_5054_;
v___y_5075_ = v___y_5055_;
v___y_5076_ = v___y_5056_;
goto v___jp_5072_;
}
}
else
{
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5158_; 
lean_dec(v_a_5069_);
lean_dec(v_a_5066_);
lean_dec(v_a_5063_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec_ref(v___x_5050_);
lean_dec(v___x_5049_);
lean_dec(v_levelParams_5046_);
v_a_5151_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5153_ = v___x_5139_;
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_a_5151_);
lean_dec(v___x_5139_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v___x_5156_; 
if (v_isShared_5154_ == 0)
{
v___x_5156_ = v___x_5153_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5151_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
v___jp_5072_:
{
lean_object* v___x_5077_; lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5137_; 
v___x_5077_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_5066_, v___y_5074_);
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5080_ = v___x_5077_;
v_isShared_5081_ = v_isSharedCheck_5137_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5077_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5137_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
uint8_t v___x_5082_; lean_object* v___x_5083_; 
v___x_5082_ = 1;
v___x_5083_ = l_Lean_Meta_mkForallFVars(v_xs_5051_, v_a_5063_, v___x_5071_, v___x_5070_, v___x_5070_, v___x_5082_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
if (lean_obj_tag(v___x_5083_) == 0)
{
lean_object* v_a_5084_; lean_object* v___x_5085_; 
v_a_5084_ = lean_ctor_get(v___x_5083_, 0);
lean_inc(v_a_5084_);
lean_dec_ref(v___x_5083_);
lean_inc(v___y_5076_);
lean_inc_ref(v___y_5075_);
lean_inc(v___y_5074_);
lean_inc_ref(v___y_5073_);
v___x_5085_ = l_Lean_Meta_letToHave(v_a_5084_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; lean_object* v___x_5087_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5086_);
lean_dec_ref(v___x_5085_);
v___x_5087_ = l_Lean_Meta_mkLambdaFVars(v_xs_5051_, v_a_5078_, v___x_5071_, v___x_5070_, v___x_5071_, v___x_5070_, v___x_5082_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v_a_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5093_; 
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_a_5088_);
lean_dec_ref(v___x_5087_);
lean_inc(v___x_5049_);
v___x_5089_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5089_, 0, v___x_5049_);
lean_ctor_set(v___x_5089_, 1, v_levelParams_5046_);
lean_ctor_set(v___x_5089_, 2, v_a_5086_);
lean_inc(v___x_5049_);
v___x_5090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5090_, 0, v___x_5049_);
lean_ctor_set(v___x_5090_, 1, v___x_5058_);
v___x_5091_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5089_);
lean_ctor_set(v___x_5091_, 1, v_a_5088_);
lean_ctor_set(v___x_5091_, 2, v___x_5090_);
if (v_isShared_5081_ == 0)
{
lean_ctor_set_tag(v___x_5080_, 2);
lean_ctor_set(v___x_5080_, 0, v___x_5091_);
v___x_5093_ = v___x_5080_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5091_);
v___x_5093_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
lean_object* v___x_5094_; 
lean_inc(v___y_5076_);
lean_inc_ref(v___y_5075_);
v___x_5094_ = l_Lean_addDecl(v___x_5093_, v___x_5071_, v___y_5075_, v___y_5076_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v___x_5095_; 
lean_dec_ref(v___x_5094_);
lean_inc(v___y_5076_);
lean_inc_ref(v___y_5075_);
lean_inc(v___y_5074_);
lean_inc_ref(v___y_5073_);
lean_inc(v___x_5049_);
v___x_5095_ = l_Lean_inferDefEqAttr(v___x_5049_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
if (lean_obj_tag(v___x_5095_) == 0)
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v_a_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5111_; 
lean_dec_ref(v___x_5095_);
v___x_5096_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_5097_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___redArg(v___x_5096_, v___y_5075_);
v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5100_ = v___x_5097_;
v_isShared_5101_ = v_isSharedCheck_5111_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_a_5098_);
lean_dec(v___x_5097_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5111_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
uint8_t v___x_5102_; 
v___x_5102_ = lean_unbox(v_a_5098_);
lean_dec(v_a_5098_);
if (v___x_5102_ == 0)
{
lean_object* v___x_5103_; lean_object* v___x_5105_; 
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec(v___x_5049_);
v___x_5103_ = lean_box(0);
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 0, v___x_5103_);
v___x_5105_ = v___x_5100_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v___x_5103_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
}
}
else
{
lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; 
lean_del_object(v___x_5100_);
v___x_5107_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1);
v___x_5108_ = l_Lean_MessageData_ofConstName(v___x_5049_, v___x_5071_);
v___x_5109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5109_, 0, v___x_5107_);
lean_ctor_set(v___x_5109_, 1, v___x_5108_);
v___x_5110_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(v___x_5096_, v___x_5109_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
return v___x_5110_;
}
}
}
else
{
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec(v___x_5049_);
return v___x_5095_;
}
}
else
{
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec(v___x_5049_);
return v___x_5094_;
}
}
}
else
{
lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5120_; 
lean_dec(v_a_5086_);
lean_del_object(v___x_5080_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec(v___x_5049_);
lean_dec(v_levelParams_5046_);
v_a_5113_ = lean_ctor_get(v___x_5087_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5087_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5115_ = v___x_5087_;
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_dec(v___x_5087_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_a_5113_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
}
else
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
lean_del_object(v___x_5080_);
lean_dec(v_a_5078_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec(v___x_5049_);
lean_dec(v_levelParams_5046_);
v_a_5121_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5085_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5085_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
else
{
lean_object* v_a_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5136_; 
lean_del_object(v___x_5080_);
lean_dec(v_a_5078_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec(v___x_5049_);
lean_dec(v_levelParams_5046_);
v_a_5129_ = lean_ctor_get(v___x_5083_, 0);
v_isSharedCheck_5136_ = !lean_is_exclusive(v___x_5083_);
if (v_isSharedCheck_5136_ == 0)
{
v___x_5131_ = v___x_5083_;
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_a_5129_);
lean_dec(v___x_5083_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5134_; 
if (v_isShared_5132_ == 0)
{
v___x_5134_ = v___x_5131_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_a_5129_);
v___x_5134_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
return v___x_5134_;
}
}
}
}
}
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
lean_dec(v_a_5066_);
lean_dec(v_a_5063_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec_ref(v___x_5050_);
lean_dec(v___x_5049_);
lean_dec(v___x_5048_);
lean_dec(v_levelParams_5046_);
v_a_5159_ = lean_ctor_get(v___x_5068_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5068_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5068_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5164_; 
if (v_isShared_5162_ == 0)
{
v___x_5164_ = v___x_5161_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_a_5159_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
}
else
{
lean_object* v_a_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5174_; 
lean_dec(v_a_5063_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec_ref(v___x_5050_);
lean_dec(v___x_5049_);
lean_dec(v___x_5048_);
lean_dec(v_levelParams_5046_);
v_a_5167_ = lean_ctor_get(v___x_5065_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5169_ = v___x_5065_;
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_a_5167_);
lean_dec(v___x_5065_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5172_; 
if (v_isShared_5170_ == 0)
{
v___x_5172_ = v___x_5169_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v_a_5167_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
}
}
}
}
else
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5182_; 
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec_ref(v___x_5050_);
lean_dec(v___x_5049_);
lean_dec(v___x_5048_);
lean_dec(v_levelParams_5046_);
v_a_5175_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5177_ = v___x_5062_;
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v___x_5062_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v___x_5180_; 
if (v_isShared_5178_ == 0)
{
v___x_5180_ = v___x_5177_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v_a_5175_);
v___x_5180_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
return v___x_5180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed(lean_object* v_levelParams_5183_, lean_object* v_declName_5184_, lean_object* v___x_5185_, lean_object* v___x_5186_, lean_object* v___x_5187_, lean_object* v_xs_5188_, lean_object* v_body_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_){
_start:
{
lean_object* v_res_5195_; 
v_res_5195_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(v_levelParams_5183_, v_declName_5184_, v___x_5185_, v___x_5186_, v___x_5187_, v_xs_5188_, v_body_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_);
lean_dec_ref(v_xs_5188_);
return v_res_5195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(uint8_t v___x_5196_, lean_object* v_value_5197_, lean_object* v___f_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v___x_5204_; lean_object* v_fileName_5205_; lean_object* v_fileMap_5206_; lean_object* v_options_5207_; lean_object* v_currRecDepth_5208_; lean_object* v_ref_5209_; lean_object* v_currNamespace_5210_; lean_object* v_openDecls_5211_; lean_object* v_initHeartbeats_5212_; lean_object* v_maxHeartbeats_5213_; lean_object* v_quotContext_5214_; lean_object* v_currMacroScope_5215_; lean_object* v_cancelTk_x3f_5216_; uint8_t v_suppressElabErrors_5217_; lean_object* v_inheritedTraceOptions_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5271_; 
v___x_5204_ = lean_st_ref_get(v___y_5202_);
v_fileName_5205_ = lean_ctor_get(v___y_5201_, 0);
v_fileMap_5206_ = lean_ctor_get(v___y_5201_, 1);
v_options_5207_ = lean_ctor_get(v___y_5201_, 2);
v_currRecDepth_5208_ = lean_ctor_get(v___y_5201_, 3);
v_ref_5209_ = lean_ctor_get(v___y_5201_, 5);
v_currNamespace_5210_ = lean_ctor_get(v___y_5201_, 6);
v_openDecls_5211_ = lean_ctor_get(v___y_5201_, 7);
v_initHeartbeats_5212_ = lean_ctor_get(v___y_5201_, 8);
v_maxHeartbeats_5213_ = lean_ctor_get(v___y_5201_, 9);
v_quotContext_5214_ = lean_ctor_get(v___y_5201_, 10);
v_currMacroScope_5215_ = lean_ctor_get(v___y_5201_, 11);
v_cancelTk_x3f_5216_ = lean_ctor_get(v___y_5201_, 12);
v_suppressElabErrors_5217_ = lean_ctor_get_uint8(v___y_5201_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5218_ = lean_ctor_get(v___y_5201_, 13);
v_isSharedCheck_5271_ = !lean_is_exclusive(v___y_5201_);
if (v_isSharedCheck_5271_ == 0)
{
lean_object* v_unused_5272_; 
v_unused_5272_ = lean_ctor_get(v___y_5201_, 4);
lean_dec(v_unused_5272_);
v___x_5220_ = v___y_5201_;
v_isShared_5221_ = v_isSharedCheck_5271_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_inheritedTraceOptions_5218_);
lean_inc(v_cancelTk_x3f_5216_);
lean_inc(v_currMacroScope_5215_);
lean_inc(v_quotContext_5214_);
lean_inc(v_maxHeartbeats_5213_);
lean_inc(v_initHeartbeats_5212_);
lean_inc(v_openDecls_5211_);
lean_inc(v_currNamespace_5210_);
lean_inc(v_ref_5209_);
lean_inc(v_currRecDepth_5208_);
lean_inc(v_options_5207_);
lean_inc(v_fileMap_5206_);
lean_inc(v_fileName_5205_);
lean_dec(v___y_5201_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5271_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v_env_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; uint8_t v___x_5226_; lean_object* v_fileName_5228_; lean_object* v_fileMap_5229_; lean_object* v_currRecDepth_5230_; lean_object* v_ref_5231_; lean_object* v_currNamespace_5232_; lean_object* v_openDecls_5233_; lean_object* v_initHeartbeats_5234_; lean_object* v_maxHeartbeats_5235_; lean_object* v_quotContext_5236_; lean_object* v_currMacroScope_5237_; lean_object* v_cancelTk_x3f_5238_; uint8_t v_suppressElabErrors_5239_; lean_object* v_inheritedTraceOptions_5240_; lean_object* v___y_5241_; uint8_t v___y_5249_; uint8_t v___x_5270_; 
v_env_5222_ = lean_ctor_get(v___x_5204_, 0);
lean_inc_ref(v_env_5222_);
lean_dec(v___x_5204_);
v___x_5223_ = l_Lean_Meta_tactic_hygienic;
v___x_5224_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v_options_5207_, v___x_5223_, v___x_5196_);
v___x_5225_ = l_Lean_diagnostics;
v___x_5226_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v___x_5224_, v___x_5225_);
v___x_5270_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5222_);
lean_dec_ref(v_env_5222_);
if (v___x_5270_ == 0)
{
if (v___x_5226_ == 0)
{
v_fileName_5228_ = v_fileName_5205_;
v_fileMap_5229_ = v_fileMap_5206_;
v_currRecDepth_5230_ = v_currRecDepth_5208_;
v_ref_5231_ = v_ref_5209_;
v_currNamespace_5232_ = v_currNamespace_5210_;
v_openDecls_5233_ = v_openDecls_5211_;
v_initHeartbeats_5234_ = v_initHeartbeats_5212_;
v_maxHeartbeats_5235_ = v_maxHeartbeats_5213_;
v_quotContext_5236_ = v_quotContext_5214_;
v_currMacroScope_5237_ = v_currMacroScope_5215_;
v_cancelTk_x3f_5238_ = v_cancelTk_x3f_5216_;
v_suppressElabErrors_5239_ = v_suppressElabErrors_5217_;
v_inheritedTraceOptions_5240_ = v_inheritedTraceOptions_5218_;
v___y_5241_ = v___y_5202_;
goto v___jp_5227_;
}
else
{
v___y_5249_ = v___x_5270_;
goto v___jp_5248_;
}
}
else
{
v___y_5249_ = v___x_5226_;
goto v___jp_5248_;
}
v___jp_5227_:
{
lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5245_; 
v___x_5242_ = l_Lean_maxRecDepth;
v___x_5243_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(v___x_5224_, v___x_5242_);
if (v_isShared_5221_ == 0)
{
lean_ctor_set(v___x_5220_, 13, v_inheritedTraceOptions_5240_);
lean_ctor_set(v___x_5220_, 12, v_cancelTk_x3f_5238_);
lean_ctor_set(v___x_5220_, 11, v_currMacroScope_5237_);
lean_ctor_set(v___x_5220_, 10, v_quotContext_5236_);
lean_ctor_set(v___x_5220_, 9, v_maxHeartbeats_5235_);
lean_ctor_set(v___x_5220_, 8, v_initHeartbeats_5234_);
lean_ctor_set(v___x_5220_, 7, v_openDecls_5233_);
lean_ctor_set(v___x_5220_, 6, v_currNamespace_5232_);
lean_ctor_set(v___x_5220_, 5, v_ref_5231_);
lean_ctor_set(v___x_5220_, 4, v___x_5243_);
lean_ctor_set(v___x_5220_, 3, v_currRecDepth_5230_);
lean_ctor_set(v___x_5220_, 2, v___x_5224_);
lean_ctor_set(v___x_5220_, 1, v_fileMap_5229_);
lean_ctor_set(v___x_5220_, 0, v_fileName_5228_);
v___x_5245_ = v___x_5220_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_fileName_5228_);
lean_ctor_set(v_reuseFailAlloc_5247_, 1, v_fileMap_5229_);
lean_ctor_set(v_reuseFailAlloc_5247_, 2, v___x_5224_);
lean_ctor_set(v_reuseFailAlloc_5247_, 3, v_currRecDepth_5230_);
lean_ctor_set(v_reuseFailAlloc_5247_, 4, v___x_5243_);
lean_ctor_set(v_reuseFailAlloc_5247_, 5, v_ref_5231_);
lean_ctor_set(v_reuseFailAlloc_5247_, 6, v_currNamespace_5232_);
lean_ctor_set(v_reuseFailAlloc_5247_, 7, v_openDecls_5233_);
lean_ctor_set(v_reuseFailAlloc_5247_, 8, v_initHeartbeats_5234_);
lean_ctor_set(v_reuseFailAlloc_5247_, 9, v_maxHeartbeats_5235_);
lean_ctor_set(v_reuseFailAlloc_5247_, 10, v_quotContext_5236_);
lean_ctor_set(v_reuseFailAlloc_5247_, 11, v_currMacroScope_5237_);
lean_ctor_set(v_reuseFailAlloc_5247_, 12, v_cancelTk_x3f_5238_);
lean_ctor_set(v_reuseFailAlloc_5247_, 13, v_inheritedTraceOptions_5240_);
v___x_5245_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
lean_object* v___x_5246_; 
lean_ctor_set_uint8(v___x_5245_, sizeof(void*)*14, v___x_5226_);
lean_ctor_set_uint8(v___x_5245_, sizeof(void*)*14 + 1, v_suppressElabErrors_5239_);
v___x_5246_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___redArg(v_value_5197_, v___f_5198_, v___x_5196_, v___y_5199_, v___y_5200_, v___x_5245_, v___y_5241_);
return v___x_5246_;
}
}
v___jp_5248_:
{
if (v___y_5249_ == 0)
{
lean_object* v___x_5250_; lean_object* v_env_5251_; lean_object* v_nextMacroScope_5252_; lean_object* v_ngen_5253_; lean_object* v_auxDeclNGen_5254_; lean_object* v_traceState_5255_; lean_object* v_messages_5256_; lean_object* v_infoState_5257_; lean_object* v_snapshotTasks_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5268_; 
v___x_5250_ = lean_st_ref_take(v___y_5202_);
v_env_5251_ = lean_ctor_get(v___x_5250_, 0);
v_nextMacroScope_5252_ = lean_ctor_get(v___x_5250_, 1);
v_ngen_5253_ = lean_ctor_get(v___x_5250_, 2);
v_auxDeclNGen_5254_ = lean_ctor_get(v___x_5250_, 3);
v_traceState_5255_ = lean_ctor_get(v___x_5250_, 4);
v_messages_5256_ = lean_ctor_get(v___x_5250_, 6);
v_infoState_5257_ = lean_ctor_get(v___x_5250_, 7);
v_snapshotTasks_5258_ = lean_ctor_get(v___x_5250_, 8);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5268_ == 0)
{
lean_object* v_unused_5269_; 
v_unused_5269_ = lean_ctor_get(v___x_5250_, 5);
lean_dec(v_unused_5269_);
v___x_5260_ = v___x_5250_;
v_isShared_5261_ = v_isSharedCheck_5268_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_snapshotTasks_5258_);
lean_inc(v_infoState_5257_);
lean_inc(v_messages_5256_);
lean_inc(v_traceState_5255_);
lean_inc(v_auxDeclNGen_5254_);
lean_inc(v_ngen_5253_);
lean_inc(v_nextMacroScope_5252_);
lean_inc(v_env_5251_);
lean_dec(v___x_5250_);
v___x_5260_ = lean_box(0);
v_isShared_5261_ = v_isSharedCheck_5268_;
goto v_resetjp_5259_;
}
v_resetjp_5259_:
{
lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5265_; 
v___x_5262_ = l_Lean_Kernel_enableDiag(v_env_5251_, v___x_5226_);
v___x_5263_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__6_spec__7___redArg___closed__2);
if (v_isShared_5261_ == 0)
{
lean_ctor_set(v___x_5260_, 5, v___x_5263_);
lean_ctor_set(v___x_5260_, 0, v___x_5262_);
v___x_5265_ = v___x_5260_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v___x_5262_);
lean_ctor_set(v_reuseFailAlloc_5267_, 1, v_nextMacroScope_5252_);
lean_ctor_set(v_reuseFailAlloc_5267_, 2, v_ngen_5253_);
lean_ctor_set(v_reuseFailAlloc_5267_, 3, v_auxDeclNGen_5254_);
lean_ctor_set(v_reuseFailAlloc_5267_, 4, v_traceState_5255_);
lean_ctor_set(v_reuseFailAlloc_5267_, 5, v___x_5263_);
lean_ctor_set(v_reuseFailAlloc_5267_, 6, v_messages_5256_);
lean_ctor_set(v_reuseFailAlloc_5267_, 7, v_infoState_5257_);
lean_ctor_set(v_reuseFailAlloc_5267_, 8, v_snapshotTasks_5258_);
v___x_5265_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
lean_object* v___x_5266_; 
v___x_5266_ = lean_st_ref_set(v___y_5202_, v___x_5265_);
v_fileName_5228_ = v_fileName_5205_;
v_fileMap_5229_ = v_fileMap_5206_;
v_currRecDepth_5230_ = v_currRecDepth_5208_;
v_ref_5231_ = v_ref_5209_;
v_currNamespace_5232_ = v_currNamespace_5210_;
v_openDecls_5233_ = v_openDecls_5211_;
v_initHeartbeats_5234_ = v_initHeartbeats_5212_;
v_maxHeartbeats_5235_ = v_maxHeartbeats_5213_;
v_quotContext_5236_ = v_quotContext_5214_;
v_currMacroScope_5237_ = v_currMacroScope_5215_;
v_cancelTk_x3f_5238_ = v_cancelTk_x3f_5216_;
v_suppressElabErrors_5239_ = v_suppressElabErrors_5217_;
v_inheritedTraceOptions_5240_ = v_inheritedTraceOptions_5218_;
v___y_5241_ = v___y_5202_;
goto v___jp_5227_;
}
}
}
else
{
v_fileName_5228_ = v_fileName_5205_;
v_fileMap_5229_ = v_fileMap_5206_;
v_currRecDepth_5230_ = v_currRecDepth_5208_;
v_ref_5231_ = v_ref_5209_;
v_currNamespace_5232_ = v_currNamespace_5210_;
v_openDecls_5233_ = v_openDecls_5211_;
v_initHeartbeats_5234_ = v_initHeartbeats_5212_;
v_maxHeartbeats_5235_ = v_maxHeartbeats_5213_;
v_quotContext_5236_ = v_quotContext_5214_;
v_currMacroScope_5237_ = v_currMacroScope_5215_;
v_cancelTk_x3f_5238_ = v_cancelTk_x3f_5216_;
v_suppressElabErrors_5239_ = v_suppressElabErrors_5217_;
v_inheritedTraceOptions_5240_ = v_inheritedTraceOptions_5218_;
v___y_5241_ = v___y_5202_;
goto v___jp_5227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed(lean_object* v___x_5273_, lean_object* v_value_5274_, lean_object* v___f_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
uint8_t v___x_4835__boxed_5281_; lean_object* v_res_5282_; 
v___x_4835__boxed_5281_ = lean_unbox(v___x_5273_);
v_res_5282_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(v___x_4835__boxed_5281_, v_value_5274_, v___f_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
return v_res_5282_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_5284_; lean_object* v___x_5285_; 
v___x_5284_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0));
v___x_5285_ = l_Lean_stringToMessageData(v___x_5284_);
return v___x_5285_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3(void){
_start:
{
lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5287_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__2));
v___x_5288_ = l_Lean_stringToMessageData(v___x_5287_);
return v___x_5288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object* v_preDef_5289_, lean_object* v_unaryPreDefName_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_){
_start:
{
lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v_env_5298_; lean_object* v_levelParams_5299_; lean_object* v_declName_5300_; lean_object* v_value_5301_; lean_object* v_env_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___f_5312_; lean_object* v___x_5313_; lean_object* v___f_5314_; uint8_t v___x_5315_; lean_object* v___x_5316_; lean_object* v___f_5317_; lean_object* v___x_5318_; 
v___x_5296_ = lean_st_ref_get(v_a_5294_);
v___x_5297_ = lean_st_ref_get(v_a_5294_);
v_env_5298_ = lean_ctor_get(v___x_5296_, 0);
lean_inc_ref(v_env_5298_);
lean_dec(v___x_5296_);
v_levelParams_5299_ = lean_ctor_get(v_preDef_5289_, 1);
lean_inc(v_levelParams_5299_);
v_declName_5300_ = lean_ctor_get(v_preDef_5289_, 3);
lean_inc(v_declName_5300_);
v_value_5301_ = lean_ctor_get(v_preDef_5289_, 7);
lean_inc_ref(v_value_5301_);
lean_dec_ref(v_preDef_5289_);
v_env_5302_ = lean_ctor_get(v___x_5297_, 0);
lean_inc_ref(v_env_5302_);
lean_dec(v___x_5297_);
v___x_5303_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_5300_);
v___x_5304_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5298_, v_declName_5300_, v___x_5303_);
v___x_5305_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5302_, v_unaryPreDefName_5290_, v___x_5303_);
v___x_5306_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1);
lean_inc(v___x_5304_);
v___x_5307_ = l_Lean_MessageData_ofName(v___x_5304_);
v___x_5308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5306_);
lean_ctor_set(v___x_5308_, 1, v___x_5307_);
v___x_5309_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3);
v___x_5310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5308_);
lean_ctor_set(v___x_5310_, 1, v___x_5309_);
lean_inc(v___x_5305_);
v___x_5311_ = l_Lean_MessageData_ofName(v___x_5305_);
lean_inc_ref(v___x_5311_);
v___f_5312_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5312_, 0, v_levelParams_5299_);
lean_closure_set(v___f_5312_, 1, v_declName_5300_);
lean_closure_set(v___f_5312_, 2, v___x_5305_);
lean_closure_set(v___f_5312_, 3, v___x_5304_);
lean_closure_set(v___f_5312_, 4, v___x_5311_);
v___x_5313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5313_, 0, v___x_5310_);
lean_ctor_set(v___x_5313_, 1, v___x_5311_);
v___f_5314_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_5314_, 0, v___x_5313_);
v___x_5315_ = 0;
v___x_5316_ = lean_box(v___x_5315_);
v___f_5317_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_5317_, 0, v___x_5316_);
lean_closure_set(v___f_5317_, 1, v_value_5301_);
lean_closure_set(v___f_5317_, 2, v___f_5312_);
v___x_5318_ = l_Lean_Meta_mapErrorImp___redArg(v___f_5317_, v___f_5314_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_);
if (lean_obj_tag(v___x_5318_) == 0)
{
lean_object* v_a_5319_; lean_object* v___x_5321_; uint8_t v_isShared_5322_; uint8_t v_isSharedCheck_5326_; 
v_a_5319_ = lean_ctor_get(v___x_5318_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5318_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5321_ = v___x_5318_;
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
else
{
lean_inc(v_a_5319_);
lean_dec(v___x_5318_);
v___x_5321_ = lean_box(0);
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
v_resetjp_5320_:
{
lean_object* v___x_5324_; 
if (v_isShared_5322_ == 0)
{
v___x_5324_ = v___x_5321_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
else
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5334_; 
v_a_5327_ = lean_ctor_get(v___x_5318_, 0);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5318_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5329_ = v___x_5318_;
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5318_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5332_; 
if (v_isShared_5330_ == 0)
{
v___x_5332_ = v___x_5329_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5327_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___boxed(lean_object* v_preDef_5335_, lean_object* v_unaryPreDefName_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_){
_start:
{
lean_object* v_res_5342_; 
v_res_5342_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_preDef_5335_, v_unaryPreDefName_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_);
return v_res_5342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5387_; uint8_t v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; 
v___x_5387_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5388_ = 0;
v___x_5389_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5390_ = l_Lean_registerTraceClass(v___x_5387_, v___x_5388_, v___x_5389_);
return v___x_5390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2____boxed(lean_object* v_a_5391_){
_start:
{
lean_object* v_res_5392_; 
v_res_5392_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_();
return v_res_5392_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_();
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
