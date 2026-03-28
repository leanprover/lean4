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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
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
uint8_t v___x_7425__boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v___x_7425__boxed_157_ = lean_unbox(v___x_155_);
v_res_158_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(v___x_7425__boxed_157_, v_x_156_);
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
uint8_t v___x_7433__boxed_188_; uint8_t v___x_7434__boxed_189_; lean_object* v_res_190_; 
v___x_7433__boxed_188_ = lean_unbox(v___x_179_);
v___x_7434__boxed_189_ = lean_unbox(v___x_180_);
v_res_190_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(v___x_177_, v___x_178_, v___x_7433__boxed_188_, v___x_7434__boxed_189_, v_ys_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_272_; size_t v___x_273_; size_t v___x_274_; 
v___x_272_ = ((size_t)5ULL);
v___x_273_ = ((size_t)1ULL);
v___x_274_ = lean_usize_shift_left(v___x_273_, v___x_272_);
return v___x_274_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; 
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_277_ = lean_usize_sub(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(lean_object* v_x_279_, size_t v_x_280_, size_t v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v_es_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; lean_object* v_j_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_es_284_ = lean_ctor_get(v_x_279_, 0);
v___x_285_ = ((size_t)5ULL);
v___x_286_ = ((size_t)1ULL);
v___x_287_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__1);
v___x_288_ = lean_usize_land(v_x_280_, v___x_287_);
v_j_289_ = lean_usize_to_nat(v___x_288_);
v___x_290_ = lean_array_get_size(v_es_284_);
v___x_291_ = lean_nat_dec_lt(v_j_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec(v_j_289_);
lean_dec(v_x_283_);
lean_dec(v_x_282_);
return v_x_279_;
}
else
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_328_; 
lean_inc_ref(v_es_284_);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_279_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_x_279_, 0);
lean_dec(v_unused_329_);
v___x_293_ = v_x_279_;
v_isShared_294_ = v_isSharedCheck_328_;
goto v_resetjp_292_;
}
else
{
lean_dec(v_x_279_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_328_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v_v_295_; lean_object* v___x_296_; lean_object* v_xs_x27_297_; lean_object* v___y_299_; 
v_v_295_ = lean_array_fget(v_es_284_, v_j_289_);
v___x_296_ = lean_box(0);
v_xs_x27_297_ = lean_array_fset(v_es_284_, v_j_289_, v___x_296_);
switch(lean_obj_tag(v_v_295_))
{
case 0:
{
lean_object* v_key_304_; lean_object* v_val_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_315_; 
v_key_304_ = lean_ctor_get(v_v_295_, 0);
v_val_305_ = lean_ctor_get(v_v_295_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v_v_295_);
if (v_isSharedCheck_315_ == 0)
{
v___x_307_ = v_v_295_;
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_val_305_);
lean_inc(v_key_304_);
lean_dec(v_v_295_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
uint8_t v___x_309_; 
v___x_309_ = l_Lean_instBEqMVarId_beq(v_x_282_, v_key_304_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_del_object(v___x_307_);
v___x_310_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_304_, v_val_305_, v_x_282_, v_x_283_);
v___x_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
v___y_299_ = v___x_311_;
goto v___jp_298_;
}
else
{
lean_object* v___x_313_; 
lean_dec(v_val_305_);
lean_dec(v_key_304_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v_x_283_);
lean_ctor_set(v___x_307_, 0, v_x_282_);
v___x_313_ = v___x_307_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_x_282_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_x_283_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
v___y_299_ = v___x_313_;
goto v___jp_298_;
}
}
}
}
case 1:
{
lean_object* v_node_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_326_; 
v_node_316_ = lean_ctor_get(v_v_295_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v_v_295_);
if (v_isSharedCheck_326_ == 0)
{
v___x_318_ = v_v_295_;
v_isShared_319_ = v_isSharedCheck_326_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_node_316_);
lean_dec(v_v_295_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_326_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
size_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_320_ = lean_usize_shift_right(v_x_280_, v___x_285_);
v___x_321_ = lean_usize_add(v_x_281_, v___x_286_);
v___x_322_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_node_316_, v___x_320_, v___x_321_, v_x_282_, v_x_283_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_322_);
v___x_324_ = v___x_318_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
v___y_299_ = v___x_324_;
goto v___jp_298_;
}
}
}
default: 
{
lean_object* v___x_327_; 
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v_x_282_);
lean_ctor_set(v___x_327_, 1, v_x_283_);
v___y_299_ = v___x_327_;
goto v___jp_298_;
}
}
v___jp_298_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_300_ = lean_array_fset(v_xs_x27_297_, v_j_289_, v___y_299_);
lean_dec(v_j_289_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_300_);
v___x_302_ = v___x_293_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
else
{
lean_object* v_ks_330_; lean_object* v_vs_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_351_; 
v_ks_330_ = lean_ctor_get(v_x_279_, 0);
v_vs_331_ = lean_ctor_get(v_x_279_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_x_279_);
if (v_isSharedCheck_351_ == 0)
{
v___x_333_ = v_x_279_;
v_isShared_334_ = v_isSharedCheck_351_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_vs_331_);
lean_inc(v_ks_330_);
lean_dec(v_x_279_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_351_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_ks_330_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_vs_331_);
v___x_336_ = v_reuseFailAlloc_350_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v_newNode_337_; uint8_t v___y_339_; size_t v___x_345_; uint8_t v___x_346_; 
v_newNode_337_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v___x_336_, v_x_282_, v_x_283_);
v___x_345_ = ((size_t)7ULL);
v___x_346_ = lean_usize_dec_le(v___x_345_, v_x_281_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_337_);
v___x_348_ = lean_unsigned_to_nat(4u);
v___x_349_ = lean_nat_dec_lt(v___x_347_, v___x_348_);
lean_dec(v___x_347_);
v___y_339_ = v___x_349_;
goto v___jp_338_;
}
else
{
v___y_339_ = v___x_346_;
goto v___jp_338_;
}
v___jp_338_:
{
if (v___y_339_ == 0)
{
lean_object* v_ks_340_; lean_object* v_vs_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_ks_340_ = lean_ctor_get(v_newNode_337_, 0);
lean_inc_ref(v_ks_340_);
v_vs_341_ = lean_ctor_get(v_newNode_337_, 1);
lean_inc_ref(v_vs_341_);
lean_dec_ref(v_newNode_337_);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__2);
v___x_344_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_x_281_, v_ks_340_, v_vs_341_, v___x_342_, v___x_343_);
lean_dec_ref(v_vs_341_);
lean_dec_ref(v_ks_340_);
return v___x_344_;
}
else
{
return v_newNode_337_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_352_, lean_object* v_keys_353_, lean_object* v_vals_354_, lean_object* v_i_355_, lean_object* v_entries_356_){
_start:
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_array_get_size(v_keys_353_);
v___x_358_ = lean_nat_dec_lt(v_i_355_, v___x_357_);
if (v___x_358_ == 0)
{
lean_dec(v_i_355_);
return v_entries_356_;
}
else
{
lean_object* v_k_359_; lean_object* v_v_360_; uint64_t v___x_361_; size_t v_h_362_; size_t v___x_363_; lean_object* v___x_364_; size_t v___x_365_; size_t v___x_366_; size_t v___x_367_; size_t v_h_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_k_359_ = lean_array_fget_borrowed(v_keys_353_, v_i_355_);
v_v_360_ = lean_array_fget_borrowed(v_vals_354_, v_i_355_);
v___x_361_ = l_Lean_instHashableMVarId_hash(v_k_359_);
v_h_362_ = lean_uint64_to_usize(v___x_361_);
v___x_363_ = ((size_t)5ULL);
v___x_364_ = lean_unsigned_to_nat(1u);
v___x_365_ = ((size_t)1ULL);
v___x_366_ = lean_usize_sub(v_depth_352_, v___x_365_);
v___x_367_ = lean_usize_mul(v___x_363_, v___x_366_);
v_h_368_ = lean_usize_shift_right(v_h_362_, v___x_367_);
v___x_369_ = lean_nat_add(v_i_355_, v___x_364_);
lean_dec(v_i_355_);
lean_inc(v_v_360_);
lean_inc(v_k_359_);
v___x_370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_entries_356_, v_h_368_, v_depth_352_, v_k_359_, v_v_360_);
v_i_355_ = v___x_369_;
v_entries_356_ = v___x_370_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_372_, lean_object* v_keys_373_, lean_object* v_vals_374_, lean_object* v_i_375_, lean_object* v_entries_376_){
_start:
{
size_t v_depth_boxed_377_; lean_object* v_res_378_; 
v_depth_boxed_377_ = lean_unbox_usize(v_depth_372_);
lean_dec(v_depth_372_);
v_res_378_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_377_, v_keys_373_, v_vals_374_, v_i_375_, v_entries_376_);
lean_dec_ref(v_vals_374_);
lean_dec_ref(v_keys_373_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
size_t v_x_7623__boxed_384_; size_t v_x_7624__boxed_385_; lean_object* v_res_386_; 
v_x_7623__boxed_384_ = lean_unbox_usize(v_x_380_);
lean_dec(v_x_380_);
v_x_7624__boxed_385_ = lean_unbox_usize(v_x_381_);
lean_dec(v_x_381_);
v_res_386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_379_, v_x_7623__boxed_384_, v_x_7624__boxed_385_, v_x_382_, v_x_383_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_x_389_){
_start:
{
uint64_t v___x_390_; size_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; 
v___x_390_ = l_Lean_instHashableMVarId_hash(v_x_388_);
v___x_391_ = lean_uint64_to_usize(v___x_390_);
v___x_392_ = ((size_t)1ULL);
v___x_393_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_387_, v___x_391_, v___x_392_, v_x_388_, v_x_389_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(lean_object* v_mvarId_394_, lean_object* v_val_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; lean_object* v_mctx_399_; lean_object* v_cache_400_; lean_object* v_zetaDeltaFVarIds_401_; lean_object* v_postponed_402_; lean_object* v_diag_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_430_; 
v___x_398_ = lean_st_ref_take(v___y_396_);
v_mctx_399_ = lean_ctor_get(v___x_398_, 0);
v_cache_400_ = lean_ctor_get(v___x_398_, 1);
v_zetaDeltaFVarIds_401_ = lean_ctor_get(v___x_398_, 2);
v_postponed_402_ = lean_ctor_get(v___x_398_, 3);
v_diag_403_ = lean_ctor_get(v___x_398_, 4);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_430_ == 0)
{
v___x_405_ = v___x_398_;
v_isShared_406_ = v_isSharedCheck_430_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_diag_403_);
lean_inc(v_postponed_402_);
lean_inc(v_zetaDeltaFVarIds_401_);
lean_inc(v_cache_400_);
lean_inc(v_mctx_399_);
lean_dec(v___x_398_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_430_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v_depth_407_; lean_object* v_levelAssignDepth_408_; lean_object* v_mvarCounter_409_; lean_object* v_lDepth_410_; lean_object* v_decls_411_; lean_object* v_userNames_412_; lean_object* v_lAssignment_413_; lean_object* v_eAssignment_414_; lean_object* v_dAssignment_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_429_; 
v_depth_407_ = lean_ctor_get(v_mctx_399_, 0);
v_levelAssignDepth_408_ = lean_ctor_get(v_mctx_399_, 1);
v_mvarCounter_409_ = lean_ctor_get(v_mctx_399_, 2);
v_lDepth_410_ = lean_ctor_get(v_mctx_399_, 3);
v_decls_411_ = lean_ctor_get(v_mctx_399_, 4);
v_userNames_412_ = lean_ctor_get(v_mctx_399_, 5);
v_lAssignment_413_ = lean_ctor_get(v_mctx_399_, 6);
v_eAssignment_414_ = lean_ctor_get(v_mctx_399_, 7);
v_dAssignment_415_ = lean_ctor_get(v_mctx_399_, 8);
v_isSharedCheck_429_ = !lean_is_exclusive(v_mctx_399_);
if (v_isSharedCheck_429_ == 0)
{
v___x_417_ = v_mctx_399_;
v_isShared_418_ = v_isSharedCheck_429_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_dAssignment_415_);
lean_inc(v_eAssignment_414_);
lean_inc(v_lAssignment_413_);
lean_inc(v_userNames_412_);
lean_inc(v_decls_411_);
lean_inc(v_lDepth_410_);
lean_inc(v_mvarCounter_409_);
lean_inc(v_levelAssignDepth_408_);
lean_inc(v_depth_407_);
lean_dec(v_mctx_399_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_429_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_eAssignment_414_, v_mvarId_394_, v_val_395_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 7, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_depth_407_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_levelAssignDepth_408_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_mvarCounter_409_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_lDepth_410_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_decls_411_);
lean_ctor_set(v_reuseFailAlloc_428_, 5, v_userNames_412_);
lean_ctor_set(v_reuseFailAlloc_428_, 6, v_lAssignment_413_);
lean_ctor_set(v_reuseFailAlloc_428_, 7, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_428_, 8, v_dAssignment_415_);
v___x_421_ = v_reuseFailAlloc_428_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_423_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_421_);
v___x_423_ = v___x_405_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_cache_400_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_zetaDeltaFVarIds_401_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_postponed_402_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v_diag_403_);
v___x_423_ = v_reuseFailAlloc_427_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_st_ref_set(v___y_396_, v___x_423_);
v___x_425_ = lean_box(0);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg___boxed(lean_object* v_mvarId_431_, lean_object* v_val_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_431_, v_val_432_, v___y_433_);
lean_dec(v___y_433_);
return v_res_435_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_442_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4));
v___x_443_ = lean_unsigned_to_nat(41u);
v___x_444_ = lean_unsigned_to_nat(34u);
v___x_445_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3));
v___x_446_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_447_ = l_mkPanicMessageWithDecl(v___x_446_, v___x_445_, v___x_444_, v___x_443_, v___x_442_);
return v___x_447_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9));
v___x_455_ = l_Lean_stringToMessageData(v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18(void){
_start:
{
lean_object* v___x_470_; lean_object* v_dummy_471_; 
v___x_470_ = lean_box(0);
v_dummy_471_ = l_Lean_Expr_sort___override(v___x_470_);
return v_dummy_471_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object* v_mvarId_479_, lean_object* v___x_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
lean_inc(v_mvarId_479_);
v___x_486_ = l_Lean_MVarId_getType_x27(v_mvarId_479_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref(v___x_486_);
v___x_488_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_489_ = lean_unsigned_to_nat(3u);
v___x_490_ = l_Lean_Expr_isAppOfArity(v_a_487_, v___x_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_a_487_);
lean_dec_ref(v___x_480_);
lean_dec(v_mvarId_479_);
v___x_491_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5);
v___x_492_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(v___x_491_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v___x_492_;
}
else
{
lean_object* v___x_493_; lean_object* v___f_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; 
v___x_493_ = lean_box(v___x_490_);
v___f_494_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_494_, 0, v___x_493_);
v___x_495_ = l_Lean_Expr_appFn_x21(v_a_487_);
v___x_496_ = l_Lean_Expr_appArg_x21(v___x_495_);
lean_dec_ref(v___x_495_);
v___x_497_ = 0;
lean_inc_ref(v___x_496_);
v___x_498_ = l_Lean_Meta_delta_x3f(v___x_496_, v___f_494_, v___x_497_, v___y_483_, v___y_484_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
if (lean_obj_tag(v_a_499_) == 1)
{
lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_653_; 
v_val_500_ = lean_ctor_get(v_a_499_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_a_499_);
if (v_isSharedCheck_653_ == 0)
{
v___x_502_ = v_a_499_;
v_isShared_503_ = v_isSharedCheck_653_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_dec(v_a_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_653_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; 
lean_inc(v_val_500_);
v___x_504_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_val_500_, v___y_482_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___f_508_; lean_object* v___x_509_; lean_object* v_h_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
v___x_506_ = lean_box(v___x_497_);
v___x_507_ = lean_box(v___x_490_);
v___f_508_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed), 11, 4);
lean_closure_set(v___f_508_, 0, v___x_496_);
lean_closure_set(v___f_508_, 1, v___x_480_);
lean_closure_set(v___f_508_, 2, v___x_506_);
lean_closure_set(v___f_508_, 3, v___x_507_);
v___x_509_ = l_Lean_Expr_appArg_x21(v_a_487_);
lean_dec(v_a_487_);
v___x_606_ = l_Lean_Expr_cleanupAnnotations(v_a_505_);
v___x_607_ = l_Lean_Expr_isApp(v___x_606_);
if (v___x_607_ == 0)
{
lean_dec_ref(v___x_606_);
v___y_585_ = v___y_481_;
v___y_586_ = v___y_482_;
v___y_587_ = v___y_483_;
v___y_588_ = v___y_484_;
goto v___jp_584_;
}
else
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = l_Lean_Expr_appFnCleanup___redArg(v___x_606_);
v___x_609_ = l_Lean_Expr_isApp(v___x_608_);
if (v___x_609_ == 0)
{
lean_dec_ref(v___x_608_);
v___y_585_ = v___y_481_;
v___y_586_ = v___y_482_;
v___y_587_ = v___y_483_;
v___y_588_ = v___y_484_;
goto v___jp_584_;
}
else
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = l_Lean_Expr_appFnCleanup___redArg(v___x_608_);
v___x_611_ = l_Lean_Expr_isApp(v___x_610_);
if (v___x_611_ == 0)
{
lean_dec_ref(v___x_610_);
v___y_585_ = v___y_481_;
v___y_586_ = v___y_482_;
v___y_587_ = v___y_483_;
v___y_588_ = v___y_484_;
goto v___jp_584_;
}
else
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_610_);
v___x_613_ = l_Lean_Expr_isApp(v___x_612_);
if (v___x_613_ == 0)
{
lean_dec_ref(v___x_612_);
v___y_585_ = v___y_481_;
v___y_586_ = v___y_482_;
v___y_587_ = v___y_483_;
v___y_588_ = v___y_484_;
goto v___jp_584_;
}
else
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = l_Lean_Expr_appFnCleanup___redArg(v___x_612_);
v___x_615_ = l_Lean_Expr_isApp(v___x_614_);
if (v___x_615_ == 0)
{
lean_dec_ref(v___x_614_);
v___y_585_ = v___y_481_;
v___y_586_ = v___y_482_;
v___y_587_ = v___y_483_;
v___y_588_ = v___y_484_;
goto v___jp_584_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_616_ = l_Lean_Expr_appFnCleanup___redArg(v___x_614_);
v___x_617_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14));
v___x_618_ = l_Lean_Expr_isConstOf(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
uint8_t v___x_619_; 
v___x_619_ = l_Lean_Expr_isApp(v___x_616_);
if (v___x_619_ == 0)
{
lean_dec_ref(v___x_616_);
v___y_585_ = v___y_481_;
v___y_586_ = v___y_482_;
v___y_587_ = v___y_483_;
v___y_588_ = v___y_484_;
goto v___jp_584_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = l_Lean_Expr_appFnCleanup___redArg(v___x_616_);
v___x_621_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15));
v___x_622_ = l_Lean_Expr_isConstOf(v___x_620_, v___x_621_);
lean_dec_ref(v___x_620_);
if (v___x_622_ == 0)
{
v___y_585_ = v___y_481_;
v___y_586_ = v___y_482_;
v___y_587_ = v___y_483_;
v___y_588_ = v___y_484_;
goto v___jp_584_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_dummy_627_; lean_object* v_nargs_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_del_object(v___x_502_);
v___x_623_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17));
v___x_624_ = l_Lean_Expr_getAppFn(v_val_500_);
v___x_625_ = l_Lean_Expr_constLevels_x21(v___x_624_);
lean_dec_ref(v___x_624_);
v___x_626_ = l_Lean_mkConst(v___x_623_, v___x_625_);
v_dummy_627_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_628_ = l_Lean_Expr_getAppNumArgs(v_val_500_);
lean_inc(v_nargs_628_);
v___x_629_ = lean_mk_array(v_nargs_628_, v_dummy_627_);
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_sub(v_nargs_628_, v___x_630_);
lean_dec(v_nargs_628_);
lean_inc(v_val_500_);
v___x_632_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_500_, v___x_629_, v___x_631_);
v___x_633_ = l_Lean_mkAppN(v___x_626_, v___x_632_);
lean_dec_ref(v___x_632_);
v_h_511_ = v___x_633_;
v___y_512_ = v___y_481_;
v___y_513_ = v___y_482_;
v___y_514_ = v___y_483_;
v___y_515_ = v___y_484_;
goto v___jp_510_;
}
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_dummy_638_; lean_object* v_nargs_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec_ref(v___x_616_);
lean_del_object(v___x_502_);
v___x_634_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19));
v___x_635_ = l_Lean_Expr_getAppFn(v_val_500_);
v___x_636_ = l_Lean_Expr_constLevels_x21(v___x_635_);
lean_dec_ref(v___x_635_);
v___x_637_ = l_Lean_mkConst(v___x_634_, v___x_636_);
v_dummy_638_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_639_ = l_Lean_Expr_getAppNumArgs(v_val_500_);
lean_inc(v_nargs_639_);
v___x_640_ = lean_mk_array(v_nargs_639_, v_dummy_638_);
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_sub(v_nargs_639_, v___x_641_);
lean_dec(v_nargs_639_);
lean_inc(v_val_500_);
v___x_643_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_500_, v___x_640_, v___x_642_);
v___x_644_ = l_Lean_mkAppN(v___x_637_, v___x_643_);
lean_dec_ref(v___x_643_);
v_h_511_ = v___x_644_;
v___y_512_ = v___y_481_;
v___y_513_ = v___y_482_;
v___y_514_ = v___y_483_;
v___y_515_ = v___y_484_;
goto v___jp_510_;
}
}
}
}
}
}
v___jp_510_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_516_ = l_Lean_Expr_appFn_x21(v_val_500_);
v___x_517_ = l_Lean_Expr_appArg_x21(v___x_516_);
lean_dec_ref(v___x_516_);
v___x_518_ = l_Lean_Expr_appArg_x21(v_val_500_);
lean_dec(v_val_500_);
lean_inc_ref(v___x_518_);
lean_inc_ref(v___x_517_);
v___x_519_ = l_Lean_Expr_app___override(v___x_517_, v___x_518_);
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
lean_inc(v___y_513_);
lean_inc_ref(v___y_512_);
v___x_520_ = lean_infer_type(v___x_519_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v___x_520_);
v___x_522_ = l_Lean_Expr_bindingDomain_x21(v_a_521_);
lean_dec(v_a_521_);
v___x_523_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_524_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_522_, v___x_523_, v___f_508_, v___x_497_, v___x_497_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref(v___x_524_);
v___x_526_ = l_Lean_mkAppB(v___x_517_, v___x_518_, v_a_525_);
v___x_527_ = l_Lean_Meta_mkEq(v___x_526_, v___x_509_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref(v___x_527_);
v___x_529_ = lean_box(0);
v___x_530_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_528_, v___x_529_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_n(v_a_531_, 2);
lean_dec_ref(v___x_530_);
v___x_532_ = l_Lean_Meta_mkEqTrans(v_h_511_, v_a_531_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec_ref(v___y_512_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_542_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref(v___x_532_);
v___x_534_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_479_, v_a_533_, v___y_513_);
lean_dec(v___y_513_);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v___x_534_, 0);
lean_dec(v_unused_543_);
v___x_536_ = v___x_534_;
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
else
{
lean_dec(v___x_534_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_Lean_Expr_mvarId_x21(v_a_531_);
lean_dec(v_a_531_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec(v_a_531_);
lean_dec(v___y_513_);
lean_dec(v_mvarId_479_);
v_a_544_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_532_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_532_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v_h_511_);
lean_dec(v_mvarId_479_);
v_a_552_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_530_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_530_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v_h_511_);
lean_dec(v_mvarId_479_);
v_a_560_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_527_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_527_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec_ref(v___x_518_);
lean_dec_ref(v___x_517_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v_h_511_);
lean_dec_ref(v___x_509_);
lean_dec(v_mvarId_479_);
v_a_568_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_524_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_524_);
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
lean_dec_ref(v___x_518_);
lean_dec_ref(v___x_517_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v_h_511_);
lean_dec_ref(v___x_509_);
lean_dec_ref(v___f_508_);
lean_dec(v_mvarId_479_);
v_a_576_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_520_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_520_);
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
v___jp_584_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_589_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8));
v___x_590_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10);
lean_inc(v_val_500_);
v___x_591_ = l_Lean_MessageData_ofExpr(v_val_500_);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_592_);
v___x_594_ = v___x_502_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_605_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; 
lean_inc(v_mvarId_479_);
v___x_595_ = l_Lean_Meta_throwTacticEx___redArg(v___x_589_, v_mvarId_479_, v___x_594_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref(v___x_595_);
v_h_511_ = v_a_596_;
v___y_512_ = v___y_585_;
v___y_513_ = v___y_586_;
v___y_514_ = v___y_587_;
v___y_515_ = v___y_588_;
goto v___jp_510_;
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec_ref(v___x_509_);
lean_dec_ref(v___f_508_);
lean_dec(v_val_500_);
lean_dec(v_mvarId_479_);
v_a_597_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_595_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_595_);
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
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_del_object(v___x_502_);
lean_dec(v_val_500_);
lean_dec_ref(v___x_496_);
lean_dec(v_a_487_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec_ref(v___x_480_);
lean_dec(v_mvarId_479_);
v_a_645_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_504_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_504_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v_a_499_);
lean_dec(v_a_487_);
lean_dec_ref(v___x_480_);
lean_dec(v_mvarId_479_);
v___x_654_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21);
v___x_655_ = l_Lean_MessageData_ofExpr(v___x_496_);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_656_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v___x_657_;
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v___x_496_);
lean_dec(v_a_487_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec_ref(v___x_480_);
lean_dec(v_mvarId_479_);
v_a_658_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_498_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_498_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec_ref(v___x_480_);
lean_dec(v_mvarId_479_);
v_a_666_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_486_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_486_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed(lean_object* v_mvarId_674_, lean_object* v___x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(v_mvarId_674_, v___x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(lean_object* v_mvarId_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; lean_object* v___f_689_; lean_object* v___x_690_; 
v___x_688_ = l_Lean_instInhabitedExpr;
lean_inc(v_mvarId_682_);
v___f_689_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed), 7, 2);
lean_closure_set(v___f_689_, 0, v_mvarId_682_);
lean_closure_set(v___f_689_, 1, v___x_688_);
v___x_690_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(v_mvarId_682_, v___f_689_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___boxed(lean_object* v_mvarId_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(lean_object* v_mvarId_698_, lean_object* v_val_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_698_, v_val_699_, v___y_701_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___boxed(lean_object* v_mvarId_706_, lean_object* v_val_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(v_mvarId_706_, v_val_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(lean_object* v_00_u03b1_714_, lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___boxed(lean_object* v_00_u03b1_722_, lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(v_00_u03b1_722_, v_msg_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2(lean_object* v_00_u03b2_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_x_731_, v_x_732_, v_x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_735_, lean_object* v_x_736_, size_t v_x_737_, size_t v_x_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_736_, v_x_737_, v_x_738_, v_x_739_, v_x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_742_, lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
size_t v_x_8408__boxed_748_; size_t v_x_8409__boxed_749_; lean_object* v_res_750_; 
v_x_8408__boxed_748_ = lean_unbox_usize(v_x_744_);
lean_dec(v_x_744_);
v_x_8409__boxed_749_ = lean_unbox_usize(v_x_745_);
lean_dec(v_x_745_);
v_res_750_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(v_00_u03b2_742_, v_x_743_, v_x_8408__boxed_748_, v_x_8409__boxed_749_, v_x_746_, v_x_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_751_, lean_object* v_n_752_, lean_object* v_k_753_, lean_object* v_v_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v_n_752_, v_k_753_, v_v_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_756_, size_t v_depth_757_, lean_object* v_keys_758_, lean_object* v_vals_759_, lean_object* v_heq_760_, lean_object* v_i_761_, lean_object* v_entries_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_757_, v_keys_758_, v_vals_759_, v_i_761_, v_entries_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_764_, lean_object* v_depth_765_, lean_object* v_keys_766_, lean_object* v_vals_767_, lean_object* v_heq_768_, lean_object* v_i_769_, lean_object* v_entries_770_){
_start:
{
size_t v_depth_boxed_771_; lean_object* v_res_772_; 
v_depth_boxed_771_ = lean_unbox_usize(v_depth_765_);
lean_dec(v_depth_765_);
v_res_772_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_764_, v_depth_boxed_771_, v_keys_766_, v_vals_767_, v_heq_768_, v_i_769_, v_entries_770_);
lean_dec_ref(v_vals_767_);
lean_dec_ref(v_keys_766_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_774_, v_x_775_, v_x_776_, v_x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(lean_object* v_e_779_, lean_object* v_maxFVars_780_, lean_object* v_k_781_, uint8_t v_cleanupAnnotations_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___f_788_; uint8_t v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___f_788_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_788_, 0, v_k_781_);
v___x_789_ = 1;
v___x_790_ = 0;
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v_maxFVars_780_);
v___x_792_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_779_, v___x_789_, v___x_790_, v___x_789_, v___x_790_, v___x_791_, v___f_788_, v_cleanupAnnotations_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec_ref(v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
v_a_801_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_792_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_792_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg___boxed(lean_object* v_e_809_, lean_object* v_maxFVars_810_, lean_object* v_k_811_, lean_object* v_cleanupAnnotations_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_818_; lean_object* v_res_819_; 
v_cleanupAnnotations_boxed_818_ = lean_unbox(v_cleanupAnnotations_812_);
v_res_819_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_809_, v_maxFVars_810_, v_k_811_, v_cleanupAnnotations_boxed_818_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(lean_object* v_00_u03b1_820_, lean_object* v_e_821_, lean_object* v_maxFVars_822_, lean_object* v_k_823_, uint8_t v_cleanupAnnotations_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_821_, v_maxFVars_822_, v_k_823_, v_cleanupAnnotations_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___boxed(lean_object* v_00_u03b1_831_, lean_object* v_e_832_, lean_object* v_maxFVars_833_, lean_object* v_k_834_, lean_object* v_cleanupAnnotations_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_841_; lean_object* v_res_842_; 
v_cleanupAnnotations_boxed_841_ = lean_unbox(v_cleanupAnnotations_835_);
v_res_842_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(v_00_u03b1_831_, v_e_832_, v_maxFVars_833_, v_k_834_, v_cleanupAnnotations_boxed_841_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(lean_object* v___x_843_, lean_object* v_xs_844_, lean_object* v_t_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___y_855_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_878_ = lean_array_get_size(v_xs_844_);
v___x_879_ = lean_nat_dec_eq(v___x_878_, v___x_843_);
if (v___x_879_ == 0)
{
v___y_855_ = v___x_879_;
goto v___jp_854_;
}
else
{
uint8_t v___x_880_; 
v___x_880_ = l_Lean_Expr_isForall(v_t_845_);
v___y_855_ = v___x_880_;
goto v___jp_854_;
}
v___jp_851_:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_box(0);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
v___jp_854_:
{
if (v___y_855_ == 0)
{
goto v___jp_851_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_856_ = l_Lean_Expr_bindingBody_x21(v_t_845_);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_expr_has_loose_bvar(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; lean_object* v___x_860_; 
v___x_859_ = 1;
v___x_860_ = l_Lean_Meta_mkLambdaFVars(v_xs_844_, v___x_856_, v___x_858_, v___y_855_, v___x_858_, v___y_855_, v___x_859_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_869_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v_a_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_870_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_860_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_860_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_dec_ref(v___x_856_);
goto v___jp_851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed(lean_object* v___x_881_, lean_object* v_xs_882_, lean_object* v_t_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(v___x_881_, v_xs_882_, v_t_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_t_883_);
lean_dec_ref(v_xs_882_);
lean_dec(v___x_881_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(lean_object* v_matcherApp_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_motive_896_; lean_object* v_discrs_897_; lean_object* v___x_898_; lean_object* v___f_899_; uint8_t v___x_900_; lean_object* v___x_901_; 
v_motive_896_ = lean_ctor_get(v_matcherApp_890_, 4);
lean_inc_ref(v_motive_896_);
v_discrs_897_ = lean_ctor_get(v_matcherApp_890_, 5);
lean_inc_ref(v_discrs_897_);
lean_dec_ref(v_matcherApp_890_);
v___x_898_ = lean_array_get_size(v_discrs_897_);
lean_dec_ref(v_discrs_897_);
v___f_899_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed), 8, 1);
lean_closure_set(v___f_899_, 0, v___x_898_);
v___x_900_ = 0;
v___x_901_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_motive_896_, v___x_898_, v___f_899_, v___x_900_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___boxed(lean_object* v_matcherApp_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_matcherApp_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(lean_object* v_e_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; lean_object* v_env_913_; uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_912_ = lean_st_ref_get(v___y_910_);
v_env_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_env_913_);
lean_dec(v___x_912_);
v___x_914_ = l_Lean_Meta_isMatcherAppCore(v_env_913_, v_e_909_);
v___x_915_ = lean_box(v___x_914_);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg___boxed(lean_object* v_e_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v_e_917_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(lean_object* v_e_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_921_, v___y_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___boxed(lean_object* v_e_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(v_e_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec_ref(v_e_928_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(lean_object* v_msg_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___f_941_; lean_object* v___x_864__overap_942_; lean_object* v___x_943_; 
v___f_941_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_864__overap_942_ = lean_panic_fn_borrowed(v___f_941_, v_msg_935_);
lean_inc(v___y_939_);
lean_inc_ref(v___y_938_);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
v___x_943_ = lean_apply_5(v___x_864__overap_942_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, lean_box(0));
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1___boxed(lean_object* v_msg_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v_msg_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(size_t v_sz_951_, size_t v_i_952_, lean_object* v_bs_953_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = lean_usize_dec_lt(v_i_952_, v_sz_951_);
if (v___x_954_ == 0)
{
return v_bs_953_;
}
else
{
lean_object* v_v_955_; lean_object* v_toInductionSubgoal_956_; lean_object* v_mvarId_957_; lean_object* v___x_958_; lean_object* v_bs_x27_959_; size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; 
v_v_955_ = lean_array_uget_borrowed(v_bs_953_, v_i_952_);
v_toInductionSubgoal_956_ = lean_ctor_get(v_v_955_, 0);
v_mvarId_957_ = lean_ctor_get(v_toInductionSubgoal_956_, 0);
lean_inc(v_mvarId_957_);
v___x_958_ = lean_unsigned_to_nat(0u);
v_bs_x27_959_ = lean_array_uset(v_bs_953_, v_i_952_, v___x_958_);
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_add(v_i_952_, v___x_960_);
v___x_962_ = lean_array_uset(v_bs_x27_959_, v_i_952_, v_mvarId_957_);
v_i_952_ = v___x_961_;
v_bs_953_ = v___x_962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2___boxed(lean_object* v_sz_964_, lean_object* v_i_965_, lean_object* v_bs_966_){
_start:
{
size_t v_sz_boxed_967_; size_t v_i_boxed_968_; lean_object* v_res_969_; 
v_sz_boxed_967_ = lean_unbox_usize(v_sz_964_);
lean_dec(v_sz_964_);
v_i_boxed_968_ = lean_unbox_usize(v_i_965_);
lean_dec(v_i_965_);
v_res_969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_boxed_967_, v_i_boxed_968_, v_bs_966_);
return v_res_969_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_972_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1));
v___x_973_ = lean_unsigned_to_nat(4u);
v___x_974_ = lean_unsigned_to_nat(76u);
v___x_975_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0));
v___x_976_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_977_ = l_mkPanicMessageWithDecl(v___x_976_, v___x_975_, v___x_974_, v___x_973_, v___x_972_);
return v___x_977_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__4(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_979_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3));
v___x_980_ = lean_unsigned_to_nat(4u);
v___x_981_ = lean_unsigned_to_nat(78u);
v___x_982_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0));
v___x_983_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_984_ = l_mkPanicMessageWithDecl(v___x_983_, v___x_982_, v___x_981_, v___x_980_, v___x_979_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(lean_object* v_mvarId_987_, lean_object* v_e_988_, lean_object* v_matcherInfo_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_995_; lean_object* v_a_996_; uint8_t v___x_997_; 
v___x_995_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_988_, v_a_993_);
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref(v___x_995_);
v___x_997_ = lean_unbox(v_a_996_);
if (v___x_997_ == 0)
{
lean_object* v_numParams_998_; lean_object* v_numDiscrs_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_numParams_998_ = lean_ctor_get(v_matcherInfo_989_, 0);
v_numDiscrs_999_ = lean_ctor_get(v_matcherInfo_989_, 1);
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = lean_nat_dec_eq(v_numDiscrs_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v_a_996_);
lean_dec_ref(v_e_988_);
lean_dec(v_mvarId_987_);
v___x_1002_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2);
v___x_1003_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v___x_1002_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
return v___x_1003_;
}
else
{
lean_object* v___x_1004_; lean_object* v_dummy_1005_; lean_object* v_nargs_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1004_ = l_Lean_instInhabitedExpr;
v_dummy_1005_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_1006_ = l_Lean_Expr_getAppNumArgs(v_e_988_);
lean_inc(v_nargs_1006_);
v___x_1007_ = lean_mk_array(v_nargs_1006_, v_dummy_1005_);
v___x_1008_ = lean_nat_sub(v_nargs_1006_, v___x_1000_);
lean_dec(v_nargs_1006_);
v___x_1009_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_988_, v___x_1007_, v___x_1008_);
v___x_1010_ = lean_nat_add(v_numParams_998_, v___x_1000_);
v___x_1011_ = lean_array_get(v___x_1004_, v___x_1009_, v___x_1010_);
lean_dec(v___x_1010_);
lean_dec_ref(v___x_1009_);
v___x_1012_ = l_Lean_Expr_isFVar(v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec(v___x_1011_);
lean_dec(v_a_996_);
lean_dec(v_mvarId_987_);
v___x_1013_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__4);
v___x_1014_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v___x_1013_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; lean_object* v___x_1019_; 
v___x_1015_ = l_Lean_Expr_fvarId_x21(v___x_1011_);
lean_dec(v___x_1011_);
v___x_1016_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__5));
v___x_1017_ = lean_box(0);
v___x_1018_ = lean_unbox(v_a_996_);
lean_dec(v_a_996_);
v___x_1019_ = l_Lean_MVarId_cases(v_mvarId_987_, v___x_1015_, v___x_1016_, v___x_1018_, v___x_1017_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1031_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1031_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1031_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
size_t v_sz_1024_; size_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v_sz_1024_ = lean_array_size(v_a_1020_);
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_1024_, v___x_1025_, v_a_1020_);
v___x_1027_ = lean_array_to_list(v___x_1026_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1027_);
v___x_1029_ = v___x_1022_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_a_1032_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1019_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1019_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
else
{
lean_object* v___x_1040_; 
lean_dec(v_a_996_);
v___x_1040_ = l_Lean_Meta_Split_splitMatch(v_mvarId_987_, v_e_988_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___boxed(lean_object* v_mvarId_1041_, lean_object* v_e_1042_, lean_object* v_matcherInfo_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v_mvarId_1041_, v_e_1042_, v_matcherInfo_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec_ref(v_matcherInfo_1043_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(lean_object* v_msg_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___f_1056_; lean_object* v___x_12210__overap_1057_; lean_object* v___x_1058_; 
v___f_1056_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_12210__overap_1057_ = lean_panic_fn_borrowed(v___f_1056_, v_msg_1050_);
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
v___x_1058_ = lean_apply_5(v___x_12210__overap_1057_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, lean_box(0));
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1___boxed(lean_object* v_msg_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v_msg_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(lean_object* v_type_1066_, lean_object* v_k_1067_, uint8_t v_cleanupAnnotations_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___f_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___f_1074_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1074_, 0, v_k_1067_);
v___x_1075_ = 0;
v___x_1076_ = lean_box(0);
v___x_1077_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1075_, v___x_1076_, v_type_1066_, v___f_1074_, v_cleanupAnnotations_1068_, v___x_1075_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_a_1086_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1077_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1077_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg___boxed(lean_object* v_type_1094_, lean_object* v_k_1095_, lean_object* v_cleanupAnnotations_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1102_; lean_object* v_res_1103_; 
v_cleanupAnnotations_boxed_1102_ = lean_unbox(v_cleanupAnnotations_1096_);
v_res_1103_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1094_, v_k_1095_, v_cleanupAnnotations_boxed_1102_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(lean_object* v_00_u03b1_1104_, lean_object* v_type_1105_, lean_object* v_k_1106_, uint8_t v_cleanupAnnotations_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1105_, v_k_1106_, v_cleanupAnnotations_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___boxed(lean_object* v_00_u03b1_1114_, lean_object* v_type_1115_, lean_object* v_k_1116_, lean_object* v_cleanupAnnotations_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1123_; lean_object* v_res_1124_; 
v_cleanupAnnotations_boxed_1123_ = lean_unbox(v_cleanupAnnotations_1117_);
v_res_1124_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(v_00_u03b1_1114_, v_type_1115_, v_k_1116_, v_cleanupAnnotations_boxed_1123_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(lean_object* v_e_1125_, lean_object* v___y_1126_){
_start:
{
uint8_t v___x_1128_; 
v___x_1128_ = l_Lean_Expr_hasMVar(v_e_1125_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_e_1125_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; lean_object* v_mctx_1131_; lean_object* v___x_1132_; lean_object* v_fst_1133_; lean_object* v_snd_1134_; lean_object* v___x_1135_; lean_object* v_cache_1136_; lean_object* v_zetaDeltaFVarIds_1137_; lean_object* v_postponed_1138_; lean_object* v_diag_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1148_; 
v___x_1130_ = lean_st_ref_get(v___y_1126_);
v_mctx_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc_ref(v_mctx_1131_);
lean_dec(v___x_1130_);
v___x_1132_ = l_Lean_instantiateMVarsCore(v_mctx_1131_, v_e_1125_);
v_fst_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_fst_1133_);
v_snd_1134_ = lean_ctor_get(v___x_1132_, 1);
lean_inc(v_snd_1134_);
lean_dec_ref(v___x_1132_);
v___x_1135_ = lean_st_ref_take(v___y_1126_);
v_cache_1136_ = lean_ctor_get(v___x_1135_, 1);
v_zetaDeltaFVarIds_1137_ = lean_ctor_get(v___x_1135_, 2);
v_postponed_1138_ = lean_ctor_get(v___x_1135_, 3);
v_diag_1139_ = lean_ctor_get(v___x_1135_, 4);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v___x_1135_, 0);
lean_dec(v_unused_1149_);
v___x_1141_ = v___x_1135_;
v_isShared_1142_ = v_isSharedCheck_1148_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_diag_1139_);
lean_inc(v_postponed_1138_);
lean_inc(v_zetaDeltaFVarIds_1137_);
lean_inc(v_cache_1136_);
lean_dec(v___x_1135_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1148_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v_snd_1134_);
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_snd_1134_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_cache_1136_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_zetaDeltaFVarIds_1137_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_postponed_1138_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_diag_1139_);
v___x_1144_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_st_ref_set(v___y_1126_, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_fst_1133_);
return v___x_1146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg___boxed(lean_object* v_e_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1150_, v___y_1151_);
lean_dec(v___y_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(lean_object* v_e_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1154_, v___y_1156_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___boxed(lean_object* v_e_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(v_e_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(lean_object* v_x_1168_, lean_object* v_motiveBody_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Meta_getLevel(v_motiveBody_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0___boxed(lean_object* v_x_1176_, lean_object* v_motiveBody_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(v_x_1176_, v_motiveBody_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec_ref(v_x_1176_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(lean_object* v___x_1184_, lean_object* v___x_1185_, lean_object* v_alpha_1186_, uint8_t v___x_1187_, lean_object* v_xs_1188_, lean_object* v_x_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; uint8_t v___x_1199_; uint8_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1195_ = l_Lean_Level_ofNat(v___x_1184_);
v___x_1196_ = l_Lean_Expr_sort___override(v___x_1195_);
v___x_1197_ = l_Lean_Expr_forallE___override(v___x_1185_, v_alpha_1186_, v___x_1196_, v___x_1187_);
v___x_1198_ = 0;
v___x_1199_ = 1;
v___x_1200_ = 1;
v___x_1201_ = l_Lean_Meta_mkForallFVars(v_xs_1188_, v___x_1197_, v___x_1198_, v___x_1199_, v___x_1199_, v___x_1200_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed(lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v_alpha_1204_, lean_object* v___x_1205_, lean_object* v_xs_1206_, lean_object* v_x_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
uint8_t v___x_16360__boxed_1213_; lean_object* v_res_1214_; 
v___x_16360__boxed_1213_ = lean_unbox(v___x_1205_);
v_res_1214_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(v___x_1202_, v___x_1203_, v_alpha_1204_, v___x_16360__boxed_1213_, v_xs_1206_, v_x_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec_ref(v_x_1207_);
lean_dec_ref(v_xs_1206_);
lean_dec(v___x_1202_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(lean_object* v___x_1221_, lean_object* v___x_1222_, lean_object* v_rel_1223_, lean_object* v___x_1224_, lean_object* v_beta_1225_, uint8_t v___x_1226_, lean_object* v_alpha_1227_, uint8_t v___x_1228_, lean_object* v_xs_1229_, lean_object* v_x_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1236_ = l_Lean_mkAppN(v___x_1221_, v_xs_1229_);
v___x_1237_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1238_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_xs_1229_);
v___x_1239_ = lean_array_push(v_xs_1229_, v___x_1222_);
v___x_1240_ = l_Lean_mkAppN(v_rel_1223_, v___x_1239_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = l_Lean_Expr_bvar___override(v___x_1224_);
v___x_1242_ = l_Lean_Expr_app___override(v_beta_1225_, v___x_1241_);
v___x_1243_ = l_Lean_Expr_forallE___override(v___x_1238_, v___x_1240_, v___x_1242_, v___x_1226_);
v___x_1244_ = l_Lean_Expr_forallE___override(v___x_1237_, v_alpha_1227_, v___x_1243_, v___x_1226_);
v___x_1245_ = l_Lean_mkArrow(v___x_1244_, v___x_1236_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; uint8_t v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = 1;
v___x_1248_ = 1;
v___x_1249_ = l_Lean_Meta_mkLambdaFVars(v_xs_1229_, v_a_1246_, v___x_1228_, v___x_1247_, v___x_1228_, v___x_1247_, v___x_1248_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec_ref(v_xs_1229_);
return v___x_1249_;
}
else
{
lean_dec_ref(v_xs_1229_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed(lean_object* v___x_1250_, lean_object* v___x_1251_, lean_object* v_rel_1252_, lean_object* v___x_1253_, lean_object* v_beta_1254_, lean_object* v___x_1255_, lean_object* v_alpha_1256_, lean_object* v___x_1257_, lean_object* v_xs_1258_, lean_object* v_x_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v___x_16414__boxed_1265_; uint8_t v___x_16415__boxed_1266_; lean_object* v_res_1267_; 
v___x_16414__boxed_1265_ = lean_unbox(v___x_1255_);
v___x_16415__boxed_1266_ = lean_unbox(v___x_1257_);
v_res_1267_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(v___x_1250_, v___x_1251_, v_rel_1252_, v___x_1253_, v_beta_1254_, v___x_16414__boxed_1265_, v_alpha_1256_, v___x_16415__boxed_1266_, v_xs_1258_, v_x_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec_ref(v_x_1259_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(lean_object* v___x_1268_, lean_object* v___x_1269_, lean_object* v_f_1270_, uint8_t v___x_1271_, uint8_t v___x_1272_, lean_object* v_ys_1273_, lean_object* v_x_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1280_ = lean_array_get_borrowed(v___x_1268_, v_ys_1273_, v___x_1269_);
lean_inc(v___x_1280_);
v___x_1281_ = l_Lean_Expr_app___override(v_f_1270_, v___x_1280_);
v___x_1282_ = 1;
v___x_1283_ = l_Lean_Meta_mkLambdaFVars(v_ys_1273_, v___x_1281_, v___x_1271_, v___x_1272_, v___x_1271_, v___x_1272_, v___x_1282_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed(lean_object* v___x_1284_, lean_object* v___x_1285_, lean_object* v_f_1286_, lean_object* v___x_1287_, lean_object* v___x_1288_, lean_object* v_ys_1289_, lean_object* v_x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
uint8_t v___x_16481__boxed_1296_; uint8_t v___x_16482__boxed_1297_; lean_object* v_res_1298_; 
v___x_16481__boxed_1296_ = lean_unbox(v___x_1287_);
v___x_16482__boxed_1297_ = lean_unbox(v___x_1288_);
v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(v___x_1284_, v___x_1285_, v_f_1286_, v___x_16481__boxed_1296_, v___x_16482__boxed_1297_, v_ys_1289_, v_x_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec_ref(v_x_1290_);
lean_dec_ref(v_ys_1289_);
lean_dec(v___x_1285_);
lean_dec_ref(v___x_1284_);
return v_res_1298_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1));
v___x_1302_ = lean_unsigned_to_nat(10u);
v___x_1303_ = lean_unsigned_to_nat(145u);
v___x_1304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0));
v___x_1305_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_1306_ = l_mkPanicMessageWithDecl(v___x_1305_, v___x_1304_, v___x_1303_, v___x_1302_, v___x_1301_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(lean_object* v___x_1307_, lean_object* v___x_1308_, lean_object* v_f_1309_, uint8_t v___x_1310_, lean_object* v_a_1311_, lean_object* v_ys_1312_, lean_object* v_altBodyType_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_Expr_isForall(v_altBodyType_1313_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec_ref(v_ys_1312_);
lean_dec_ref(v_a_1311_);
lean_dec_ref(v_f_1309_);
lean_dec(v___x_1308_);
lean_dec_ref(v___x_1307_);
v___x_1320_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2);
v___x_1321_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v___x_1320_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___f_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1322_ = lean_box(v___x_1310_);
v___x_1323_ = lean_box(v___x_1319_);
v___f_1324_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1324_, 0, v___x_1307_);
lean_closure_set(v___f_1324_, 1, v___x_1308_);
lean_closure_set(v___f_1324_, 2, v_f_1309_);
lean_closure_set(v___f_1324_, 3, v___x_1322_);
lean_closure_set(v___f_1324_, 4, v___x_1323_);
v___x_1325_ = l_Lean_Expr_bindingDomain_x21(v_altBodyType_1313_);
v___x_1326_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_1327_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_1325_, v___x_1326_, v___f_1324_, v___x_1310_, v___x_1310_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref(v___x_1327_);
lean_inc_ref(v_ys_1312_);
v___x_1329_ = lean_array_push(v_ys_1312_, v_a_1328_);
v___x_1330_ = l_Lean_mkAppN(v_a_1311_, v___x_1329_);
lean_dec_ref(v___x_1329_);
v___x_1331_ = 1;
v___x_1332_ = l_Lean_Meta_mkLambdaFVars(v_ys_1312_, v___x_1330_, v___x_1310_, v___x_1319_, v___x_1310_, v___x_1319_, v___x_1331_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec_ref(v_ys_1312_);
return v___x_1332_;
}
else
{
lean_dec_ref(v_ys_1312_);
lean_dec_ref(v_a_1311_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed(lean_object* v___x_1333_, lean_object* v___x_1334_, lean_object* v_f_1335_, lean_object* v___x_1336_, lean_object* v_a_1337_, lean_object* v_ys_1338_, lean_object* v_altBodyType_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
uint8_t v___x_16538__boxed_1345_; lean_object* v_res_1346_; 
v___x_16538__boxed_1345_ = lean_unbox(v___x_1336_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(v___x_1333_, v___x_1334_, v_f_1335_, v___x_16538__boxed_1345_, v_a_1337_, v_ys_1338_, v_altBodyType_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v_altBodyType_1339_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(lean_object* v_f_1347_, lean_object* v_as_1348_, size_t v_sz_1349_, size_t v_i_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_usize_dec_lt(v_i_1350_, v_sz_1349_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec_ref(v_f_1347_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_b_1351_);
return v___x_1358_;
}
else
{
lean_object* v_snd_1359_; lean_object* v_fst_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1419_; 
v_snd_1359_ = lean_ctor_get(v_b_1351_, 1);
v_fst_1360_ = lean_ctor_get(v_b_1351_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_b_1351_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1362_ = v_b_1351_;
v_isShared_1363_ = v_isSharedCheck_1419_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_snd_1359_);
lean_inc(v_fst_1360_);
lean_dec(v_b_1351_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1419_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_array_1364_; lean_object* v_start_1365_; lean_object* v_stop_1366_; uint8_t v___x_1367_; 
v_array_1364_ = lean_ctor_get(v_snd_1359_, 0);
v_start_1365_ = lean_ctor_get(v_snd_1359_, 1);
v_stop_1366_ = lean_ctor_get(v_snd_1359_, 2);
v___x_1367_ = lean_nat_dec_lt(v_start_1365_, v_stop_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1369_; 
lean_dec_ref(v_f_1347_);
if (v_isShared_1363_ == 0)
{
v___x_1369_ = v___x_1362_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_fst_1360_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_snd_1359_);
v___x_1369_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
}
else
{
lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1415_; 
lean_inc(v_stop_1366_);
lean_inc(v_start_1365_);
lean_inc_ref(v_array_1364_);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_snd_1359_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; lean_object* v_unused_1417_; lean_object* v_unused_1418_; 
v_unused_1416_ = lean_ctor_get(v_snd_1359_, 2);
lean_dec(v_unused_1416_);
v_unused_1417_ = lean_ctor_get(v_snd_1359_, 1);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v_snd_1359_, 0);
lean_dec(v_unused_1418_);
v___x_1373_ = v_snd_1359_;
v_isShared_1374_ = v_isSharedCheck_1415_;
goto v_resetjp_1372_;
}
else
{
lean_dec(v_snd_1359_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1415_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_a_1375_; lean_object* v___x_1376_; 
v_a_1375_ = lean_array_uget_borrowed(v_as_1348_, v_i_1350_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v_a_1375_);
v___x_1376_ = lean_infer_type(v_a_1375_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___f_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = l_Lean_instInhabitedExpr;
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = 0;
v___x_1381_ = lean_box(v___x_1380_);
lean_inc(v_a_1375_);
lean_inc_ref(v_f_1347_);
v___f_1382_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed), 12, 5);
lean_closure_set(v___f_1382_, 0, v___x_1378_);
lean_closure_set(v___f_1382_, 1, v___x_1379_);
lean_closure_set(v___f_1382_, 2, v_f_1347_);
lean_closure_set(v___f_1382_, 3, v___x_1381_);
lean_closure_set(v___f_1382_, 4, v_a_1375_);
v___x_1383_ = lean_array_fget_borrowed(v_array_1364_, v_start_1365_);
lean_inc(v___x_1383_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
v___x_1385_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1377_, v___x_1384_, v___f_1382_, v___x_1380_, v___x_1380_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1390_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = lean_unsigned_to_nat(1u);
v___x_1388_ = lean_nat_add(v_start_1365_, v___x_1387_);
lean_dec(v_start_1365_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v___x_1388_);
v___x_1390_ = v___x_1373_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_array_1364_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_stop_1366_);
v___x_1390_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = l_Lean_Expr_app___override(v_fst_1360_, v_a_1386_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v___x_1390_);
lean_ctor_set(v___x_1362_, 0, v___x_1391_);
v___x_1393_ = v___x_1362_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1390_);
v___x_1393_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
size_t v___x_1394_; size_t v___x_1395_; 
v___x_1394_ = ((size_t)1ULL);
v___x_1395_ = lean_usize_add(v_i_1350_, v___x_1394_);
v_i_1350_ = v___x_1395_;
v_b_1351_ = v___x_1393_;
goto _start;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_del_object(v___x_1373_);
lean_dec(v_stop_1366_);
lean_dec(v_start_1365_);
lean_dec_ref(v_array_1364_);
lean_del_object(v___x_1362_);
lean_dec(v_fst_1360_);
lean_dec_ref(v_f_1347_);
v_a_1399_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1385_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1385_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_del_object(v___x_1373_);
lean_dec(v_stop_1366_);
lean_dec(v_start_1365_);
lean_dec_ref(v_array_1364_);
lean_del_object(v___x_1362_);
lean_dec(v_fst_1360_);
lean_dec_ref(v_f_1347_);
v_a_1407_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1376_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1376_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___boxed(lean_object* v_f_1420_, lean_object* v_as_1421_, lean_object* v_sz_1422_, lean_object* v_i_1423_, lean_object* v_b_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
size_t v_sz_boxed_1430_; size_t v_i_boxed_1431_; lean_object* v_res_1432_; 
v_sz_boxed_1430_ = lean_unbox_usize(v_sz_1422_);
lean_dec(v_sz_1422_);
v_i_boxed_1431_ = lean_unbox_usize(v_i_1423_);
lean_dec(v_i_1423_);
v_res_1432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1420_, v_as_1421_, v_sz_boxed_1430_, v_i_boxed_1431_, v_b_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec_ref(v_as_1421_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(lean_object* v_as_x27_1433_, lean_object* v_b_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
if (lean_obj_tag(v_as_x27_1433_) == 0)
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_b_1434_);
return v___x_1440_;
}
else
{
lean_object* v_head_1441_; lean_object* v_tail_1442_; uint8_t v___x_1443_; lean_object* v___x_1444_; 
v_head_1441_ = lean_ctor_get(v_as_x27_1433_, 0);
lean_inc(v_head_1441_);
v_tail_1442_ = lean_ctor_get(v_as_x27_1433_, 1);
lean_inc(v_tail_1442_);
lean_dec_ref(v_as_x27_1433_);
v___x_1443_ = 1;
v___x_1444_ = l_Lean_MVarId_refl(v_head_1441_, v___x_1443_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v___x_1445_; 
lean_dec_ref(v___x_1444_);
v___x_1445_ = lean_box(0);
v_as_x27_1433_ = v_tail_1442_;
v_b_1434_ = v___x_1445_;
goto _start;
}
else
{
lean_dec(v_tail_1442_);
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg___boxed(lean_object* v_as_x27_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_1447_, v_b_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(lean_object* v___x_1455_, lean_object* v_matcherInfo_1456_, lean_object* v___x_1457_, lean_object* v___x_1458_, lean_object* v_f_1459_, lean_object* v_discrs_1460_, lean_object* v___x_1461_, lean_object* v_rel_1462_, lean_object* v___x_1463_, uint8_t v___x_1464_, lean_object* v_alpha_1465_, lean_object* v___x_1466_, lean_object* v_beta_1467_, lean_object* v___x_1468_, uint8_t v___x_1469_, lean_object* v___x_1470_, lean_object* v___x_1471_, lean_object* v___x_1472_, lean_object* v_alts_1473_, lean_object* v_x_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; size_t v_sz_1485_; size_t v___x_1486_; lean_object* v___x_1487_; 
v___x_1480_ = l_Lean_mkAppN(v___x_1455_, v_alts_1473_);
lean_inc_ref(v_matcherInfo_1456_);
v___x_1481_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_matcherInfo_1456_);
v___x_1482_ = lean_array_get_size(v___x_1481_);
v___x_1483_ = l_Array_toSubarray___redArg(v___x_1481_, v___x_1457_, v___x_1482_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1458_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v_sz_1485_ = lean_array_size(v_alts_1473_);
v___x_1486_ = ((size_t)0ULL);
lean_inc_ref(v_f_1459_);
v___x_1487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1459_, v_alts_1473_, v_sz_1485_, v___x_1486_, v___x_1484_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v_fst_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1583_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref(v___x_1487_);
v_fst_1489_ = lean_ctor_get(v_a_1488_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_a_1488_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v_a_1488_, 1);
lean_dec(v_unused_1584_);
v___x_1491_ = v_a_1488_;
v_isShared_1492_ = v_isSharedCheck_1583_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_fst_1489_);
lean_dec(v_a_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1583_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1493_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1494_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_discrs_1460_);
v___x_1495_ = lean_array_push(v_discrs_1460_, v___x_1461_);
lean_inc_ref(v_rel_1462_);
v___x_1496_ = l_Lean_mkAppN(v_rel_1462_, v___x_1495_);
lean_dec_ref(v___x_1495_);
v___x_1497_ = l_Lean_Expr_bvar___override(v___x_1463_);
lean_inc_ref(v_f_1459_);
v___x_1498_ = l_Lean_Expr_app___override(v_f_1459_, v___x_1497_);
v___x_1499_ = l_Lean_Expr_lam___override(v___x_1494_, v___x_1496_, v___x_1498_, v___x_1464_);
lean_inc_ref(v_alpha_1465_);
v___x_1500_ = l_Lean_Expr_lam___override(v___x_1493_, v_alpha_1465_, v___x_1499_, v___x_1464_);
v___x_1501_ = l_Lean_Expr_app___override(v___x_1480_, v___x_1500_);
lean_inc(v_fst_1489_);
v___x_1502_ = l_Lean_Meta_mkEq(v___x_1501_, v_fst_1489_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc_n(v_a_1503_, 2);
lean_dec_ref(v___x_1502_);
v___x_1504_ = lean_box(0);
v___x_1505_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1503_, v___x_1504_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref(v___x_1505_);
v___x_1507_ = l_Lean_Expr_mvarId_x21(v_a_1506_);
v___x_1508_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v___x_1507_, v_fst_1489_, v_matcherInfo_1456_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec_ref(v_matcherInfo_1456_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref(v___x_1508_);
v___x_1510_ = lean_box(0);
v___x_1511_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_a_1509_, v___x_1510_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v___x_1512_; lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v___x_1511_);
v___x_1512_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_1506_, v___y_1476_);
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1558_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1558_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1517_ = lean_unsigned_to_nat(5u);
v___x_1518_ = lean_mk_empty_array_with_capacity(v___x_1517_);
v___x_1519_ = lean_array_push(v___x_1518_, v___x_1466_);
v___x_1520_ = lean_array_push(v___x_1519_, v_alpha_1465_);
v___x_1521_ = lean_array_push(v___x_1520_, v_beta_1467_);
v___x_1522_ = lean_array_push(v___x_1521_, v_f_1459_);
v___x_1523_ = lean_array_push(v___x_1522_, v_rel_1462_);
v___x_1524_ = l_Array_append___redArg(v___x_1468_, v___x_1523_);
lean_dec_ref(v___x_1523_);
v___x_1525_ = l_Array_append___redArg(v___x_1524_, v_discrs_1460_);
lean_dec_ref(v_discrs_1460_);
v___x_1526_ = l_Array_append___redArg(v___x_1525_, v_alts_1473_);
v___x_1527_ = 1;
v___x_1528_ = 1;
v___x_1529_ = l_Lean_Meta_mkForallFVars(v___x_1526_, v_a_1503_, v___x_1469_, v___x_1527_, v___x_1527_, v___x_1528_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v___x_1531_ = l_Lean_Meta_mkLambdaFVars(v___x_1526_, v_a_1513_, v___x_1469_, v___x_1527_, v___x_1469_, v___x_1527_, v___x_1528_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec_ref(v___x_1526_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref(v___x_1531_);
lean_inc(v___x_1470_);
v___x_1533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1470_);
lean_ctor_set(v___x_1533_, 1, v___x_1471_);
lean_ctor_set(v___x_1533_, 2, v_a_1530_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set_tag(v___x_1491_, 1);
lean_ctor_set(v___x_1491_, 1, v___x_1472_);
lean_ctor_set(v___x_1491_, 0, v___x_1470_);
v___x_1535_ = v___x_1491_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___x_1472_);
v___x_1535_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1533_);
lean_ctor_set(v___x_1536_, 1, v_a_1532_);
lean_ctor_set(v___x_1536_, 2, v___x_1535_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set_tag(v___x_1515_, 2);
lean_ctor_set(v___x_1515_, 0, v___x_1536_);
v___x_1538_ = v___x_1515_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_addDecl(v___x_1538_, v___x_1469_, v___y_1477_, v___y_1478_);
return v___x_1539_;
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec(v_a_1530_);
lean_del_object(v___x_1515_);
lean_del_object(v___x_1491_);
lean_dec(v___x_1472_);
lean_dec(v___x_1471_);
lean_dec(v___x_1470_);
v_a_1542_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1531_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1531_);
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
lean_dec_ref(v___x_1526_);
lean_del_object(v___x_1515_);
lean_dec(v_a_1513_);
lean_del_object(v___x_1491_);
lean_dec(v___x_1472_);
lean_dec(v___x_1471_);
lean_dec(v___x_1470_);
v_a_1550_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1529_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1529_);
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
}
else
{
lean_dec(v_a_1506_);
lean_dec(v_a_1503_);
lean_del_object(v___x_1491_);
lean_dec(v___x_1472_);
lean_dec(v___x_1471_);
lean_dec(v___x_1470_);
lean_dec_ref(v___x_1468_);
lean_dec_ref(v_beta_1467_);
lean_dec_ref(v___x_1466_);
lean_dec_ref(v_alpha_1465_);
lean_dec_ref(v_rel_1462_);
lean_dec_ref(v_discrs_1460_);
lean_dec_ref(v_f_1459_);
return v___x_1511_;
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_a_1506_);
lean_dec(v_a_1503_);
lean_del_object(v___x_1491_);
lean_dec(v___x_1472_);
lean_dec(v___x_1471_);
lean_dec(v___x_1470_);
lean_dec_ref(v___x_1468_);
lean_dec_ref(v_beta_1467_);
lean_dec_ref(v___x_1466_);
lean_dec_ref(v_alpha_1465_);
lean_dec_ref(v_rel_1462_);
lean_dec_ref(v_discrs_1460_);
lean_dec_ref(v_f_1459_);
v_a_1559_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1508_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1508_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1503_);
lean_del_object(v___x_1491_);
lean_dec(v_fst_1489_);
lean_dec(v___x_1472_);
lean_dec(v___x_1471_);
lean_dec(v___x_1470_);
lean_dec_ref(v___x_1468_);
lean_dec_ref(v_beta_1467_);
lean_dec_ref(v___x_1466_);
lean_dec_ref(v_alpha_1465_);
lean_dec_ref(v_rel_1462_);
lean_dec_ref(v_discrs_1460_);
lean_dec_ref(v_f_1459_);
lean_dec_ref(v_matcherInfo_1456_);
v_a_1567_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1505_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1505_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_del_object(v___x_1491_);
lean_dec(v_fst_1489_);
lean_dec(v___x_1472_);
lean_dec(v___x_1471_);
lean_dec(v___x_1470_);
lean_dec_ref(v___x_1468_);
lean_dec_ref(v_beta_1467_);
lean_dec_ref(v___x_1466_);
lean_dec_ref(v_alpha_1465_);
lean_dec_ref(v_rel_1462_);
lean_dec_ref(v_discrs_1460_);
lean_dec_ref(v_f_1459_);
lean_dec_ref(v_matcherInfo_1456_);
v_a_1575_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1502_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1502_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v___x_1480_);
lean_dec(v___x_1472_);
lean_dec(v___x_1471_);
lean_dec(v___x_1470_);
lean_dec_ref(v___x_1468_);
lean_dec_ref(v_beta_1467_);
lean_dec_ref(v___x_1466_);
lean_dec_ref(v_alpha_1465_);
lean_dec(v___x_1463_);
lean_dec_ref(v_rel_1462_);
lean_dec_ref(v___x_1461_);
lean_dec_ref(v_discrs_1460_);
lean_dec_ref(v_f_1459_);
lean_dec_ref(v_matcherInfo_1456_);
v_a_1585_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1487_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1487_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed(lean_object** _args){
lean_object* v___x_1593_ = _args[0];
lean_object* v_matcherInfo_1594_ = _args[1];
lean_object* v___x_1595_ = _args[2];
lean_object* v___x_1596_ = _args[3];
lean_object* v_f_1597_ = _args[4];
lean_object* v_discrs_1598_ = _args[5];
lean_object* v___x_1599_ = _args[6];
lean_object* v_rel_1600_ = _args[7];
lean_object* v___x_1601_ = _args[8];
lean_object* v___x_1602_ = _args[9];
lean_object* v_alpha_1603_ = _args[10];
lean_object* v___x_1604_ = _args[11];
lean_object* v_beta_1605_ = _args[12];
lean_object* v___x_1606_ = _args[13];
lean_object* v___x_1607_ = _args[14];
lean_object* v___x_1608_ = _args[15];
lean_object* v___x_1609_ = _args[16];
lean_object* v___x_1610_ = _args[17];
lean_object* v_alts_1611_ = _args[18];
lean_object* v_x_1612_ = _args[19];
lean_object* v___y_1613_ = _args[20];
lean_object* v___y_1614_ = _args[21];
lean_object* v___y_1615_ = _args[22];
lean_object* v___y_1616_ = _args[23];
lean_object* v___y_1617_ = _args[24];
_start:
{
uint8_t v___x_16768__boxed_1618_; uint8_t v___x_16771__boxed_1619_; lean_object* v_res_1620_; 
v___x_16768__boxed_1618_ = lean_unbox(v___x_1602_);
v___x_16771__boxed_1619_ = lean_unbox(v___x_1607_);
v_res_1620_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(v___x_1593_, v_matcherInfo_1594_, v___x_1595_, v___x_1596_, v_f_1597_, v_discrs_1598_, v___x_1599_, v_rel_1600_, v___x_1601_, v___x_16768__boxed_1618_, v_alpha_1603_, v___x_1604_, v_beta_1605_, v___x_1606_, v___x_16771__boxed_1619_, v___x_1608_, v___x_1609_, v___x_1610_, v_alts_1611_, v_x_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec_ref(v_x_1612_);
lean_dec_ref(v_alts_1611_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(lean_object* v___x_1621_, lean_object* v___x_1622_, lean_object* v_matcherInfo_1623_, lean_object* v___x_1624_, lean_object* v_f_1625_, lean_object* v___x_1626_, lean_object* v_rel_1627_, lean_object* v___x_1628_, uint8_t v___x_1629_, lean_object* v_alpha_1630_, lean_object* v___x_1631_, lean_object* v_beta_1632_, lean_object* v___x_1633_, uint8_t v___x_1634_, lean_object* v___x_1635_, lean_object* v___x_1636_, lean_object* v___x_1637_, lean_object* v_discrs_1638_, lean_object* v_x_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = l_Lean_mkAppN(v___x_1621_, v_discrs_1638_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
lean_inc_ref(v___x_1645_);
v___x_1646_ = lean_infer_type(v___x_1645_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___f_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref(v___x_1646_);
v___x_1648_ = l_Lean_mkAppN(v___x_1622_, v_discrs_1638_);
v___x_1649_ = lean_box(v___x_1629_);
v___x_1650_ = lean_box(v___x_1634_);
lean_inc_ref(v_matcherInfo_1623_);
v___f_1651_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1651_, 0, v___x_1645_);
lean_closure_set(v___f_1651_, 1, v_matcherInfo_1623_);
lean_closure_set(v___f_1651_, 2, v___x_1624_);
lean_closure_set(v___f_1651_, 3, v___x_1648_);
lean_closure_set(v___f_1651_, 4, v_f_1625_);
lean_closure_set(v___f_1651_, 5, v_discrs_1638_);
lean_closure_set(v___f_1651_, 6, v___x_1626_);
lean_closure_set(v___f_1651_, 7, v_rel_1627_);
lean_closure_set(v___f_1651_, 8, v___x_1628_);
lean_closure_set(v___f_1651_, 9, v___x_1649_);
lean_closure_set(v___f_1651_, 10, v_alpha_1630_);
lean_closure_set(v___f_1651_, 11, v___x_1631_);
lean_closure_set(v___f_1651_, 12, v_beta_1632_);
lean_closure_set(v___f_1651_, 13, v___x_1633_);
lean_closure_set(v___f_1651_, 14, v___x_1650_);
lean_closure_set(v___f_1651_, 15, v___x_1635_);
lean_closure_set(v___f_1651_, 16, v___x_1636_);
lean_closure_set(v___f_1651_, 17, v___x_1637_);
v___x_1652_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_matcherInfo_1623_);
lean_dec_ref(v_matcherInfo_1623_);
v___x_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
v___x_1654_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1647_, v___x_1653_, v___f_1651_, v___x_1634_, v___x_1634_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v___x_1654_;
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec_ref(v___x_1645_);
lean_dec_ref(v_discrs_1638_);
lean_dec(v___x_1637_);
lean_dec(v___x_1636_);
lean_dec(v___x_1635_);
lean_dec_ref(v___x_1633_);
lean_dec_ref(v_beta_1632_);
lean_dec_ref(v___x_1631_);
lean_dec_ref(v_alpha_1630_);
lean_dec(v___x_1628_);
lean_dec_ref(v_rel_1627_);
lean_dec_ref(v___x_1626_);
lean_dec_ref(v_f_1625_);
lean_dec(v___x_1624_);
lean_dec_ref(v_matcherInfo_1623_);
lean_dec_ref(v___x_1622_);
v_a_1655_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1646_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1646_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed(lean_object** _args){
lean_object* v___x_1663_ = _args[0];
lean_object* v___x_1664_ = _args[1];
lean_object* v_matcherInfo_1665_ = _args[2];
lean_object* v___x_1666_ = _args[3];
lean_object* v_f_1667_ = _args[4];
lean_object* v___x_1668_ = _args[5];
lean_object* v_rel_1669_ = _args[6];
lean_object* v___x_1670_ = _args[7];
lean_object* v___x_1671_ = _args[8];
lean_object* v_alpha_1672_ = _args[9];
lean_object* v___x_1673_ = _args[10];
lean_object* v_beta_1674_ = _args[11];
lean_object* v___x_1675_ = _args[12];
lean_object* v___x_1676_ = _args[13];
lean_object* v___x_1677_ = _args[14];
lean_object* v___x_1678_ = _args[15];
lean_object* v___x_1679_ = _args[16];
lean_object* v_discrs_1680_ = _args[17];
lean_object* v_x_1681_ = _args[18];
lean_object* v___y_1682_ = _args[19];
lean_object* v___y_1683_ = _args[20];
lean_object* v___y_1684_ = _args[21];
lean_object* v___y_1685_ = _args[22];
lean_object* v___y_1686_ = _args[23];
_start:
{
uint8_t v___x_17049__boxed_1687_; uint8_t v___x_17052__boxed_1688_; lean_object* v_res_1689_; 
v___x_17049__boxed_1687_ = lean_unbox(v___x_1671_);
v___x_17052__boxed_1688_ = lean_unbox(v___x_1676_);
v_res_1689_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(v___x_1663_, v___x_1664_, v_matcherInfo_1665_, v___x_1666_, v_f_1667_, v___x_1668_, v_rel_1669_, v___x_1670_, v___x_17049__boxed_1687_, v_alpha_1672_, v___x_1673_, v_beta_1674_, v___x_1675_, v___x_17052__boxed_1688_, v___x_1677_, v___x_1678_, v___x_1679_, v_discrs_1680_, v_x_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v_x_1681_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
if (lean_obj_tag(v_a_1690_) == 0)
{
lean_object* v___x_1692_; 
v___x_1692_ = l_List_reverse___redArg(v_a_1691_);
return v___x_1692_;
}
else
{
lean_object* v_head_1693_; lean_object* v_tail_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1703_; 
v_head_1693_ = lean_ctor_get(v_a_1690_, 0);
v_tail_1694_ = lean_ctor_get(v_a_1690_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_a_1690_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1696_ = v_a_1690_;
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_tail_1694_);
lean_inc(v_head_1693_);
lean_dec(v_a_1690_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = l_Lean_mkLevelParam(v_head_1693_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 1, v_a_1691_);
lean_ctor_set(v___x_1696_, 0, v___x_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_a_1691_);
v___x_1700_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
v_a_1690_ = v_tail_1694_;
v_a_1691_ = v___x_1700_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__0));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__2));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(lean_object* v___x_1710_, lean_object* v___x_1711_, lean_object* v___x_1712_, lean_object* v_beta_1713_, uint8_t v___x_1714_, lean_object* v_alpha_1715_, uint8_t v___x_1716_, lean_object* v_numDiscrs_1717_, lean_object* v___f_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_levelParams_1721_, lean_object* v_matcherName_1722_, lean_object* v___x_1723_, lean_object* v_matcherInfo_1724_, lean_object* v___x_1725_, lean_object* v_f_1726_, lean_object* v___x_1727_, lean_object* v_uElimPos_x3f_1728_, lean_object* v_rel_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; 
lean_inc(v___y_1733_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1731_);
lean_inc_ref(v___y_1730_);
lean_inc_ref(v___x_1710_);
v___x_1735_ = lean_infer_type(v___x_1710_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = lean_box(v___x_1714_);
v___x_1738_ = lean_box(v___x_1716_);
lean_inc_ref(v_alpha_1715_);
lean_inc_ref(v_beta_1713_);
lean_inc(v___x_1712_);
lean_inc_ref(v_rel_1729_);
lean_inc_ref(v___x_1711_);
lean_inc_ref(v___x_1710_);
v___f_1739_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed), 15, 8);
lean_closure_set(v___f_1739_, 0, v___x_1710_);
lean_closure_set(v___f_1739_, 1, v___x_1711_);
lean_closure_set(v___f_1739_, 2, v_rel_1729_);
lean_closure_set(v___f_1739_, 3, v___x_1712_);
lean_closure_set(v___f_1739_, 4, v_beta_1713_);
lean_closure_set(v___f_1739_, 5, v___x_1737_);
lean_closure_set(v___f_1739_, 6, v_alpha_1715_);
lean_closure_set(v___f_1739_, 7, v___x_1738_);
v___x_1740_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1736_, v___f_1739_, v___x_1716_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1742_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc_n(v_a_1741_, 2);
lean_dec_ref(v___x_1740_);
lean_inc(v_numDiscrs_1717_);
v___x_1742_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_a_1741_, v_numDiscrs_1717_, v___f_1718_, v___x_1716_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v_matcherLevels_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref(v___x_1742_);
v___x_1744_ = lean_box(0);
v___x_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1745_, 0, v_a_1719_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_a_1720_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
lean_inc(v_levelParams_1721_);
v___x_1747_ = l_List_appendTR___redArg(v_levelParams_1721_, v___x_1746_);
v___x_1748_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_1721_, v___x_1744_);
if (lean_obj_tag(v_uElimPos_x3f_1728_) == 0)
{
uint8_t v___x_1777_; 
v___x_1777_ = l_Lean_Level_isZero(v_a_1743_);
lean_dec(v_a_1743_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v___x_1748_);
lean_dec(v___x_1747_);
lean_dec(v_a_1741_);
lean_dec_ref(v_rel_1729_);
lean_dec(v___x_1727_);
lean_dec_ref(v_f_1726_);
lean_dec(v___x_1725_);
lean_dec_ref(v_matcherInfo_1724_);
lean_dec_ref(v___x_1723_);
lean_dec(v_numDiscrs_1717_);
lean_dec_ref(v_alpha_1715_);
lean_dec_ref(v_beta_1713_);
lean_dec(v___x_1712_);
lean_dec_ref(v___x_1711_);
lean_dec_ref(v___x_1710_);
v___x_1778_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1);
v___x_1779_ = l_Lean_MessageData_ofConstName(v_matcherName_1722_, v___x_1716_);
v___x_1780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_1782_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
return v___x_1783_;
}
else
{
lean_inc(v___x_1748_);
v_matcherLevels_1750_ = v___x_1748_;
v___y_1751_ = v___y_1730_;
v___y_1752_ = v___y_1731_;
v___y_1753_ = v___y_1732_;
v___y_1754_ = v___y_1733_;
goto v___jp_1749_;
}
}
else
{
lean_object* v_val_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_val_1784_ = lean_ctor_get(v_uElimPos_x3f_1728_, 0);
lean_inc(v___x_1748_);
v___x_1785_ = lean_array_mk(v___x_1748_);
v___x_1786_ = lean_array_set(v___x_1785_, v_val_1784_, v_a_1743_);
v___x_1787_ = lean_array_to_list(v___x_1786_);
v_matcherLevels_1750_ = v___x_1787_;
v___y_1751_ = v___y_1730_;
v___y_1752_ = v___y_1731_;
v___y_1753_ = v___y_1732_;
v___y_1754_ = v___y_1733_;
goto v___jp_1749_;
}
v___jp_1749_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_inc(v_matcherName_1722_);
v___x_1755_ = l_Lean_Expr_const___override(v_matcherName_1722_, v_matcherLevels_1750_);
v___x_1756_ = l_Subarray_copy___redArg(v___x_1723_);
v___x_1757_ = l_Lean_mkAppN(v___x_1755_, v___x_1756_);
v___x_1758_ = l_Lean_Expr_app___override(v___x_1757_, v_a_1741_);
lean_inc(v___y_1754_);
lean_inc_ref(v___y_1753_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
lean_inc_ref(v___x_1758_);
v___x_1759_ = lean_infer_type(v___x_1758_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___f_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref(v___x_1759_);
v___x_1761_ = l_Lean_Expr_const___override(v_matcherName_1722_, v___x_1748_);
v___x_1762_ = l_Lean_mkAppN(v___x_1761_, v___x_1756_);
lean_inc_ref(v___x_1710_);
v___x_1763_ = l_Lean_Expr_app___override(v___x_1762_, v___x_1710_);
v___x_1764_ = lean_box(v___x_1714_);
v___x_1765_ = lean_box(v___x_1716_);
v___f_1766_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed), 24, 17);
lean_closure_set(v___f_1766_, 0, v___x_1758_);
lean_closure_set(v___f_1766_, 1, v___x_1763_);
lean_closure_set(v___f_1766_, 2, v_matcherInfo_1724_);
lean_closure_set(v___f_1766_, 3, v___x_1725_);
lean_closure_set(v___f_1766_, 4, v_f_1726_);
lean_closure_set(v___f_1766_, 5, v___x_1711_);
lean_closure_set(v___f_1766_, 6, v_rel_1729_);
lean_closure_set(v___f_1766_, 7, v___x_1712_);
lean_closure_set(v___f_1766_, 8, v___x_1764_);
lean_closure_set(v___f_1766_, 9, v_alpha_1715_);
lean_closure_set(v___f_1766_, 10, v___x_1710_);
lean_closure_set(v___f_1766_, 11, v_beta_1713_);
lean_closure_set(v___f_1766_, 12, v___x_1756_);
lean_closure_set(v___f_1766_, 13, v___x_1765_);
lean_closure_set(v___f_1766_, 14, v___x_1727_);
lean_closure_set(v___f_1766_, 15, v___x_1747_);
lean_closure_set(v___f_1766_, 16, v___x_1744_);
v___x_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_numDiscrs_1717_);
v___x_1768_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1760_, v___x_1767_, v___f_1766_, v___x_1716_, v___x_1716_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1768_;
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v___x_1758_);
lean_dec_ref(v___x_1756_);
lean_dec(v___x_1748_);
lean_dec(v___x_1747_);
lean_dec_ref(v_rel_1729_);
lean_dec(v___x_1727_);
lean_dec_ref(v_f_1726_);
lean_dec(v___x_1725_);
lean_dec_ref(v_matcherInfo_1724_);
lean_dec(v_matcherName_1722_);
lean_dec(v_numDiscrs_1717_);
lean_dec_ref(v_alpha_1715_);
lean_dec_ref(v_beta_1713_);
lean_dec(v___x_1712_);
lean_dec_ref(v___x_1711_);
lean_dec_ref(v___x_1710_);
v_a_1769_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1759_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1759_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_a_1741_);
lean_dec_ref(v_rel_1729_);
lean_dec(v___x_1727_);
lean_dec_ref(v_f_1726_);
lean_dec(v___x_1725_);
lean_dec_ref(v_matcherInfo_1724_);
lean_dec_ref(v___x_1723_);
lean_dec(v_matcherName_1722_);
lean_dec(v_levelParams_1721_);
lean_dec(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec(v_numDiscrs_1717_);
lean_dec_ref(v_alpha_1715_);
lean_dec_ref(v_beta_1713_);
lean_dec(v___x_1712_);
lean_dec_ref(v___x_1711_);
lean_dec_ref(v___x_1710_);
v_a_1788_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1742_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1742_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v_rel_1729_);
lean_dec(v___x_1727_);
lean_dec_ref(v_f_1726_);
lean_dec(v___x_1725_);
lean_dec_ref(v_matcherInfo_1724_);
lean_dec_ref(v___x_1723_);
lean_dec(v_matcherName_1722_);
lean_dec(v_levelParams_1721_);
lean_dec(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v___f_1718_);
lean_dec(v_numDiscrs_1717_);
lean_dec_ref(v_alpha_1715_);
lean_dec_ref(v_beta_1713_);
lean_dec(v___x_1712_);
lean_dec_ref(v___x_1711_);
lean_dec_ref(v___x_1710_);
v_a_1796_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1740_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1740_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec_ref(v_rel_1729_);
lean_dec(v___x_1727_);
lean_dec_ref(v_f_1726_);
lean_dec(v___x_1725_);
lean_dec_ref(v_matcherInfo_1724_);
lean_dec_ref(v___x_1723_);
lean_dec(v_matcherName_1722_);
lean_dec(v_levelParams_1721_);
lean_dec(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v___f_1718_);
lean_dec(v_numDiscrs_1717_);
lean_dec_ref(v_alpha_1715_);
lean_dec_ref(v_beta_1713_);
lean_dec(v___x_1712_);
lean_dec_ref(v___x_1711_);
lean_dec_ref(v___x_1710_);
v_a_1804_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1735_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1735_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed(lean_object** _args){
lean_object* v___x_1812_ = _args[0];
lean_object* v___x_1813_ = _args[1];
lean_object* v___x_1814_ = _args[2];
lean_object* v_beta_1815_ = _args[3];
lean_object* v___x_1816_ = _args[4];
lean_object* v_alpha_1817_ = _args[5];
lean_object* v___x_1818_ = _args[6];
lean_object* v_numDiscrs_1819_ = _args[7];
lean_object* v___f_1820_ = _args[8];
lean_object* v_a_1821_ = _args[9];
lean_object* v_a_1822_ = _args[10];
lean_object* v_levelParams_1823_ = _args[11];
lean_object* v_matcherName_1824_ = _args[12];
lean_object* v___x_1825_ = _args[13];
lean_object* v_matcherInfo_1826_ = _args[14];
lean_object* v___x_1827_ = _args[15];
lean_object* v_f_1828_ = _args[16];
lean_object* v___x_1829_ = _args[17];
lean_object* v_uElimPos_x3f_1830_ = _args[18];
lean_object* v_rel_1831_ = _args[19];
lean_object* v___y_1832_ = _args[20];
lean_object* v___y_1833_ = _args[21];
lean_object* v___y_1834_ = _args[22];
lean_object* v___y_1835_ = _args[23];
lean_object* v___y_1836_ = _args[24];
_start:
{
uint8_t v___x_17177__boxed_1837_; uint8_t v___x_17178__boxed_1838_; lean_object* v_res_1839_; 
v___x_17177__boxed_1837_ = lean_unbox(v___x_1816_);
v___x_17178__boxed_1838_ = lean_unbox(v___x_1818_);
v_res_1839_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(v___x_1812_, v___x_1813_, v___x_1814_, v_beta_1815_, v___x_17177__boxed_1837_, v_alpha_1817_, v___x_17178__boxed_1838_, v_numDiscrs_1819_, v___f_1820_, v_a_1821_, v_a_1822_, v_levelParams_1823_, v_matcherName_1824_, v___x_1825_, v_matcherInfo_1826_, v___x_1827_, v_f_1828_, v___x_1829_, v_uElimPos_x3f_1830_, v_rel_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v_uElimPos_x3f_1830_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(lean_object* v_k_1840_, lean_object* v_b_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; 
lean_inc(v___y_1845_);
lean_inc_ref(v___y_1844_);
lean_inc(v___y_1843_);
lean_inc_ref(v___y_1842_);
v___x_1847_ = lean_apply_6(v_k_1840_, v_b_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, lean_box(0));
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v_k_1848_, lean_object* v_b_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(v_k_1848_, v_b_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(lean_object* v_name_1856_, uint8_t v_bi_1857_, lean_object* v_type_1858_, lean_object* v_k_1859_, uint8_t v_kind_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___f_1866_; lean_object* v___x_1867_; 
v___f_1866_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1866_, 0, v_k_1859_);
v___x_1867_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1856_, v_bi_1857_, v_type_1858_, v___f_1866_, v_kind_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
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
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
v_a_1876_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1867_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1867_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___boxed(lean_object* v_name_1884_, lean_object* v_bi_1885_, lean_object* v_type_1886_, lean_object* v_k_1887_, lean_object* v_kind_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
uint8_t v_bi_boxed_1894_; uint8_t v_kind_boxed_1895_; lean_object* v_res_1896_; 
v_bi_boxed_1894_ = lean_unbox(v_bi_1885_);
v_kind_boxed_1895_ = lean_unbox(v_kind_1888_);
v_res_1896_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1884_, v_bi_boxed_1894_, v_type_1886_, v_k_1887_, v_kind_boxed_1895_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(lean_object* v_name_1897_, lean_object* v_type_1898_, lean_object* v_k_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
uint8_t v___x_1905_; uint8_t v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = 0;
v___x_1906_ = 0;
v___x_1907_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1897_, v___x_1905_, v_type_1898_, v_k_1899_, v___x_1906_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg___boxed(lean_object* v_name_1908_, lean_object* v_type_1909_, lean_object* v_k_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_1908_, v_type_1909_, v_k_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(lean_object* v___x_1920_, lean_object* v___f_1921_, lean_object* v___x_1922_, lean_object* v___x_1923_, lean_object* v_beta_1924_, uint8_t v___x_1925_, lean_object* v_alpha_1926_, lean_object* v_numDiscrs_1927_, lean_object* v___f_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_levelParams_1931_, lean_object* v_matcherName_1932_, lean_object* v___x_1933_, lean_object* v_matcherInfo_1934_, lean_object* v___x_1935_, lean_object* v___x_1936_, lean_object* v_uElimPos_x3f_1937_, lean_object* v_f_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
lean_inc_ref(v___x_1920_);
v___x_1944_ = lean_infer_type(v___x_1920_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; uint8_t v___x_1946_; lean_object* v___x_1947_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref(v___x_1944_);
v___x_1946_ = 0;
v___x_1947_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1945_, v___f_1921_, v___x_1946_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___f_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v___x_1949_ = lean_box(v___x_1925_);
v___x_1950_ = lean_box(v___x_1946_);
v___f_1951_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed), 25, 19);
lean_closure_set(v___f_1951_, 0, v___x_1920_);
lean_closure_set(v___f_1951_, 1, v___x_1922_);
lean_closure_set(v___f_1951_, 2, v___x_1923_);
lean_closure_set(v___f_1951_, 3, v_beta_1924_);
lean_closure_set(v___f_1951_, 4, v___x_1949_);
lean_closure_set(v___f_1951_, 5, v_alpha_1926_);
lean_closure_set(v___f_1951_, 6, v___x_1950_);
lean_closure_set(v___f_1951_, 7, v_numDiscrs_1927_);
lean_closure_set(v___f_1951_, 8, v___f_1928_);
lean_closure_set(v___f_1951_, 9, v_a_1929_);
lean_closure_set(v___f_1951_, 10, v_a_1930_);
lean_closure_set(v___f_1951_, 11, v_levelParams_1931_);
lean_closure_set(v___f_1951_, 12, v_matcherName_1932_);
lean_closure_set(v___f_1951_, 13, v___x_1933_);
lean_closure_set(v___f_1951_, 14, v_matcherInfo_1934_);
lean_closure_set(v___f_1951_, 15, v___x_1935_);
lean_closure_set(v___f_1951_, 16, v_f_1938_);
lean_closure_set(v___f_1951_, 17, v___x_1936_);
lean_closure_set(v___f_1951_, 18, v_uElimPos_x3f_1937_);
v___x_1952_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__1));
v___x_1953_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_1952_, v_a_1948_, v___f_1951_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1953_;
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v_f_1938_);
lean_dec(v_uElimPos_x3f_1937_);
lean_dec(v___x_1936_);
lean_dec(v___x_1935_);
lean_dec_ref(v_matcherInfo_1934_);
lean_dec_ref(v___x_1933_);
lean_dec(v_matcherName_1932_);
lean_dec(v_levelParams_1931_);
lean_dec(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v___f_1928_);
lean_dec(v_numDiscrs_1927_);
lean_dec_ref(v_alpha_1926_);
lean_dec_ref(v_beta_1924_);
lean_dec(v___x_1923_);
lean_dec_ref(v___x_1922_);
lean_dec_ref(v___x_1920_);
v_a_1954_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1947_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1947_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v_f_1938_);
lean_dec(v_uElimPos_x3f_1937_);
lean_dec(v___x_1936_);
lean_dec(v___x_1935_);
lean_dec_ref(v_matcherInfo_1934_);
lean_dec_ref(v___x_1933_);
lean_dec(v_matcherName_1932_);
lean_dec(v_levelParams_1931_);
lean_dec(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v___f_1928_);
lean_dec(v_numDiscrs_1927_);
lean_dec_ref(v_alpha_1926_);
lean_dec_ref(v_beta_1924_);
lean_dec(v___x_1923_);
lean_dec_ref(v___x_1922_);
lean_dec_ref(v___f_1921_);
lean_dec_ref(v___x_1920_);
v_a_1962_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1944_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1944_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed(lean_object** _args){
lean_object* v___x_1970_ = _args[0];
lean_object* v___f_1971_ = _args[1];
lean_object* v___x_1972_ = _args[2];
lean_object* v___x_1973_ = _args[3];
lean_object* v_beta_1974_ = _args[4];
lean_object* v___x_1975_ = _args[5];
lean_object* v_alpha_1976_ = _args[6];
lean_object* v_numDiscrs_1977_ = _args[7];
lean_object* v___f_1978_ = _args[8];
lean_object* v_a_1979_ = _args[9];
lean_object* v_a_1980_ = _args[10];
lean_object* v_levelParams_1981_ = _args[11];
lean_object* v_matcherName_1982_ = _args[12];
lean_object* v___x_1983_ = _args[13];
lean_object* v_matcherInfo_1984_ = _args[14];
lean_object* v___x_1985_ = _args[15];
lean_object* v___x_1986_ = _args[16];
lean_object* v_uElimPos_x3f_1987_ = _args[17];
lean_object* v_f_1988_ = _args[18];
lean_object* v___y_1989_ = _args[19];
lean_object* v___y_1990_ = _args[20];
lean_object* v___y_1991_ = _args[21];
lean_object* v___y_1992_ = _args[22];
lean_object* v___y_1993_ = _args[23];
_start:
{
uint8_t v___x_17481__boxed_1994_; lean_object* v_res_1995_; 
v___x_17481__boxed_1994_ = lean_unbox(v___x_1975_);
v_res_1995_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(v___x_1970_, v___f_1971_, v___x_1972_, v___x_1973_, v_beta_1974_, v___x_17481__boxed_1994_, v_alpha_1976_, v_numDiscrs_1977_, v___f_1978_, v_a_1979_, v_a_1980_, v_levelParams_1981_, v_matcherName_1982_, v___x_1983_, v_matcherInfo_1984_, v___x_1985_, v___x_1986_, v_uElimPos_x3f_1987_, v_f_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(lean_object* v___x_2002_, lean_object* v_alpha_2003_, lean_object* v___x_2004_, lean_object* v___x_2005_, lean_object* v_numDiscrs_2006_, lean_object* v___f_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_levelParams_2010_, lean_object* v_matcherName_2011_, lean_object* v___x_2012_, lean_object* v_matcherInfo_2013_, lean_object* v___x_2014_, lean_object* v_uElimPos_x3f_2015_, lean_object* v_beta_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___f_2028_; lean_object* v___x_2029_; lean_object* v___f_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2022_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__1));
v___x_2023_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__3));
lean_inc_n(v___x_2002_, 2);
v___x_2024_ = l_Lean_Expr_bvar___override(v___x_2002_);
lean_inc_ref(v___x_2024_);
lean_inc_ref(v_beta_2016_);
v___x_2025_ = l_Lean_Expr_app___override(v_beta_2016_, v___x_2024_);
v___x_2026_ = 0;
v___x_2027_ = lean_box(v___x_2026_);
lean_inc_ref_n(v_alpha_2003_, 2);
v___f_2028_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2028_, 0, v___x_2002_);
lean_closure_set(v___f_2028_, 1, v___x_2023_);
lean_closure_set(v___f_2028_, 2, v_alpha_2003_);
lean_closure_set(v___f_2028_, 3, v___x_2027_);
v___x_2029_ = lean_box(v___x_2026_);
v___f_2030_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed), 24, 18);
lean_closure_set(v___f_2030_, 0, v___x_2004_);
lean_closure_set(v___f_2030_, 1, v___f_2028_);
lean_closure_set(v___f_2030_, 2, v___x_2024_);
lean_closure_set(v___f_2030_, 3, v___x_2005_);
lean_closure_set(v___f_2030_, 4, v_beta_2016_);
lean_closure_set(v___f_2030_, 5, v___x_2029_);
lean_closure_set(v___f_2030_, 6, v_alpha_2003_);
lean_closure_set(v___f_2030_, 7, v_numDiscrs_2006_);
lean_closure_set(v___f_2030_, 8, v___f_2007_);
lean_closure_set(v___f_2030_, 9, v_a_2008_);
lean_closure_set(v___f_2030_, 10, v_a_2009_);
lean_closure_set(v___f_2030_, 11, v_levelParams_2010_);
lean_closure_set(v___f_2030_, 12, v_matcherName_2011_);
lean_closure_set(v___f_2030_, 13, v___x_2012_);
lean_closure_set(v___f_2030_, 14, v_matcherInfo_2013_);
lean_closure_set(v___f_2030_, 15, v___x_2002_);
lean_closure_set(v___f_2030_, 16, v___x_2014_);
lean_closure_set(v___f_2030_, 17, v_uElimPos_x3f_2015_);
v___x_2031_ = l_Lean_Expr_forallE___override(v___x_2023_, v_alpha_2003_, v___x_2025_, v___x_2026_);
v___x_2032_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2022_, v___x_2031_, v___f_2030_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed(lean_object** _args){
lean_object* v___x_2033_ = _args[0];
lean_object* v_alpha_2034_ = _args[1];
lean_object* v___x_2035_ = _args[2];
lean_object* v___x_2036_ = _args[3];
lean_object* v_numDiscrs_2037_ = _args[4];
lean_object* v___f_2038_ = _args[5];
lean_object* v_a_2039_ = _args[6];
lean_object* v_a_2040_ = _args[7];
lean_object* v_levelParams_2041_ = _args[8];
lean_object* v_matcherName_2042_ = _args[9];
lean_object* v___x_2043_ = _args[10];
lean_object* v_matcherInfo_2044_ = _args[11];
lean_object* v___x_2045_ = _args[12];
lean_object* v_uElimPos_x3f_2046_ = _args[13];
lean_object* v_beta_2047_ = _args[14];
lean_object* v___y_2048_ = _args[15];
lean_object* v___y_2049_ = _args[16];
lean_object* v___y_2050_ = _args[17];
lean_object* v___y_2051_ = _args[18];
lean_object* v___y_2052_ = _args[19];
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(v___x_2033_, v_alpha_2034_, v___x_2035_, v___x_2036_, v_numDiscrs_2037_, v___f_2038_, v_a_2039_, v_a_2040_, v_levelParams_2041_, v_matcherName_2042_, v___x_2043_, v_matcherInfo_2044_, v___x_2045_, v_uElimPos_x3f_2046_, v_beta_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(lean_object* v_a_2057_, lean_object* v___x_2058_, lean_object* v___x_2059_, lean_object* v___x_2060_, lean_object* v_numDiscrs_2061_, lean_object* v___f_2062_, lean_object* v_a_2063_, lean_object* v_levelParams_2064_, lean_object* v_matcherName_2065_, lean_object* v___x_2066_, lean_object* v_matcherInfo_2067_, lean_object* v___x_2068_, lean_object* v_uElimPos_x3f_2069_, lean_object* v_alpha_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_inc(v_a_2057_);
v___x_2076_ = l_Lean_Level_param___override(v_a_2057_);
v___x_2077_ = l_Lean_Expr_sort___override(v___x_2076_);
lean_inc_ref(v_alpha_2070_);
v___x_2078_ = l_Lean_mkArrow(v_alpha_2070_, v___x_2077_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___f_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref(v___x_2078_);
v___f_2080_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed), 20, 14);
lean_closure_set(v___f_2080_, 0, v___x_2058_);
lean_closure_set(v___f_2080_, 1, v_alpha_2070_);
lean_closure_set(v___f_2080_, 2, v___x_2059_);
lean_closure_set(v___f_2080_, 3, v___x_2060_);
lean_closure_set(v___f_2080_, 4, v_numDiscrs_2061_);
lean_closure_set(v___f_2080_, 5, v___f_2062_);
lean_closure_set(v___f_2080_, 6, v_a_2057_);
lean_closure_set(v___f_2080_, 7, v_a_2063_);
lean_closure_set(v___f_2080_, 8, v_levelParams_2064_);
lean_closure_set(v___f_2080_, 9, v_matcherName_2065_);
lean_closure_set(v___f_2080_, 10, v___x_2066_);
lean_closure_set(v___f_2080_, 11, v_matcherInfo_2067_);
lean_closure_set(v___f_2080_, 12, v___x_2068_);
lean_closure_set(v___f_2080_, 13, v_uElimPos_x3f_2069_);
v___x_2081_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__1));
v___x_2082_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2081_, v_a_2079_, v___f_2080_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
return v___x_2082_;
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec_ref(v_alpha_2070_);
lean_dec(v_uElimPos_x3f_2069_);
lean_dec(v___x_2068_);
lean_dec_ref(v_matcherInfo_2067_);
lean_dec_ref(v___x_2066_);
lean_dec(v_matcherName_2065_);
lean_dec(v_levelParams_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v___f_2062_);
lean_dec(v_numDiscrs_2061_);
lean_dec(v___x_2060_);
lean_dec_ref(v___x_2059_);
lean_dec(v___x_2058_);
lean_dec(v_a_2057_);
v_a_2083_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2078_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2078_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed(lean_object** _args){
lean_object* v_a_2091_ = _args[0];
lean_object* v___x_2092_ = _args[1];
lean_object* v___x_2093_ = _args[2];
lean_object* v___x_2094_ = _args[3];
lean_object* v_numDiscrs_2095_ = _args[4];
lean_object* v___f_2096_ = _args[5];
lean_object* v_a_2097_ = _args[6];
lean_object* v_levelParams_2098_ = _args[7];
lean_object* v_matcherName_2099_ = _args[8];
lean_object* v___x_2100_ = _args[9];
lean_object* v_matcherInfo_2101_ = _args[10];
lean_object* v___x_2102_ = _args[11];
lean_object* v_uElimPos_x3f_2103_ = _args[12];
lean_object* v_alpha_2104_ = _args[13];
lean_object* v___y_2105_ = _args[14];
lean_object* v___y_2106_ = _args[15];
lean_object* v___y_2107_ = _args[16];
lean_object* v___y_2108_ = _args[17];
lean_object* v___y_2109_ = _args[18];
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(v_a_2091_, v___x_2092_, v___x_2093_, v___x_2094_, v_numDiscrs_2095_, v___f_2096_, v_a_2097_, v_levelParams_2098_, v_matcherName_2099_, v___x_2100_, v_matcherInfo_2101_, v___x_2102_, v_uElimPos_x3f_2103_, v_alpha_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(lean_object* v_numParams_2120_, lean_object* v___x_2121_, lean_object* v___x_2122_, lean_object* v_numDiscrs_2123_, lean_object* v___f_2124_, lean_object* v_levelParams_2125_, lean_object* v_matcherName_2126_, lean_object* v_matcherInfo_2127_, lean_object* v___x_2128_, lean_object* v_uElimPos_x3f_2129_, lean_object* v_xs_2130_, lean_object* v_x_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__1));
v___x_2138_ = l_Lean_Core_mkFreshUserName(v___x_2137_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___x_2138_);
v___x_2140_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__3));
v___x_2141_ = l_Lean_Core_mkFreshUserName(v___x_2140_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref(v___x_2141_);
v___x_2143_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2120_);
lean_inc_ref(v_xs_2130_);
v___x_2144_ = l_Array_toSubarray___redArg(v_xs_2130_, v___x_2143_, v_numParams_2120_);
v___x_2145_ = lean_array_get(v___x_2121_, v_xs_2130_, v_numParams_2120_);
lean_dec(v_numParams_2120_);
lean_dec_ref(v_xs_2130_);
lean_inc(v_a_2139_);
v___f_2146_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed), 19, 13);
lean_closure_set(v___f_2146_, 0, v_a_2142_);
lean_closure_set(v___f_2146_, 1, v___x_2143_);
lean_closure_set(v___f_2146_, 2, v___x_2145_);
lean_closure_set(v___f_2146_, 3, v___x_2122_);
lean_closure_set(v___f_2146_, 4, v_numDiscrs_2123_);
lean_closure_set(v___f_2146_, 5, v___f_2124_);
lean_closure_set(v___f_2146_, 6, v_a_2139_);
lean_closure_set(v___f_2146_, 7, v_levelParams_2125_);
lean_closure_set(v___f_2146_, 8, v_matcherName_2126_);
lean_closure_set(v___f_2146_, 9, v___x_2144_);
lean_closure_set(v___f_2146_, 10, v_matcherInfo_2127_);
lean_closure_set(v___f_2146_, 11, v___x_2128_);
lean_closure_set(v___f_2146_, 12, v_uElimPos_x3f_2129_);
v___x_2147_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__5));
v___x_2148_ = l_Lean_Level_param___override(v_a_2139_);
v___x_2149_ = l_Lean_Expr_sort___override(v___x_2148_);
v___x_2150_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2147_, v___x_2149_, v___f_2146_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
return v___x_2150_;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_a_2139_);
lean_dec_ref(v_xs_2130_);
lean_dec(v_uElimPos_x3f_2129_);
lean_dec(v___x_2128_);
lean_dec_ref(v_matcherInfo_2127_);
lean_dec(v_matcherName_2126_);
lean_dec(v_levelParams_2125_);
lean_dec_ref(v___f_2124_);
lean_dec(v_numDiscrs_2123_);
lean_dec(v___x_2122_);
lean_dec(v_numParams_2120_);
v_a_2151_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2141_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2141_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec_ref(v_xs_2130_);
lean_dec(v_uElimPos_x3f_2129_);
lean_dec(v___x_2128_);
lean_dec_ref(v_matcherInfo_2127_);
lean_dec(v_matcherName_2126_);
lean_dec(v_levelParams_2125_);
lean_dec_ref(v___f_2124_);
lean_dec(v_numDiscrs_2123_);
lean_dec(v___x_2122_);
lean_dec(v_numParams_2120_);
v_a_2159_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2138_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2138_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed(lean_object** _args){
lean_object* v_numParams_2167_ = _args[0];
lean_object* v___x_2168_ = _args[1];
lean_object* v___x_2169_ = _args[2];
lean_object* v_numDiscrs_2170_ = _args[3];
lean_object* v___f_2171_ = _args[4];
lean_object* v_levelParams_2172_ = _args[5];
lean_object* v_matcherName_2173_ = _args[6];
lean_object* v_matcherInfo_2174_ = _args[7];
lean_object* v___x_2175_ = _args[8];
lean_object* v_uElimPos_x3f_2176_ = _args[9];
lean_object* v_xs_2177_ = _args[10];
lean_object* v_x_2178_ = _args[11];
lean_object* v___y_2179_ = _args[12];
lean_object* v___y_2180_ = _args[13];
lean_object* v___y_2181_ = _args[14];
lean_object* v___y_2182_ = _args[15];
lean_object* v___y_2183_ = _args[16];
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(v_numParams_2167_, v___x_2168_, v___x_2169_, v_numDiscrs_2170_, v___f_2171_, v_levelParams_2172_, v_matcherName_2173_, v_matcherInfo_2174_, v___x_2175_, v_uElimPos_x3f_2176_, v_xs_2177_, v_x_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec_ref(v_x_2178_);
lean_dec_ref(v___x_2168_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(lean_object* v_ref_2185_, lean_object* v_msg_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_fileName_2192_; lean_object* v_fileMap_2193_; lean_object* v_options_2194_; lean_object* v_currRecDepth_2195_; lean_object* v_maxRecDepth_2196_; lean_object* v_ref_2197_; lean_object* v_currNamespace_2198_; lean_object* v_openDecls_2199_; lean_object* v_initHeartbeats_2200_; lean_object* v_maxHeartbeats_2201_; lean_object* v_quotContext_2202_; lean_object* v_currMacroScope_2203_; uint8_t v_diag_2204_; lean_object* v_cancelTk_x3f_2205_; uint8_t v_suppressElabErrors_2206_; lean_object* v_inheritedTraceOptions_2207_; lean_object* v_ref_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_fileName_2192_ = lean_ctor_get(v___y_2189_, 0);
v_fileMap_2193_ = lean_ctor_get(v___y_2189_, 1);
v_options_2194_ = lean_ctor_get(v___y_2189_, 2);
v_currRecDepth_2195_ = lean_ctor_get(v___y_2189_, 3);
v_maxRecDepth_2196_ = lean_ctor_get(v___y_2189_, 4);
v_ref_2197_ = lean_ctor_get(v___y_2189_, 5);
v_currNamespace_2198_ = lean_ctor_get(v___y_2189_, 6);
v_openDecls_2199_ = lean_ctor_get(v___y_2189_, 7);
v_initHeartbeats_2200_ = lean_ctor_get(v___y_2189_, 8);
v_maxHeartbeats_2201_ = lean_ctor_get(v___y_2189_, 9);
v_quotContext_2202_ = lean_ctor_get(v___y_2189_, 10);
v_currMacroScope_2203_ = lean_ctor_get(v___y_2189_, 11);
v_diag_2204_ = lean_ctor_get_uint8(v___y_2189_, sizeof(void*)*14);
v_cancelTk_x3f_2205_ = lean_ctor_get(v___y_2189_, 12);
v_suppressElabErrors_2206_ = lean_ctor_get_uint8(v___y_2189_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2207_ = lean_ctor_get(v___y_2189_, 13);
v_ref_2208_ = l_Lean_replaceRef(v_ref_2185_, v_ref_2197_);
lean_inc_ref(v_inheritedTraceOptions_2207_);
lean_inc(v_cancelTk_x3f_2205_);
lean_inc(v_currMacroScope_2203_);
lean_inc(v_quotContext_2202_);
lean_inc(v_maxHeartbeats_2201_);
lean_inc(v_initHeartbeats_2200_);
lean_inc(v_openDecls_2199_);
lean_inc(v_currNamespace_2198_);
lean_inc(v_maxRecDepth_2196_);
lean_inc(v_currRecDepth_2195_);
lean_inc_ref(v_options_2194_);
lean_inc_ref(v_fileMap_2193_);
lean_inc_ref(v_fileName_2192_);
v___x_2209_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2209_, 0, v_fileName_2192_);
lean_ctor_set(v___x_2209_, 1, v_fileMap_2193_);
lean_ctor_set(v___x_2209_, 2, v_options_2194_);
lean_ctor_set(v___x_2209_, 3, v_currRecDepth_2195_);
lean_ctor_set(v___x_2209_, 4, v_maxRecDepth_2196_);
lean_ctor_set(v___x_2209_, 5, v_ref_2208_);
lean_ctor_set(v___x_2209_, 6, v_currNamespace_2198_);
lean_ctor_set(v___x_2209_, 7, v_openDecls_2199_);
lean_ctor_set(v___x_2209_, 8, v_initHeartbeats_2200_);
lean_ctor_set(v___x_2209_, 9, v_maxHeartbeats_2201_);
lean_ctor_set(v___x_2209_, 10, v_quotContext_2202_);
lean_ctor_set(v___x_2209_, 11, v_currMacroScope_2203_);
lean_ctor_set(v___x_2209_, 12, v_cancelTk_x3f_2205_);
lean_ctor_set(v___x_2209_, 13, v_inheritedTraceOptions_2207_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*14, v_diag_2204_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*14 + 1, v_suppressElabErrors_2206_);
v___x_2210_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_2186_, v___y_2187_, v___y_2188_, v___x_2209_, v___y_2190_);
lean_dec_ref(v___x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2211_, lean_object* v_msg_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2211_, v_msg_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v_ref_2211_);
return v_res_2218_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2223_ = lean_unsigned_to_nat(0u);
v___x_2224_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
lean_ctor_set(v___x_2224_, 2, v___x_2223_);
lean_ctor_set(v___x_2224_, 3, v___x_2222_);
lean_ctor_set(v___x_2224_, 4, v___x_2222_);
lean_ctor_set(v___x_2224_, 5, v___x_2222_);
lean_ctor_set(v___x_2224_, 6, v___x_2222_);
lean_ctor_set(v___x_2224_, 7, v___x_2222_);
lean_ctor_set(v___x_2224_, 8, v___x_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = lean_unsigned_to_nat(32u);
v___x_2226_ = lean_mk_empty_array_with_capacity(v___x_2225_);
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2228_ = ((size_t)5ULL);
v___x_2229_ = lean_unsigned_to_nat(0u);
v___x_2230_ = lean_unsigned_to_nat(32u);
v___x_2231_ = lean_mk_empty_array_with_capacity(v___x_2230_);
v___x_2232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3);
v___x_2233_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
lean_ctor_set(v___x_2233_, 1, v___x_2231_);
lean_ctor_set(v___x_2233_, 2, v___x_2229_);
lean_ctor_set(v___x_2233_, 3, v___x_2229_);
lean_ctor_set_usize(v___x_2233_, 4, v___x_2228_);
return v___x_2233_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2234_ = lean_box(1);
v___x_2235_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4);
v___x_2236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
lean_ctor_set(v___x_2237_, 1, v___x_2235_);
lean_ctor_set(v___x_2237_, 2, v___x_2234_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__6));
v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__8));
v___x_2243_ = l_Lean_stringToMessageData(v___x_2242_);
return v___x_2243_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__10));
v___x_2246_ = l_Lean_stringToMessageData(v___x_2245_);
return v___x_2246_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__12));
v___x_2249_ = l_Lean_stringToMessageData(v___x_2248_);
return v___x_2249_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__14));
v___x_2252_ = l_Lean_stringToMessageData(v___x_2251_);
return v___x_2252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16));
v___x_2255_ = l_Lean_stringToMessageData(v___x_2254_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18));
v___x_2258_ = l_Lean_stringToMessageData(v___x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2259_, lean_object* v_declHint_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v_env_2264_; uint8_t v___x_2265_; 
v___x_2263_ = lean_st_ref_get(v___y_2261_);
v_env_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc_ref(v_env_2264_);
lean_dec(v___x_2263_);
v___x_2265_ = l_Lean_Name_isAnonymous(v_declHint_2260_);
if (v___x_2265_ == 0)
{
uint8_t v_isExporting_2266_; 
v_isExporting_2266_ = lean_ctor_get_uint8(v_env_2264_, sizeof(void*)*8);
if (v_isExporting_2266_ == 0)
{
lean_object* v___x_2267_; 
lean_dec_ref(v_env_2264_);
lean_dec(v_declHint_2260_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_msg_2259_);
return v___x_2267_;
}
else
{
lean_object* v___x_2268_; uint8_t v___x_2269_; 
lean_inc_ref(v_env_2264_);
v___x_2268_ = l_Lean_Environment_setExporting(v_env_2264_, v___x_2265_);
lean_inc(v_declHint_2260_);
lean_inc_ref(v___x_2268_);
v___x_2269_ = l_Lean_Environment_contains(v___x_2268_, v_declHint_2260_, v_isExporting_2266_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; 
lean_dec_ref(v___x_2268_);
lean_dec_ref(v_env_2264_);
lean_dec(v_declHint_2260_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v_msg_2259_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v_c_2276_; lean_object* v___x_2277_; 
v___x_2271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2272_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2273_ = l_Lean_Options_empty;
v___x_2274_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2268_);
lean_ctor_set(v___x_2274_, 1, v___x_2271_);
lean_ctor_set(v___x_2274_, 2, v___x_2272_);
lean_ctor_set(v___x_2274_, 3, v___x_2273_);
lean_inc(v_declHint_2260_);
v___x_2275_ = l_Lean_MessageData_ofConstName(v_declHint_2260_, v___x_2265_);
v_c_2276_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2276_, 0, v___x_2274_);
lean_ctor_set(v_c_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2264_, v_declHint_2260_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
lean_dec_ref(v_env_2264_);
lean_dec(v_declHint_2260_);
v___x_2278_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set(v___x_2279_, 1, v_c_2276_);
v___x_2280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = l_Lean_MessageData_note(v___x_2281_);
v___x_2283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2283_, 0, v_msg_2259_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
else
{
lean_object* v_val_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2320_; 
v_val_2285_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2287_ = v___x_2277_;
v_isShared_2288_ = v_isSharedCheck_2320_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_val_2285_);
lean_dec(v___x_2277_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2320_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v_mod_2292_; uint8_t v___x_2293_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = l_Lean_Environment_header(v_env_2264_);
lean_dec_ref(v_env_2264_);
v___x_2291_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2290_);
v_mod_2292_ = lean_array_get(v___x_2289_, v___x_2291_, v_val_2285_);
lean_dec(v_val_2285_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = l_Lean_isPrivateName(v_declHint_2260_);
lean_dec(v_declHint_2260_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2294_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v_c_2276_);
v___x_2296_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = l_Lean_MessageData_ofName(v_mod_2292_);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = l_Lean_MessageData_note(v___x_2301_);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v_msg_2259_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set_tag(v___x_2287_, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2303_);
v___x_2305_ = v___x_2287_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2307_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v_c_2276_);
v___x_2309_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_2310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = l_Lean_MessageData_ofName(v_mod_2292_);
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = l_Lean_MessageData_note(v___x_2314_);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v_msg_2259_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set_tag(v___x_2287_, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2316_);
v___x_2318_ = v___x_2287_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2321_; 
lean_dec_ref(v_env_2264_);
lean_dec(v_declHint_2260_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_msg_2259_);
return v___x_2321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2322_, lean_object* v_declHint_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2322_, v_declHint_2323_, v___y_2324_);
lean_dec(v___y_2324_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(lean_object* v_msg_2327_, lean_object* v_declHint_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2344_; 
v___x_2334_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2327_, v_declHint_2328_, v___y_2332_);
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2344_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2344_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2339_ = l_Lean_unknownIdentifierMessageTag;
v___x_2340_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v_a_2335_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2340_);
v___x_2342_ = v___x_2337_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11___boxed(lean_object* v_msg_2345_, lean_object* v_declHint_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2345_, v_declHint_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_ref_2353_, lean_object* v_msg_2354_, lean_object* v_declHint_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; lean_object* v_a_2362_; lean_object* v___x_2363_; 
v___x_2361_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2354_, v_declHint_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref(v___x_2361_);
v___x_2363_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2353_, v_a_2362_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_ref_2364_, lean_object* v_msg_2365_, lean_object* v_declHint_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2364_, v_msg_2365_, v_declHint_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v_ref_2364_);
return v_res_2372_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_2375_ = l_Lean_stringToMessageData(v___x_2374_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_2378_ = l_Lean_stringToMessageData(v___x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_2379_, lean_object* v_constName_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2386_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_2387_ = 0;
lean_inc(v_constName_2380_);
v___x_2388_ = l_Lean_MessageData_ofConstName(v_constName_2380_, v___x_2387_);
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2386_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2379_, v___x_2391_, v_constName_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_2393_, lean_object* v_constName_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2393_, v_constName_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v_ref_2393_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(lean_object* v_constName_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_ref_2407_; lean_object* v___x_2408_; 
v_ref_2407_ = lean_ctor_get(v___y_2404_, 5);
v___x_2408_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2407_, v_constName_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(lean_object* v_constName_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; lean_object* v_env_2423_; uint8_t v___x_2424_; lean_object* v___x_2425_; 
v___x_2422_ = lean_st_ref_get(v___y_2420_);
v_env_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc_ref(v_env_2423_);
lean_dec(v___x_2422_);
v___x_2424_ = 0;
lean_inc(v_constName_2416_);
v___x_2425_ = l_Lean_Environment_findConstVal_x3f(v_env_2423_, v_constName_2416_, v___x_2424_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v___x_2426_;
}
else
{
lean_object* v_val_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_constName_2416_);
v_val_2427_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2425_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_val_2427_);
lean_dec(v___x_2425_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set_tag(v___x_2429_, 0);
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_val_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0___boxed(lean_object* v_constName_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_constName_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(lean_object* v_matcherName_2442_, lean_object* v_matcherInfo_2443_, lean_object* v___x_2444_, lean_object* v___f_2445_, lean_object* v___x_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
lean_inc(v_matcherName_2442_);
v___x_2452_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_matcherName_2442_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v_levelParams_2454_; lean_object* v_type_2455_; lean_object* v_numParams_2456_; lean_object* v_numDiscrs_2457_; lean_object* v_uElimPos_x3f_2458_; lean_object* v___x_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; lean_object* v___x_2464_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref(v___x_2452_);
v_levelParams_2454_ = lean_ctor_get(v_a_2453_, 1);
lean_inc(v_levelParams_2454_);
v_type_2455_ = lean_ctor_get(v_a_2453_, 2);
lean_inc_ref(v_type_2455_);
lean_dec(v_a_2453_);
v_numParams_2456_ = lean_ctor_get(v_matcherInfo_2443_, 0);
lean_inc_n(v_numParams_2456_, 2);
v_numDiscrs_2457_ = lean_ctor_get(v_matcherInfo_2443_, 1);
lean_inc(v_numDiscrs_2457_);
v_uElimPos_x3f_2458_ = lean_ctor_get(v_matcherInfo_2443_, 3);
lean_inc(v_uElimPos_x3f_2458_);
v___x_2459_ = lean_unsigned_to_nat(1u);
v___f_2460_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed), 17, 10);
lean_closure_set(v___f_2460_, 0, v_numParams_2456_);
lean_closure_set(v___f_2460_, 1, v___x_2444_);
lean_closure_set(v___f_2460_, 2, v___x_2459_);
lean_closure_set(v___f_2460_, 3, v_numDiscrs_2457_);
lean_closure_set(v___f_2460_, 4, v___f_2445_);
lean_closure_set(v___f_2460_, 5, v_levelParams_2454_);
lean_closure_set(v___f_2460_, 6, v_matcherName_2442_);
lean_closure_set(v___f_2460_, 7, v_matcherInfo_2443_);
lean_closure_set(v___f_2460_, 8, v___x_2446_);
lean_closure_set(v___f_2460_, 9, v_uElimPos_x3f_2458_);
v___x_2461_ = lean_nat_add(v_numParams_2456_, v___x_2459_);
lean_dec(v_numParams_2456_);
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
v___x_2463_ = 0;
v___x_2464_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_2455_, v___x_2462_, v___f_2460_, v___x_2463_, v___x_2463_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
return v___x_2464_;
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v___x_2446_);
lean_dec_ref(v___f_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v_matcherInfo_2443_);
lean_dec(v_matcherName_2442_);
v_a_2465_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2452_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2452_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed(lean_object* v_matcherName_2473_, lean_object* v_matcherInfo_2474_, lean_object* v___x_2475_, lean_object* v___f_2476_, lean_object* v___x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(v_matcherName_2473_, v_matcherInfo_2474_, v___x_2475_, v___f_2476_, v___x_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11(lean_object* v___x_2484_, lean_object* v_e_2485_){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = l_Lean_indentD(v_e_2485_);
v___x_2487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2484_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(lean_object* v___f_2488_, lean_object* v___f_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2488_, v___f_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
v_a_2504_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2495_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2495_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed(lean_object* v___f_2512_, lean_object* v___f_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(v___f_2512_, v___f_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
return v_res_2519_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__3));
v___x_2526_ = l_Lean_stringToMessageData(v___x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(lean_object* v_matcherName_2527_, lean_object* v_matcherInfo_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v___x_2534_; lean_object* v_env_2535_; lean_object* v___f_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___f_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___f_2545_; lean_object* v___f_2546_; lean_object* v___x_2547_; 
v___x_2534_ = lean_st_ref_get(v_a_2532_);
v_env_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc_ref(v_env_2535_);
lean_dec(v___x_2534_);
v___f_2536_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__0));
v___x_2537_ = l_Lean_instInhabitedExpr;
lean_inc_n(v_matcherName_2527_, 3);
v___x_2538_ = l_Lean_mkPrivateName(v_env_2535_, v_matcherName_2527_);
lean_dec_ref(v_env_2535_);
v___x_2539_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__2));
v___x_2540_ = l_Lean_Name_append(v___x_2538_, v___x_2539_);
lean_inc_n(v___x_2540_, 2);
v___f_2541_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed), 10, 5);
lean_closure_set(v___f_2541_, 0, v_matcherName_2527_);
lean_closure_set(v___f_2541_, 1, v_matcherInfo_2528_);
lean_closure_set(v___f_2541_, 2, v___x_2537_);
lean_closure_set(v___f_2541_, 3, v___f_2536_);
lean_closure_set(v___f_2541_, 4, v___x_2540_);
v___x_2542_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4);
v___x_2543_ = l_Lean_MessageData_ofName(v_matcherName_2527_);
v___x_2544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___f_2545_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_2545_, 0, v___x_2544_);
v___f_2546_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed), 7, 2);
lean_closure_set(v___f_2546_, 0, v___f_2541_);
lean_closure_set(v___f_2546_, 1, v___f_2545_);
v___x_2547_ = l_Lean_Meta_realizeConst(v_matcherName_2527_, v___x_2540_, v___f_2546_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2554_ == 0)
{
lean_object* v_unused_2555_; 
v_unused_2555_ = lean_ctor_get(v___x_2547_, 0);
lean_dec(v_unused_2555_);
v___x_2549_ = v___x_2547_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_dec(v___x_2547_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2540_);
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2540_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v___x_2540_);
v_a_2556_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2547_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2547_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___boxed(lean_object* v_matcherName_2564_, lean_object* v_matcherInfo_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_2564_, v_matcherInfo_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(lean_object* v_as_2572_, lean_object* v_as_x27_2573_, lean_object* v_b_2574_, lean_object* v_a_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_2573_, v_b_2574_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___boxed(lean_object* v_as_2582_, lean_object* v_as_x27_2583_, lean_object* v_b_2584_, lean_object* v_a_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(v_as_2582_, v_as_x27_2583_, v_b_2584_, v_a_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v_as_2582_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(lean_object* v_00_u03b1_2592_, lean_object* v_name_2593_, uint8_t v_bi_2594_, lean_object* v_type_2595_, lean_object* v_k_2596_, uint8_t v_kind_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_2593_, v_bi_2594_, v_type_2595_, v_k_2596_, v_kind_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2604_, lean_object* v_name_2605_, lean_object* v_bi_2606_, lean_object* v_type_2607_, lean_object* v_k_2608_, lean_object* v_kind_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
uint8_t v_bi_boxed_2615_; uint8_t v_kind_boxed_2616_; lean_object* v_res_2617_; 
v_bi_boxed_2615_ = lean_unbox(v_bi_2606_);
v_kind_boxed_2616_ = lean_unbox(v_kind_2609_);
v_res_2617_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(v_00_u03b1_2604_, v_name_2605_, v_bi_boxed_2615_, v_type_2607_, v_k_2608_, v_kind_boxed_2616_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(lean_object* v_00_u03b1_2618_, lean_object* v_name_2619_, lean_object* v_type_2620_, lean_object* v_k_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_2619_, v_type_2620_, v_k_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___boxed(lean_object* v_00_u03b1_2628_, lean_object* v_name_2629_, lean_object* v_type_2630_, lean_object* v_k_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(v_00_u03b1_2628_, v_name_2629_, v_type_2630_, v_k_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(lean_object* v_00_u03b1_2638_, lean_object* v_constName_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2646_, lean_object* v_constName_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(v_00_u03b1_2646_, v_constName_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2654_, lean_object* v_ref_2655_, lean_object* v_constName_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2655_, v_constName_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2663_, lean_object* v_ref_2664_, lean_object* v_constName_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(v_00_u03b1_2663_, v_ref_2664_, v_constName_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v_ref_2664_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b1_2672_, lean_object* v_ref_2673_, lean_object* v_msg_2674_, lean_object* v_declHint_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2673_, v_msg_2674_, v_declHint_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b1_2682_, lean_object* v_ref_2683_, lean_object* v_msg_2684_, lean_object* v_declHint_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(v_00_u03b1_2682_, v_ref_2683_, v_msg_2684_, v_declHint_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v_ref_2683_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(lean_object* v_msg_2692_, lean_object* v_declHint_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2692_, v_declHint_2693_, v___y_2697_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_2700_, lean_object* v_declHint_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(v_msg_2700_, v_declHint_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_2708_, lean_object* v_ref_2709_, lean_object* v_msg_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2709_, v_msg_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_2717_, lean_object* v_ref_2718_, lean_object* v_msg_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(v_00_u03b1_2717_, v_ref_2718_, v_msg_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v_ref_2718_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(lean_object* v_msg_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v___f_2736_; lean_object* v___x_46802__overap_2737_; lean_object* v___x_2738_; 
v___f_2736_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0));
v___x_46802__overap_2737_ = lean_panic_fn_borrowed(v___f_2736_, v_msg_2727_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
lean_inc(v___y_2728_);
v___x_2738_ = lean_apply_8(v___x_46802__overap_2737_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___boxed(lean_object* v_msg_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v_msg_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(lean_object* v_k_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v_b_2753_, lean_object* v_c_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; 
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2757_);
lean_inc(v___y_2756_);
lean_inc_ref(v___y_2755_);
lean_inc(v___y_2752_);
lean_inc_ref(v___y_2751_);
lean_inc(v___y_2750_);
v___x_2760_ = lean_apply_10(v_k_2749_, v_b_2753_, v_c_2754_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, lean_box(0));
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed(lean_object* v_k_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v_b_2765_, lean_object* v_c_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(v_k_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v_b_2765_, v_c_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(lean_object* v_e_2773_, lean_object* v_k_2774_, uint8_t v_cleanupAnnotations_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___f_2784_; uint8_t v___x_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_inc(v___y_2778_);
lean_inc_ref(v___y_2777_);
lean_inc(v___y_2776_);
v___f_2784_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2784_, 0, v_k_2774_);
lean_closure_set(v___f_2784_, 1, v___y_2776_);
lean_closure_set(v___f_2784_, 2, v___y_2777_);
lean_closure_set(v___f_2784_, 3, v___y_2778_);
v___x_2785_ = 1;
v___x_2786_ = 0;
v___x_2787_ = lean_box(0);
v___x_2788_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2773_, v___x_2785_, v___x_2786_, v___x_2785_, v___x_2786_, v___x_2787_, v___f_2784_, v_cleanupAnnotations_2775_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2788_) == 0)
{
return v___x_2788_;
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___boxed(lean_object* v_e_2797_, lean_object* v_k_2798_, lean_object* v_cleanupAnnotations_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2808_; lean_object* v_res_2809_; 
v_cleanupAnnotations_boxed_2808_ = lean_unbox(v_cleanupAnnotations_2799_);
v_res_2809_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2797_, v_k_2798_, v_cleanupAnnotations_boxed_2808_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(lean_object* v_00_u03b1_2810_, lean_object* v_e_2811_, lean_object* v_k_2812_, uint8_t v_cleanupAnnotations_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2811_, v_k_2812_, v_cleanupAnnotations_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___boxed(lean_object* v_00_u03b1_2823_, lean_object* v_e_2824_, lean_object* v_k_2825_, lean_object* v_cleanupAnnotations_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2835_; lean_object* v_res_2836_; 
v_cleanupAnnotations_boxed_2835_ = lean_unbox(v_cleanupAnnotations_2826_);
v_res_2836_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(v_00_u03b1_2823_, v_e_2824_, v_k_2825_, v_cleanupAnnotations_boxed_2835_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(uint8_t v___x_2837_, uint8_t v___x_2838_, uint8_t v___x_2839_, lean_object* v_xs_2840_, lean_object* v_motiveBody_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; 
v___x_2850_ = l_Lean_Expr_bindingDomain_x21(v_motiveBody_2841_);
v___x_2851_ = l_Lean_Expr_bindingName_x21(v___x_2850_);
v___x_2852_ = l_Lean_Expr_bindingDomain_x21(v___x_2850_);
v___x_2853_ = l_Lean_Expr_bindingBody_x21(v___x_2850_);
lean_dec_ref(v___x_2850_);
v___x_2854_ = l_Lean_Expr_bindingDomain_x21(v___x_2853_);
lean_dec_ref(v___x_2853_);
v___x_2855_ = l_Lean_Expr_lam___override(v___x_2851_, v___x_2852_, v___x_2854_, v___x_2837_);
v___x_2856_ = 1;
v___x_2857_ = l_Lean_Meta_mkLambdaFVars(v_xs_2840_, v___x_2855_, v___x_2838_, v___x_2839_, v___x_2838_, v___x_2839_, v___x_2856_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed(lean_object* v___x_2858_, lean_object* v___x_2859_, lean_object* v___x_2860_, lean_object* v_xs_2861_, lean_object* v_motiveBody_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
uint8_t v___x_54557__boxed_2871_; uint8_t v___x_54558__boxed_2872_; uint8_t v___x_54559__boxed_2873_; lean_object* v_res_2874_; 
v___x_54557__boxed_2871_ = lean_unbox(v___x_2858_);
v___x_54558__boxed_2872_ = lean_unbox(v___x_2859_);
v___x_54559__boxed_2873_ = lean_unbox(v___x_2860_);
v_res_2874_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(v___x_54557__boxed_2871_, v___x_54558__boxed_2872_, v___x_54559__boxed_2873_, v_xs_2861_, v_motiveBody_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v_motiveBody_2862_);
lean_dec_ref(v_xs_2861_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(size_t v_sz_2875_, size_t v_i_2876_, lean_object* v_bs_2877_){
_start:
{
uint8_t v___x_2878_; 
v___x_2878_ = lean_usize_dec_lt(v_i_2876_, v_sz_2875_);
if (v___x_2878_ == 0)
{
return v_bs_2877_;
}
else
{
lean_object* v_v_2879_; lean_object* v___x_2880_; lean_object* v_bs_x27_2881_; lean_object* v___x_2882_; size_t v___x_2883_; size_t v___x_2884_; lean_object* v___x_2885_; 
v_v_2879_ = lean_array_uget(v_bs_2877_, v_i_2876_);
v___x_2880_ = lean_unsigned_to_nat(0u);
v_bs_x27_2881_ = lean_array_uset(v_bs_2877_, v_i_2876_, v___x_2880_);
v___x_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2882_, 0, v_v_2879_);
v___x_2883_ = ((size_t)1ULL);
v___x_2884_ = lean_usize_add(v_i_2876_, v___x_2883_);
v___x_2885_ = lean_array_uset(v_bs_x27_2881_, v_i_2876_, v___x_2882_);
v_i_2876_ = v___x_2884_;
v_bs_2877_ = v___x_2885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4___boxed(lean_object* v_sz_2887_, lean_object* v_i_2888_, lean_object* v_bs_2889_){
_start:
{
size_t v_sz_boxed_2890_; size_t v_i_boxed_2891_; lean_object* v_res_2892_; 
v_sz_boxed_2890_ = lean_unbox_usize(v_sz_2887_);
lean_dec(v_sz_2887_);
v_i_boxed_2891_ = lean_unbox_usize(v_i_2888_);
lean_dec(v_i_2888_);
v_res_2892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_boxed_2890_, v_i_boxed_2891_, v_bs_2889_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(lean_object* v_msg_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_ref_2899_; lean_object* v___x_2900_; lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2909_; 
v_ref_2899_ = lean_ctor_get(v___y_2896_, 5);
v___x_2900_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2903_ = v___x_2900_;
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
lean_inc(v_ref_2899_);
v___x_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2905_, 0, v_ref_2899_);
lean_ctor_set(v___x_2905_, 1, v_a_2901_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set_tag(v___x_2903_, 1);
lean_ctor_set(v___x_2903_, 0, v___x_2905_);
v___x_2907_ = v___x_2903_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg___boxed(lean_object* v_msg_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(lean_object* v_declName_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v___x_2920_; lean_object* v_env_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2920_ = lean_st_ref_get(v___y_2918_);
v_env_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_ref(v_env_2921_);
lean_dec(v___x_2920_);
v___x_2922_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2921_, v_declName_2917_);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg___boxed(lean_object* v_declName_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_2924_, v___y_2925_);
lean_dec(v___y_2925_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(lean_object* v_ref_2928_, lean_object* v_msg_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_fileName_2938_; lean_object* v_fileMap_2939_; lean_object* v_options_2940_; lean_object* v_currRecDepth_2941_; lean_object* v_maxRecDepth_2942_; lean_object* v_ref_2943_; lean_object* v_currNamespace_2944_; lean_object* v_openDecls_2945_; lean_object* v_initHeartbeats_2946_; lean_object* v_maxHeartbeats_2947_; lean_object* v_quotContext_2948_; lean_object* v_currMacroScope_2949_; uint8_t v_diag_2950_; lean_object* v_cancelTk_x3f_2951_; uint8_t v_suppressElabErrors_2952_; lean_object* v_inheritedTraceOptions_2953_; lean_object* v_ref_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_fileName_2938_ = lean_ctor_get(v___y_2935_, 0);
v_fileMap_2939_ = lean_ctor_get(v___y_2935_, 1);
v_options_2940_ = lean_ctor_get(v___y_2935_, 2);
v_currRecDepth_2941_ = lean_ctor_get(v___y_2935_, 3);
v_maxRecDepth_2942_ = lean_ctor_get(v___y_2935_, 4);
v_ref_2943_ = lean_ctor_get(v___y_2935_, 5);
v_currNamespace_2944_ = lean_ctor_get(v___y_2935_, 6);
v_openDecls_2945_ = lean_ctor_get(v___y_2935_, 7);
v_initHeartbeats_2946_ = lean_ctor_get(v___y_2935_, 8);
v_maxHeartbeats_2947_ = lean_ctor_get(v___y_2935_, 9);
v_quotContext_2948_ = lean_ctor_get(v___y_2935_, 10);
v_currMacroScope_2949_ = lean_ctor_get(v___y_2935_, 11);
v_diag_2950_ = lean_ctor_get_uint8(v___y_2935_, sizeof(void*)*14);
v_cancelTk_x3f_2951_ = lean_ctor_get(v___y_2935_, 12);
v_suppressElabErrors_2952_ = lean_ctor_get_uint8(v___y_2935_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2953_ = lean_ctor_get(v___y_2935_, 13);
v_ref_2954_ = l_Lean_replaceRef(v_ref_2928_, v_ref_2943_);
lean_inc_ref(v_inheritedTraceOptions_2953_);
lean_inc(v_cancelTk_x3f_2951_);
lean_inc(v_currMacroScope_2949_);
lean_inc(v_quotContext_2948_);
lean_inc(v_maxHeartbeats_2947_);
lean_inc(v_initHeartbeats_2946_);
lean_inc(v_openDecls_2945_);
lean_inc(v_currNamespace_2944_);
lean_inc(v_maxRecDepth_2942_);
lean_inc(v_currRecDepth_2941_);
lean_inc_ref(v_options_2940_);
lean_inc_ref(v_fileMap_2939_);
lean_inc_ref(v_fileName_2938_);
v___x_2955_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2955_, 0, v_fileName_2938_);
lean_ctor_set(v___x_2955_, 1, v_fileMap_2939_);
lean_ctor_set(v___x_2955_, 2, v_options_2940_);
lean_ctor_set(v___x_2955_, 3, v_currRecDepth_2941_);
lean_ctor_set(v___x_2955_, 4, v_maxRecDepth_2942_);
lean_ctor_set(v___x_2955_, 5, v_ref_2954_);
lean_ctor_set(v___x_2955_, 6, v_currNamespace_2944_);
lean_ctor_set(v___x_2955_, 7, v_openDecls_2945_);
lean_ctor_set(v___x_2955_, 8, v_initHeartbeats_2946_);
lean_ctor_set(v___x_2955_, 9, v_maxHeartbeats_2947_);
lean_ctor_set(v___x_2955_, 10, v_quotContext_2948_);
lean_ctor_set(v___x_2955_, 11, v_currMacroScope_2949_);
lean_ctor_set(v___x_2955_, 12, v_cancelTk_x3f_2951_);
lean_ctor_set(v___x_2955_, 13, v_inheritedTraceOptions_2953_);
lean_ctor_set_uint8(v___x_2955_, sizeof(void*)*14, v_diag_2950_);
lean_ctor_set_uint8(v___x_2955_, sizeof(void*)*14 + 1, v_suppressElabErrors_2952_);
v___x_2956_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2929_, v___y_2933_, v___y_2934_, v___x_2955_, v___y_2936_);
lean_dec_ref(v___x_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2957_, lean_object* v_msg_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_2957_, v_msg_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v_ref_2957_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2968_, lean_object* v_declHint_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; lean_object* v_env_2973_; uint8_t v___x_2974_; 
v___x_2972_ = lean_st_ref_get(v___y_2970_);
v_env_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc_ref(v_env_2973_);
lean_dec(v___x_2972_);
v___x_2974_ = l_Lean_Name_isAnonymous(v_declHint_2969_);
if (v___x_2974_ == 0)
{
uint8_t v_isExporting_2975_; 
v_isExporting_2975_ = lean_ctor_get_uint8(v_env_2973_, sizeof(void*)*8);
if (v_isExporting_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_dec_ref(v_env_2973_);
lean_dec(v_declHint_2969_);
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v_msg_2968_);
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; uint8_t v___x_2978_; 
lean_inc_ref(v_env_2973_);
v___x_2977_ = l_Lean_Environment_setExporting(v_env_2973_, v___x_2974_);
lean_inc(v_declHint_2969_);
lean_inc_ref(v___x_2977_);
v___x_2978_ = l_Lean_Environment_contains(v___x_2977_, v_declHint_2969_, v_isExporting_2975_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
lean_dec_ref(v___x_2977_);
lean_dec_ref(v_env_2973_);
lean_dec(v_declHint_2969_);
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_msg_2968_);
return v___x_2979_;
}
else
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v_c_2987_; lean_object* v___x_2988_; 
v___x_2980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2981_ = lean_unsigned_to_nat(32u);
v___x_2982_ = lean_mk_empty_array_with_capacity(v___x_2981_);
lean_dec_ref(v___x_2982_);
v___x_2983_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2984_ = l_Lean_Options_empty;
v___x_2985_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2977_);
lean_ctor_set(v___x_2985_, 1, v___x_2980_);
lean_ctor_set(v___x_2985_, 2, v___x_2983_);
lean_ctor_set(v___x_2985_, 3, v___x_2984_);
lean_inc(v_declHint_2969_);
v___x_2986_ = l_Lean_MessageData_ofConstName(v_declHint_2969_, v___x_2974_);
v_c_2987_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2987_, 0, v___x_2985_);
lean_ctor_set(v_c_2987_, 1, v___x_2986_);
v___x_2988_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2973_, v_declHint_2969_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_dec_ref(v_env_2973_);
lean_dec(v_declHint_2969_);
v___x_2989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
lean_ctor_set(v___x_2990_, 1, v_c_2987_);
v___x_2991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2990_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = l_Lean_MessageData_note(v___x_2992_);
v___x_2994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2994_, 0, v_msg_2968_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
return v___x_2995_;
}
else
{
lean_object* v_val_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3031_; 
v_val_2996_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_2998_ = v___x_2988_;
v_isShared_2999_ = v_isSharedCheck_3031_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_val_2996_);
lean_dec(v___x_2988_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3031_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v_mod_3003_; uint8_t v___x_3004_; 
v___x_3000_ = lean_box(0);
v___x_3001_ = l_Lean_Environment_header(v_env_2973_);
lean_dec_ref(v_env_2973_);
v___x_3002_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3001_);
v_mod_3003_ = lean_array_get(v___x_3000_, v___x_3002_, v_val_2996_);
lean_dec(v_val_2996_);
lean_dec_ref(v___x_3002_);
v___x_3004_ = l_Lean_isPrivateName(v_declHint_2969_);
lean_dec(v_declHint_2969_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3005_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_3006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
lean_ctor_set(v___x_3006_, 1, v_c_2987_);
v___x_3007_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = l_Lean_MessageData_ofName(v_mod_3003_);
v___x_3010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3008_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v___x_3011_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_3012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = l_Lean_MessageData_note(v___x_3012_);
v___x_3014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3014_, 0, v_msg_2968_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set_tag(v___x_2998_, 0);
lean_ctor_set(v___x_2998_, 0, v___x_3014_);
v___x_3016_ = v___x_2998_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; 
v___x_3018_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v_c_2987_);
v___x_3020_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_3021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = l_Lean_MessageData_ofName(v_mod_3003_);
v___x_3023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3023_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = l_Lean_MessageData_note(v___x_3025_);
v___x_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3027_, 0, v_msg_2968_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set_tag(v___x_2998_, 0);
lean_ctor_set(v___x_2998_, 0, v___x_3027_);
v___x_3029_ = v___x_2998_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3032_; 
lean_dec_ref(v_env_2973_);
lean_dec(v_declHint_2969_);
v___x_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3032_, 0, v_msg_2968_);
return v___x_3032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_3033_, lean_object* v_declHint_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3033_, v_declHint_3034_, v___y_3035_);
lean_dec(v___y_3035_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(lean_object* v_msg_3038_, lean_object* v_declHint_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v___x_3048_; lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3058_; 
v___x_3048_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3038_, v_declHint_3039_, v___y_3046_);
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3058_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3058_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3053_ = l_Lean_unknownIdentifierMessageTag;
v___x_3054_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
lean_ctor_set(v___x_3054_, 1, v_a_3049_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3054_);
v___x_3056_ = v___x_3051_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11___boxed(lean_object* v_msg_3059_, lean_object* v_declHint_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3059_, v_declHint_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object* v_ref_3070_, lean_object* v_msg_3071_, lean_object* v_declHint_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; lean_object* v_a_3082_; lean_object* v___x_3083_; 
v___x_3081_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3071_, v_declHint_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref(v___x_3081_);
v___x_3083_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3070_, v_a_3082_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_ref_3084_, lean_object* v_msg_3085_, lean_object* v_declHint_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3084_, v_msg_3085_, v_declHint_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec(v_ref_3084_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(lean_object* v_ref_3096_, lean_object* v_constName_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; uint8_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3106_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3107_ = 0;
lean_inc(v_constName_3097_);
v___x_3108_ = l_Lean_MessageData_ofConstName(v_constName_3097_, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3106_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3109_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3096_, v___x_3111_, v_constName_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_ref_3113_, lean_object* v_constName_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3113_, v_constName_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec(v_ref_3113_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_ref_3133_; lean_object* v___x_3134_; 
v_ref_3133_ = lean_ctor_get(v___y_3130_, 5);
v___x_3134_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3133_, v_constName_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(lean_object* v_constName_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v___x_3154_; lean_object* v_env_3155_; uint8_t v___x_3156_; lean_object* v___x_3157_; 
v___x_3154_ = lean_st_ref_get(v___y_3152_);
v_env_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc_ref(v_env_3155_);
lean_dec(v___x_3154_);
v___x_3156_ = 0;
lean_inc(v_constName_3145_);
v___x_3157_ = l_Lean_Environment_find_x3f(v_env_3155_, v_constName_3145_, v___x_3156_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
return v___x_3158_;
}
else
{
lean_object* v_val_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec(v_constName_3145_);
v_val_3159_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3157_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_val_3159_);
lean_dec(v___x_3157_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
lean_ctor_set_tag(v___x_3161_, 0);
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_val_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0___boxed(lean_object* v_constName_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_constName_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
return v_res_3176_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_instMonadEIO(lean_box(0));
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(lean_object* v_msg_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v_toApplicative_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3257_; 
v___x_3191_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0);
v___x_3192_ = l_StateRefT_x27_instMonad___redArg(v___x_3191_);
v_toApplicative_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; 
v_unused_3258_ = lean_ctor_get(v___x_3192_, 1);
lean_dec(v_unused_3258_);
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3257_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_toApplicative_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3257_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_toFunctor_3197_; lean_object* v_toSeq_3198_; lean_object* v_toSeqLeft_3199_; lean_object* v_toSeqRight_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3255_; 
v_toFunctor_3197_ = lean_ctor_get(v_toApplicative_3193_, 0);
v_toSeq_3198_ = lean_ctor_get(v_toApplicative_3193_, 2);
v_toSeqLeft_3199_ = lean_ctor_get(v_toApplicative_3193_, 3);
v_toSeqRight_3200_ = lean_ctor_get(v_toApplicative_3193_, 4);
v_isSharedCheck_3255_ = !lean_is_exclusive(v_toApplicative_3193_);
if (v_isSharedCheck_3255_ == 0)
{
lean_object* v_unused_3256_; 
v_unused_3256_ = lean_ctor_get(v_toApplicative_3193_, 1);
lean_dec(v_unused_3256_);
v___x_3202_ = v_toApplicative_3193_;
v_isShared_3203_ = v_isSharedCheck_3255_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_toSeqRight_3200_);
lean_inc(v_toSeqLeft_3199_);
lean_inc(v_toSeq_3198_);
lean_inc(v_toFunctor_3197_);
lean_dec(v_toApplicative_3193_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3255_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___f_3204_; lean_object* v___f_3205_; lean_object* v___f_3206_; lean_object* v___f_3207_; lean_object* v___x_3208_; lean_object* v___f_3209_; lean_object* v___f_3210_; lean_object* v___f_3211_; lean_object* v___x_3213_; 
v___f_3204_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__1));
v___f_3205_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3197_);
v___f_3206_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3206_, 0, v_toFunctor_3197_);
v___f_3207_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3207_, 0, v_toFunctor_3197_);
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___f_3206_);
lean_ctor_set(v___x_3208_, 1, v___f_3207_);
v___f_3209_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3209_, 0, v_toSeqRight_3200_);
v___f_3210_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3210_, 0, v_toSeqLeft_3199_);
v___f_3211_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3211_, 0, v_toSeq_3198_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 4, v___f_3209_);
lean_ctor_set(v___x_3202_, 3, v___f_3210_);
lean_ctor_set(v___x_3202_, 2, v___f_3211_);
lean_ctor_set(v___x_3202_, 1, v___f_3204_);
lean_ctor_set(v___x_3202_, 0, v___x_3208_);
v___x_3213_ = v___x_3202_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3208_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v___f_3204_);
lean_ctor_set(v_reuseFailAlloc_3254_, 2, v___f_3211_);
lean_ctor_set(v_reuseFailAlloc_3254_, 3, v___f_3210_);
lean_ctor_set(v_reuseFailAlloc_3254_, 4, v___f_3209_);
v___x_3213_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3215_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 1, v___f_3205_);
lean_ctor_set(v___x_3195_, 0, v___x_3213_);
v___x_3215_ = v___x_3195_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v___f_3205_);
v___x_3215_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3216_; lean_object* v_toApplicative_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3251_; 
v___x_3216_ = l_StateRefT_x27_instMonad___redArg(v___x_3215_);
v_toApplicative_3217_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v___x_3216_, 1);
lean_dec(v_unused_3252_);
v___x_3219_ = v___x_3216_;
v_isShared_3220_ = v_isSharedCheck_3251_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_toApplicative_3217_);
lean_dec(v___x_3216_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3251_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v_toFunctor_3221_; lean_object* v_toSeq_3222_; lean_object* v_toSeqLeft_3223_; lean_object* v_toSeqRight_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3249_; 
v_toFunctor_3221_ = lean_ctor_get(v_toApplicative_3217_, 0);
v_toSeq_3222_ = lean_ctor_get(v_toApplicative_3217_, 2);
v_toSeqLeft_3223_ = lean_ctor_get(v_toApplicative_3217_, 3);
v_toSeqRight_3224_ = lean_ctor_get(v_toApplicative_3217_, 4);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_toApplicative_3217_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v_toApplicative_3217_, 1);
lean_dec(v_unused_3250_);
v___x_3226_ = v_toApplicative_3217_;
v_isShared_3227_ = v_isSharedCheck_3249_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_toSeqRight_3224_);
lean_inc(v_toSeqLeft_3223_);
lean_inc(v_toSeq_3222_);
lean_inc(v_toFunctor_3221_);
lean_dec(v_toApplicative_3217_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3249_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___f_3228_; lean_object* v___f_3229_; lean_object* v___f_3230_; lean_object* v___f_3231_; lean_object* v___x_3232_; lean_object* v___f_3233_; lean_object* v___f_3234_; lean_object* v___f_3235_; lean_object* v___x_3237_; 
v___f_3228_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__3));
v___f_3229_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3221_);
v___f_3230_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3230_, 0, v_toFunctor_3221_);
v___f_3231_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3231_, 0, v_toFunctor_3221_);
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___f_3230_);
lean_ctor_set(v___x_3232_, 1, v___f_3231_);
v___f_3233_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3233_, 0, v_toSeqRight_3224_);
v___f_3234_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3234_, 0, v_toSeqLeft_3223_);
v___f_3235_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3235_, 0, v_toSeq_3222_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 4, v___f_3233_);
lean_ctor_set(v___x_3226_, 3, v___f_3234_);
lean_ctor_set(v___x_3226_, 2, v___f_3235_);
lean_ctor_set(v___x_3226_, 1, v___f_3228_);
lean_ctor_set(v___x_3226_, 0, v___x_3232_);
v___x_3237_ = v___x_3226_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v___f_3228_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v___f_3235_);
lean_ctor_set(v_reuseFailAlloc_3248_, 3, v___f_3234_);
lean_ctor_set(v_reuseFailAlloc_3248_, 4, v___f_3233_);
v___x_3237_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3239_; 
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 1, v___f_3229_);
lean_ctor_set(v___x_3219_, 0, v___x_3237_);
v___x_3239_ = v___x_3219_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v___f_3229_);
v___x_3239_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_48876__overap_3245_; lean_object* v___x_3246_; 
v___x_3240_ = l_StateRefT_x27_instMonad___redArg(v___x_3239_);
v___x_3241_ = l_ReaderT_instMonad___redArg(v___x_3240_);
v___x_3242_ = l_ReaderT_instMonad___redArg(v___x_3241_);
v___x_3243_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3244_ = l_instInhabitedOfMonad___redArg(v___x_3242_, v___x_3243_);
v___x_48876__overap_3245_ = lean_panic_fn_borrowed(v___x_3244_, v_msg_3182_);
lean_dec(v___x_3244_);
lean_inc(v___y_3189_);
lean_inc_ref(v___y_3188_);
lean_inc(v___y_3187_);
lean_inc_ref(v___y_3186_);
lean_inc(v___y_3185_);
lean_inc_ref(v___y_3184_);
lean_inc(v___y_3183_);
v___x_3246_ = lean_apply_8(v___x_48876__overap_3245_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, lean_box(0));
return v___x_3246_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___boxed(lean_object* v_msg_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v_msg_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
return v_res_3268_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__2));
v___x_3273_ = lean_unsigned_to_nat(53u);
v___x_3274_ = lean_unsigned_to_nat(62u);
v___x_3275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__1));
v___x_3276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__0));
v___x_3277_ = l_mkPanicMessageWithDecl(v___x_3276_, v___x_3275_, v___x_3274_, v___x_3273_, v___x_3272_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(size_t v_sz_3278_, size_t v_i_3279_, lean_object* v_bs_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
uint8_t v___x_3289_; 
v___x_3289_ = lean_usize_dec_lt(v_i_3279_, v_sz_3278_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; 
v___x_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3290_, 0, v_bs_3280_);
return v___x_3290_;
}
else
{
lean_object* v_v_3291_; lean_object* v___x_3292_; 
v_v_3291_ = lean_array_uget_borrowed(v_bs_3280_, v_i_3279_);
lean_inc(v_v_3291_);
v___x_3292_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_v_3291_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v___x_3294_; lean_object* v_bs_x27_3295_; lean_object* v_a_3297_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_a_3293_);
lean_dec_ref(v___x_3292_);
v___x_3294_ = lean_unsigned_to_nat(0u);
v_bs_x27_3295_ = lean_array_uset(v_bs_3280_, v_i_3279_, v___x_3294_);
if (lean_obj_tag(v_a_3293_) == 6)
{
lean_object* v_val_3302_; lean_object* v_numFields_3303_; uint8_t v___x_3304_; lean_object* v___x_3305_; 
v_val_3302_ = lean_ctor_get(v_a_3293_, 0);
lean_inc_ref(v_val_3302_);
lean_dec_ref(v_a_3293_);
v_numFields_3303_ = lean_ctor_get(v_val_3302_, 4);
lean_inc(v_numFields_3303_);
lean_dec_ref(v_val_3302_);
v___x_3304_ = 0;
v___x_3305_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3305_, 0, v_numFields_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3294_);
lean_ctor_set_uint8(v___x_3305_, sizeof(void*)*2, v___x_3304_);
v_a_3297_ = v___x_3305_;
goto v___jp_3296_;
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_dec(v_a_3293_);
v___x_3306_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3);
v___x_3307_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v___x_3306_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref(v___x_3307_);
v_a_3297_ = v_a_3308_;
goto v___jp_3296_;
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec_ref(v_bs_x27_3295_);
v_a_3309_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3307_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3307_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
v___jp_3296_:
{
size_t v___x_3298_; size_t v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = ((size_t)1ULL);
v___x_3299_ = lean_usize_add(v_i_3279_, v___x_3298_);
v___x_3300_ = lean_array_uset(v_bs_x27_3295_, v_i_3279_, v_a_3297_);
v_i_3279_ = v___x_3299_;
v_bs_3280_ = v___x_3300_;
goto _start;
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec_ref(v_bs_3280_);
v_a_3317_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3292_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3292_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___boxed(lean_object* v_sz_3325_, lean_object* v_i_3326_, lean_object* v_bs_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
size_t v_sz_boxed_3336_; size_t v_i_boxed_3337_; lean_object* v_res_3338_; 
v_sz_boxed_3336_ = lean_unbox_usize(v_sz_3325_);
lean_dec(v_sz_3325_);
v_i_boxed_3337_ = lean_unbox_usize(v_i_3326_);
lean_dec(v_i_3326_);
v_res_3338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_boxed_3336_, v_i_boxed_3337_, v_bs_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
return v_res_3338_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = lean_box(0);
v___x_3340_ = lean_unsigned_to_nat(16u);
v___x_3341_ = lean_mk_array(v___x_3340_, v___x_3339_);
return v___x_3341_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0);
v___x_3343_ = lean_unsigned_to_nat(0u);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
lean_ctor_set(v___x_3344_, 1, v___x_3342_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(lean_object* v_e_3347_, uint8_t v_alsoCasesOn_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
uint8_t v___x_3360_; 
v___x_3360_ = l_Lean_Expr_isApp(v_e_3347_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
lean_dec_ref(v_e_3347_);
v___x_3361_ = lean_box(0);
v___x_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
return v___x_3362_;
}
else
{
lean_object* v___x_3363_; 
v___x_3363_ = l_Lean_Expr_getAppFn(v_e_3347_);
if (lean_obj_tag(v___x_3363_) == 4)
{
lean_object* v_declName_3364_; lean_object* v_us_3365_; lean_object* v___x_3366_; lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3521_; 
v_declName_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc_n(v_declName_3364_, 2);
v_us_3365_ = lean_ctor_get(v___x_3363_, 1);
lean_inc(v_us_3365_);
lean_dec_ref(v___x_3363_);
v___x_3366_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3364_, v___y_3355_);
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3521_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3521_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
if (lean_obj_tag(v_a_3367_) == 1)
{
lean_object* v_val_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3413_; 
v_val_3371_ = lean_ctor_get(v_a_3367_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_a_3367_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3373_ = v_a_3367_;
v_isShared_3374_ = v_isSharedCheck_3413_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_val_3371_);
lean_dec(v_a_3367_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3413_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v_dummy_3375_; lean_object* v_nargs_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v_args_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v_dummy_3375_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_3376_ = l_Lean_Expr_getAppNumArgs(v_e_3347_);
lean_inc(v_nargs_3376_);
v___x_3377_ = lean_mk_array(v_nargs_3376_, v_dummy_3375_);
v___x_3378_ = lean_unsigned_to_nat(1u);
v___x_3379_ = lean_nat_sub(v_nargs_3376_, v___x_3378_);
lean_dec(v_nargs_3376_);
v_args_3380_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3347_, v___x_3377_, v___x_3379_);
v___x_3381_ = lean_array_get_size(v_args_3380_);
v___x_3382_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_3371_);
v___x_3383_ = lean_nat_dec_lt(v___x_3381_, v___x_3382_);
lean_dec(v___x_3382_);
if (v___x_3383_ == 0)
{
lean_object* v_numParams_3384_; lean_object* v_numDiscrs_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3404_; 
v_numParams_3384_ = lean_ctor_get(v_val_3371_, 0);
v_numDiscrs_3385_ = lean_ctor_get(v_val_3371_, 1);
v___x_3386_ = lean_array_mk(v_us_3365_);
v___x_3387_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3384_);
v___x_3388_ = l_Array_extract___redArg(v_args_3380_, v___x_3387_, v_numParams_3384_);
v___x_3389_ = l_Lean_instInhabitedExpr;
v___x_3390_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3371_);
v___x_3391_ = lean_array_get(v___x_3389_, v_args_3380_, v___x_3390_);
lean_dec(v___x_3390_);
v___x_3392_ = lean_nat_add(v_numParams_3384_, v___x_3378_);
v___x_3393_ = lean_nat_add(v___x_3392_, v_numDiscrs_3385_);
lean_inc(v___x_3393_);
lean_inc_ref_n(v_args_3380_, 2);
v___x_3394_ = l_Array_toSubarray___redArg(v_args_3380_, v___x_3392_, v___x_3393_);
v___x_3395_ = l_Subarray_copy___redArg(v___x_3394_);
v___x_3396_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3371_);
v___x_3397_ = lean_nat_add(v___x_3393_, v___x_3396_);
lean_dec(v___x_3396_);
lean_inc(v___x_3397_);
v___x_3398_ = l_Array_toSubarray___redArg(v_args_3380_, v___x_3393_, v___x_3397_);
v___x_3399_ = l_Subarray_copy___redArg(v___x_3398_);
v___x_3400_ = l_Array_toSubarray___redArg(v_args_3380_, v___x_3397_, v___x_3381_);
v___x_3401_ = l_Subarray_copy___redArg(v___x_3400_);
v___x_3402_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3402_, 0, v_val_3371_);
lean_ctor_set(v___x_3402_, 1, v_declName_3364_);
lean_ctor_set(v___x_3402_, 2, v___x_3386_);
lean_ctor_set(v___x_3402_, 3, v___x_3388_);
lean_ctor_set(v___x_3402_, 4, v___x_3391_);
lean_ctor_set(v___x_3402_, 5, v___x_3395_);
lean_ctor_set(v___x_3402_, 6, v___x_3399_);
lean_ctor_set(v___x_3402_, 7, v___x_3401_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3402_);
v___x_3404_ = v___x_3373_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3406_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3404_);
v___x_3406_ = v___x_3369_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3404_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3411_; 
lean_dec_ref(v_args_3380_);
lean_del_object(v___x_3373_);
lean_dec(v_val_3371_);
lean_dec(v_us_3365_);
lean_dec(v_declName_3364_);
v___x_3409_ = lean_box(0);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3409_);
v___x_3411_ = v___x_3369_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
else
{
lean_object* v___x_3414_; 
lean_del_object(v___x_3369_);
lean_dec(v_a_3367_);
v___x_3414_ = lean_st_ref_get(v___y_3355_);
if (v_alsoCasesOn_3348_ == 0)
{
lean_dec(v___x_3414_);
lean_dec(v_us_3365_);
lean_dec(v_declName_3364_);
lean_dec_ref(v_e_3347_);
goto v___jp_3357_;
}
else
{
lean_object* v_env_3415_; uint8_t v___x_3416_; 
v_env_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc_ref(v_env_3415_);
lean_dec(v___x_3414_);
lean_inc(v_declName_3364_);
v___x_3416_ = l_Lean_isCasesOnRecursor(v_env_3415_, v_declName_3364_);
if (v___x_3416_ == 0)
{
lean_dec(v_us_3365_);
lean_dec(v_declName_3364_);
lean_dec_ref(v_e_3347_);
goto v___jp_3357_;
}
else
{
lean_object* v_indName_3417_; lean_object* v___x_3418_; 
v_indName_3417_ = l_Lean_Name_getPrefix(v_declName_3364_);
v___x_3418_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_indName_3417_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3512_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3512_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3512_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
if (lean_obj_tag(v_a_3419_) == 5)
{
lean_object* v_val_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3507_; 
v_val_3423_ = lean_ctor_get(v_a_3419_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_a_3419_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3425_ = v_a_3419_;
v_isShared_3426_ = v_isSharedCheck_3507_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_val_3423_);
lean_dec(v_a_3419_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3507_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v_toConstantVal_3427_; lean_object* v_numParams_3428_; lean_object* v_numIndices_3429_; lean_object* v_ctors_3430_; lean_object* v_nargs_3431_; lean_object* v_dummy_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v_args_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; uint8_t v___x_3443_; 
v_toConstantVal_3427_ = lean_ctor_get(v_val_3423_, 0);
lean_inc_ref(v_toConstantVal_3427_);
v_numParams_3428_ = lean_ctor_get(v_val_3423_, 1);
lean_inc(v_numParams_3428_);
v_numIndices_3429_ = lean_ctor_get(v_val_3423_, 2);
lean_inc(v_numIndices_3429_);
v_ctors_3430_ = lean_ctor_get(v_val_3423_, 4);
lean_inc(v_ctors_3430_);
v_nargs_3431_ = l_Lean_Expr_getAppNumArgs(v_e_3347_);
v_dummy_3432_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_3431_);
v___x_3433_ = lean_mk_array(v_nargs_3431_, v_dummy_3432_);
v___x_3434_ = lean_unsigned_to_nat(1u);
v___x_3435_ = lean_nat_sub(v_nargs_3431_, v___x_3434_);
lean_dec(v_nargs_3431_);
v_args_3436_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3347_, v___x_3433_, v___x_3435_);
v___x_3437_ = lean_nat_add(v_numParams_3428_, v___x_3434_);
v___x_3438_ = lean_nat_add(v___x_3437_, v_numIndices_3429_);
v___x_3439_ = lean_nat_add(v___x_3438_, v___x_3434_);
lean_dec(v___x_3438_);
v___x_3440_ = l_Lean_InductiveVal_numCtors(v_val_3423_);
lean_dec_ref(v_val_3423_);
v___x_3441_ = lean_nat_add(v___x_3439_, v___x_3440_);
lean_dec(v___x_3440_);
v___x_3442_ = lean_array_get_size(v_args_3436_);
v___x_3443_ = lean_nat_dec_le(v___x_3441_, v___x_3442_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
lean_dec(v___x_3441_);
lean_dec(v___x_3439_);
lean_dec(v___x_3437_);
lean_dec_ref(v_args_3436_);
lean_dec(v_ctors_3430_);
lean_dec(v_numIndices_3429_);
lean_dec(v_numParams_3428_);
lean_dec_ref(v_toConstantVal_3427_);
lean_del_object(v___x_3425_);
lean_dec(v_us_3365_);
lean_dec(v_declName_3364_);
v___x_3444_ = lean_box(0);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3444_);
v___x_3446_ = v___x_3421_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
else
{
lean_object* v___x_3448_; lean_object* v_params_3449_; lean_object* v___x_3450_; lean_object* v_motive_3451_; lean_object* v_discrs_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v_discrInfos_3455_; lean_object* v_alts_3456_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v_lower_3498_; lean_object* v_upper_3499_; uint8_t v___x_3506_; 
lean_del_object(v___x_3421_);
v___x_3448_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3428_);
lean_inc_ref_n(v_args_3436_, 3);
v_params_3449_ = l_Array_toSubarray___redArg(v_args_3436_, v___x_3448_, v_numParams_3428_);
v___x_3450_ = l_Lean_instInhabitedExpr;
v_motive_3451_ = lean_array_get(v___x_3450_, v_args_3436_, v_numParams_3428_);
lean_dec(v_numParams_3428_);
lean_inc(v___x_3439_);
v_discrs_3452_ = l_Array_toSubarray___redArg(v_args_3436_, v___x_3437_, v___x_3439_);
v___x_3453_ = lean_nat_add(v_numIndices_3429_, v___x_3434_);
lean_dec(v_numIndices_3429_);
v___x_3454_ = lean_box(0);
v_discrInfos_3455_ = lean_mk_array(v___x_3453_, v___x_3454_);
lean_inc(v___x_3441_);
v_alts_3456_ = l_Array_toSubarray___redArg(v_args_3436_, v___x_3439_, v___x_3441_);
v___x_3506_ = lean_nat_dec_le(v___x_3441_, v___x_3448_);
if (v___x_3506_ == 0)
{
v_lower_3498_ = v___x_3441_;
v_upper_3499_ = v___x_3442_;
goto v___jp_3497_;
}
else
{
lean_dec(v___x_3441_);
v_lower_3498_ = v___x_3448_;
v_upper_3499_ = v___x_3442_;
goto v___jp_3497_;
}
v___jp_3457_:
{
lean_object* v___x_3460_; size_t v_sz_3461_; size_t v___x_3462_; lean_object* v___x_3463_; 
v___x_3460_ = lean_array_mk(v_ctors_3430_);
v_sz_3461_ = lean_array_size(v___x_3460_);
v___x_3462_ = ((size_t)0ULL);
v___x_3463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_3461_, v___x_3462_, v___x_3460_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3488_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3466_ = v___x_3463_;
v_isShared_3467_ = v_isSharedCheck_3488_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3463_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3488_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v_start_3468_; lean_object* v_stop_3469_; lean_object* v_start_3470_; lean_object* v_stop_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3483_; 
v_start_3468_ = lean_ctor_get(v_params_3449_, 1);
lean_inc(v_start_3468_);
v_stop_3469_ = lean_ctor_get(v_params_3449_, 2);
lean_inc(v_stop_3469_);
v_start_3470_ = lean_ctor_get(v_discrs_3452_, 1);
lean_inc(v_start_3470_);
v_stop_3471_ = lean_ctor_get(v_discrs_3452_, 2);
lean_inc(v_stop_3471_);
v___x_3472_ = lean_nat_sub(v_stop_3469_, v_start_3468_);
lean_dec(v_start_3468_);
lean_dec(v_stop_3469_);
v___x_3473_ = lean_nat_sub(v_stop_3471_, v_start_3470_);
lean_dec(v_start_3470_);
lean_dec(v_stop_3471_);
v___x_3474_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1);
v___x_3475_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3472_);
lean_ctor_set(v___x_3475_, 1, v___x_3473_);
lean_ctor_set(v___x_3475_, 2, v_a_3464_);
lean_ctor_set(v___x_3475_, 3, v___y_3459_);
lean_ctor_set(v___x_3475_, 4, v_discrInfos_3455_);
lean_ctor_set(v___x_3475_, 5, v___x_3474_);
v___x_3476_ = lean_array_mk(v_us_3365_);
v___x_3477_ = l_Subarray_copy___redArg(v_params_3449_);
v___x_3478_ = l_Subarray_copy___redArg(v_discrs_3452_);
v___x_3479_ = l_Subarray_copy___redArg(v_alts_3456_);
v___x_3480_ = l_Subarray_copy___redArg(v___y_3458_);
v___x_3481_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3475_);
lean_ctor_set(v___x_3481_, 1, v_declName_3364_);
lean_ctor_set(v___x_3481_, 2, v___x_3476_);
lean_ctor_set(v___x_3481_, 3, v___x_3477_);
lean_ctor_set(v___x_3481_, 4, v_motive_3451_);
lean_ctor_set(v___x_3481_, 5, v___x_3478_);
lean_ctor_set(v___x_3481_, 6, v___x_3479_);
lean_ctor_set(v___x_3481_, 7, v___x_3480_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set_tag(v___x_3425_, 1);
lean_ctor_set(v___x_3425_, 0, v___x_3481_);
v___x_3483_ = v___x_3425_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
lean_object* v___x_3485_; 
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v___x_3483_);
v___x_3485_ = v___x_3466_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v_alts_3456_);
lean_dec_ref(v_discrInfos_3455_);
lean_dec_ref(v_discrs_3452_);
lean_dec(v_motive_3451_);
lean_dec_ref(v_params_3449_);
lean_del_object(v___x_3425_);
lean_dec(v_us_3365_);
lean_dec(v_declName_3364_);
v_a_3489_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3463_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3463_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
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
v___jp_3497_:
{
lean_object* v_levelParams_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v_levelParams_3500_ = lean_ctor_get(v_toConstantVal_3427_, 1);
lean_inc(v_levelParams_3500_);
lean_dec_ref(v_toConstantVal_3427_);
v___x_3501_ = l_Array_toSubarray___redArg(v_args_3436_, v_lower_3498_, v_upper_3499_);
v___x_3502_ = l_List_lengthTR___redArg(v_levelParams_3500_);
lean_dec(v_levelParams_3500_);
v___x_3503_ = l_List_lengthTR___redArg(v_us_3365_);
v___x_3504_ = lean_nat_dec_eq(v___x_3502_, v___x_3503_);
lean_dec(v___x_3503_);
lean_dec(v___x_3502_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
v___x_3505_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__2));
v___y_3458_ = v___x_3501_;
v___y_3459_ = v___x_3505_;
goto v___jp_3457_;
}
else
{
v___y_3458_ = v___x_3501_;
v___y_3459_ = v___x_3454_;
goto v___jp_3457_;
}
}
}
}
}
else
{
lean_object* v___x_3508_; lean_object* v___x_3510_; 
lean_dec(v_a_3419_);
lean_dec(v_us_3365_);
lean_dec(v_declName_3364_);
lean_dec_ref(v_e_3347_);
v___x_3508_ = lean_box(0);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3508_);
v___x_3510_ = v___x_3421_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec(v_us_3365_);
lean_dec(v_declName_3364_);
lean_dec_ref(v_e_3347_);
v_a_3513_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3418_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3418_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
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
lean_dec_ref(v___x_3363_);
lean_dec_ref(v_e_3347_);
goto v___jp_3357_;
}
}
v___jp_3357_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = lean_box(0);
v___x_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
return v___x_3359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___boxed(lean_object* v_e_3522_, lean_object* v_alsoCasesOn_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
uint8_t v_alsoCasesOn_boxed_3532_; lean_object* v_res_3533_; 
v_alsoCasesOn_boxed_3532_ = lean_unbox(v_alsoCasesOn_3523_);
v_res_3533_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3522_, v_alsoCasesOn_boxed_3532_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
return v_res_3533_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__1));
v___x_3538_ = l_Lean_stringToMessageData(v___x_3537_);
return v___x_3538_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = lean_unsigned_to_nat(1u);
v___x_3540_ = l_Lean_Expr_bvar___override(v___x_3539_);
return v___x_3540_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3543_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__5));
v___x_3544_ = lean_unsigned_to_nat(2u);
v___x_3545_ = lean_unsigned_to_nat(181u);
v___x_3546_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__4));
v___x_3547_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_3548_ = l_mkPanicMessageWithDecl(v___x_3547_, v___x_3546_, v___x_3545_, v___x_3544_, v___x_3543_);
return v___x_3548_;
}
}
static uint64_t _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7(void){
_start:
{
uint8_t v___x_3549_; uint64_t v___x_3550_; 
v___x_3549_ = 0;
v___x_3550_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(lean_object* v_e_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_e_3560_; uint8_t v___x_3561_; lean_object* v___x_3562_; 
v_e_3560_ = l_Lean_Expr_headBeta(v_e_3551_);
v___x_3561_ = 1;
v___x_3562_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3560_, v___x_3561_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3852_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3565_ = v___x_3562_;
v_isShared_3566_ = v_isSharedCheck_3852_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3852_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
if (lean_obj_tag(v_a_3563_) == 1)
{
lean_object* v_val_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3847_; 
v_val_3567_ = lean_ctor_get(v_a_3563_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_a_3563_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3569_ = v_a_3563_;
v_isShared_3570_ = v_isSharedCheck_3847_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_val_3567_);
lean_dec(v_a_3563_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3847_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v_toMatcherInfo_3571_; lean_object* v_matcherName_3572_; lean_object* v_params_3573_; lean_object* v_motive_3574_; lean_object* v_discrs_3575_; lean_object* v_alts_3576_; lean_object* v_remaining_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; uint8_t v___x_3580_; 
v_toMatcherInfo_3571_ = lean_ctor_get(v_val_3567_, 0);
lean_inc_ref(v_toMatcherInfo_3571_);
v_matcherName_3572_ = lean_ctor_get(v_val_3567_, 1);
lean_inc(v_matcherName_3572_);
v_params_3573_ = lean_ctor_get(v_val_3567_, 3);
lean_inc_ref(v_params_3573_);
v_motive_3574_ = lean_ctor_get(v_val_3567_, 4);
lean_inc_ref(v_motive_3574_);
v_discrs_3575_ = lean_ctor_get(v_val_3567_, 5);
lean_inc_ref(v_discrs_3575_);
v_alts_3576_ = lean_ctor_get(v_val_3567_, 6);
lean_inc_ref(v_alts_3576_);
v_remaining_3577_ = lean_ctor_get(v_val_3567_, 7);
lean_inc_ref(v_remaining_3577_);
v___x_3578_ = lean_unsigned_to_nat(0u);
v___x_3579_ = lean_array_get_size(v_remaining_3577_);
v___x_3580_ = lean_nat_dec_lt(v___x_3578_, v___x_3579_);
if (v___x_3580_ == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
lean_dec(v_val_3567_);
v___x_3581_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3581_);
v___x_3583_ = v___x_3565_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
else
{
lean_object* v___x_3585_; uint8_t v___x_3586_; 
v___x_3585_ = lean_array_fget_borrowed(v_remaining_3577_, v___x_3578_);
v___x_3586_ = l_Lean_Expr_isLambda(v___x_3585_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3589_; 
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
lean_dec(v_val_3567_);
v___x_3587_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3587_);
v___x_3589_ = v___x_3565_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
else
{
lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3591_ = l_Lean_Expr_bindingBody_x21(v___x_3585_);
v___x_3592_ = l_Lean_Expr_isLambda(v___x_3591_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; lean_object* v___x_3595_; 
lean_dec_ref(v___x_3591_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
lean_dec(v_val_3567_);
v___x_3593_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3593_);
v___x_3595_ = v___x_3565_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3593_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
else
{
lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3597_ = l_Lean_Expr_bindingBody_x21(v___x_3591_);
lean_dec_ref(v___x_3591_);
v___x_3598_ = l_Lean_Expr_isApp(v___x_3597_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; lean_object* v___x_3601_; 
lean_dec_ref(v___x_3597_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
lean_dec(v_val_3567_);
v___x_3599_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3599_);
v___x_3601_ = v___x_3565_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
else
{
uint8_t v___x_3603_; 
v___x_3603_ = lean_expr_has_loose_bvar(v___x_3597_, v___x_3578_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v_a_3607_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___x_3604_ = l_Lean_Expr_appArg_x21(v___x_3597_);
v___x_3605_ = lean_unsigned_to_nat(1u);
v___x_3661_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3);
v___x_3662_ = lean_expr_eqv(v___x_3604_, v___x_3661_);
lean_dec_ref(v___x_3604_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3665_; 
lean_dec_ref(v___x_3597_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
lean_dec(v_val_3567_);
v___x_3663_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3663_);
v___x_3665_ = v___x_3565_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
else
{
lean_object* v___x_3667_; uint8_t v___x_3668_; 
v___x_3667_ = l_Lean_Expr_appFn_x21(v___x_3597_);
lean_dec_ref(v___x_3597_);
v___x_3668_ = lean_expr_has_loose_bvar(v___x_3667_, v___x_3605_);
if (v___x_3668_ == 0)
{
lean_object* v___x_3669_; 
lean_del_object(v___x_3565_);
lean_inc(v_a_3558_);
lean_inc_ref(v_a_3557_);
lean_inc(v_a_3556_);
lean_inc_ref(v_a_3555_);
lean_inc_ref(v___x_3667_);
v___x_3669_ = lean_infer_type(v___x_3667_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3671_; uint8_t v_foApprox_3672_; uint8_t v_ctxApprox_3673_; uint8_t v_quasiPatternApprox_3674_; uint8_t v_constApprox_3675_; uint8_t v_isDefEqStuckEx_3676_; uint8_t v_unificationHints_3677_; uint8_t v_proofIrrelevance_3678_; uint8_t v_assignSyntheticOpaque_3679_; uint8_t v_offsetCnstrs_3680_; uint8_t v_etaStruct_3681_; uint8_t v_univApprox_3682_; uint8_t v_iota_3683_; uint8_t v_beta_3684_; uint8_t v_proj_3685_; uint8_t v_zeta_3686_; uint8_t v_zetaDelta_3687_; uint8_t v_zetaUnused_3688_; uint8_t v_zetaHave_3689_; uint8_t v_trackZetaDelta_3690_; lean_object* v_zetaDeltaSet_3691_; lean_object* v_lctx_3692_; lean_object* v_localInstances_3693_; lean_object* v_defEqCtx_x3f_3694_; lean_object* v_synthPendingDepth_3695_; lean_object* v_canUnfold_x3f_3696_; uint8_t v_univApprox_3697_; uint8_t v_inTypeClassResolution_3698_; uint8_t v_cacheInferType_3699_; uint8_t v___x_3700_; lean_object* v_a_3702_; lean_object* v_config_3811_; uint64_t v___x_3812_; uint64_t v___x_3813_; uint64_t v___x_3814_; uint64_t v___x_3815_; uint64_t v___x_3816_; uint64_t v_key_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref(v___x_3669_);
v___x_3671_ = l_Lean_Meta_Context_config(v_a_3555_);
v_foApprox_3672_ = lean_ctor_get_uint8(v___x_3671_, 0);
v_ctxApprox_3673_ = lean_ctor_get_uint8(v___x_3671_, 1);
v_quasiPatternApprox_3674_ = lean_ctor_get_uint8(v___x_3671_, 2);
v_constApprox_3675_ = lean_ctor_get_uint8(v___x_3671_, 3);
v_isDefEqStuckEx_3676_ = lean_ctor_get_uint8(v___x_3671_, 4);
v_unificationHints_3677_ = lean_ctor_get_uint8(v___x_3671_, 5);
v_proofIrrelevance_3678_ = lean_ctor_get_uint8(v___x_3671_, 6);
v_assignSyntheticOpaque_3679_ = lean_ctor_get_uint8(v___x_3671_, 7);
v_offsetCnstrs_3680_ = lean_ctor_get_uint8(v___x_3671_, 8);
v_etaStruct_3681_ = lean_ctor_get_uint8(v___x_3671_, 10);
v_univApprox_3682_ = lean_ctor_get_uint8(v___x_3671_, 11);
v_iota_3683_ = lean_ctor_get_uint8(v___x_3671_, 12);
v_beta_3684_ = lean_ctor_get_uint8(v___x_3671_, 13);
v_proj_3685_ = lean_ctor_get_uint8(v___x_3671_, 14);
v_zeta_3686_ = lean_ctor_get_uint8(v___x_3671_, 15);
v_zetaDelta_3687_ = lean_ctor_get_uint8(v___x_3671_, 16);
v_zetaUnused_3688_ = lean_ctor_get_uint8(v___x_3671_, 17);
v_zetaHave_3689_ = lean_ctor_get_uint8(v___x_3671_, 18);
v_trackZetaDelta_3690_ = lean_ctor_get_uint8(v_a_3555_, sizeof(void*)*7);
v_zetaDeltaSet_3691_ = lean_ctor_get(v_a_3555_, 1);
v_lctx_3692_ = lean_ctor_get(v_a_3555_, 2);
v_localInstances_3693_ = lean_ctor_get(v_a_3555_, 3);
v_defEqCtx_x3f_3694_ = lean_ctor_get(v_a_3555_, 4);
v_synthPendingDepth_3695_ = lean_ctor_get(v_a_3555_, 5);
v_canUnfold_x3f_3696_ = lean_ctor_get(v_a_3555_, 6);
v_univApprox_3697_ = lean_ctor_get_uint8(v_a_3555_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3698_ = lean_ctor_get_uint8(v_a_3555_, sizeof(void*)*7 + 2);
v_cacheInferType_3699_ = lean_ctor_get_uint8(v_a_3555_, sizeof(void*)*7 + 3);
v___x_3700_ = 0;
v_config_3811_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_config_3811_, 0, v_foApprox_3672_);
lean_ctor_set_uint8(v_config_3811_, 1, v_ctxApprox_3673_);
lean_ctor_set_uint8(v_config_3811_, 2, v_quasiPatternApprox_3674_);
lean_ctor_set_uint8(v_config_3811_, 3, v_constApprox_3675_);
lean_ctor_set_uint8(v_config_3811_, 4, v_isDefEqStuckEx_3676_);
lean_ctor_set_uint8(v_config_3811_, 5, v_unificationHints_3677_);
lean_ctor_set_uint8(v_config_3811_, 6, v_proofIrrelevance_3678_);
lean_ctor_set_uint8(v_config_3811_, 7, v_assignSyntheticOpaque_3679_);
lean_ctor_set_uint8(v_config_3811_, 8, v_offsetCnstrs_3680_);
lean_ctor_set_uint8(v_config_3811_, 9, v___x_3700_);
lean_ctor_set_uint8(v_config_3811_, 10, v_etaStruct_3681_);
lean_ctor_set_uint8(v_config_3811_, 11, v_univApprox_3682_);
lean_ctor_set_uint8(v_config_3811_, 12, v_iota_3683_);
lean_ctor_set_uint8(v_config_3811_, 13, v_beta_3684_);
lean_ctor_set_uint8(v_config_3811_, 14, v_proj_3685_);
lean_ctor_set_uint8(v_config_3811_, 15, v_zeta_3686_);
lean_ctor_set_uint8(v_config_3811_, 16, v_zetaDelta_3687_);
lean_ctor_set_uint8(v_config_3811_, 17, v_zetaUnused_3688_);
lean_ctor_set_uint8(v_config_3811_, 18, v_zetaHave_3689_);
v___x_3812_ = l_Lean_Meta_Context_configKey(v_a_3555_);
v___x_3813_ = 2ULL;
v___x_3814_ = lean_uint64_shift_right(v___x_3812_, v___x_3813_);
v___x_3815_ = lean_uint64_shift_left(v___x_3814_, v___x_3813_);
v___x_3816_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7);
v_key_3817_ = lean_uint64_lor(v___x_3815_, v___x_3816_);
v___x_3818_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3818_, 0, v_config_3811_);
lean_ctor_set_uint64(v___x_3818_, sizeof(void*)*1, v_key_3817_);
lean_inc(v_canUnfold_x3f_3696_);
lean_inc(v_synthPendingDepth_3695_);
lean_inc(v_defEqCtx_x3f_3694_);
lean_inc_ref(v_localInstances_3693_);
lean_inc_ref(v_lctx_3692_);
lean_inc(v_zetaDeltaSet_3691_);
v___x_3819_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
lean_ctor_set(v___x_3819_, 1, v_zetaDeltaSet_3691_);
lean_ctor_set(v___x_3819_, 2, v_lctx_3692_);
lean_ctor_set(v___x_3819_, 3, v_localInstances_3693_);
lean_ctor_set(v___x_3819_, 4, v_defEqCtx_x3f_3694_);
lean_ctor_set(v___x_3819_, 5, v_synthPendingDepth_3695_);
lean_ctor_set(v___x_3819_, 6, v_canUnfold_x3f_3696_);
lean_ctor_set_uint8(v___x_3819_, sizeof(void*)*7, v_trackZetaDelta_3690_);
lean_ctor_set_uint8(v___x_3819_, sizeof(void*)*7 + 1, v_univApprox_3697_);
lean_ctor_set_uint8(v___x_3819_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3698_);
lean_ctor_set_uint8(v___x_3819_, sizeof(void*)*7 + 3, v_cacheInferType_3699_);
v___x_3820_ = l_Lean_Meta_whnfForall(v_a_3670_, v___x_3819_, v_a_3556_, v_a_3557_, v_a_3558_);
lean_dec_ref(v___x_3819_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref(v___x_3820_);
v_a_3702_ = v_a_3821_;
goto v___jp_3701_;
}
else
{
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3822_; 
v_a_3822_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3822_);
lean_dec_ref(v___x_3820_);
v_a_3702_ = v_a_3822_;
goto v___jp_3701_;
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref(v___x_3671_);
lean_dec_ref(v___x_3667_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
lean_dec(v_val_3567_);
v_a_3823_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3820_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3820_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
v___jp_3701_:
{
uint8_t v___x_3703_; 
v___x_3703_ = l_Lean_Expr_isForall(v_a_3702_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
lean_dec_ref(v_a_3702_);
lean_dec_ref(v___x_3671_);
lean_dec_ref(v___x_3667_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
lean_dec(v_val_3567_);
v___x_3704_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6);
v___x_3705_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v___x_3704_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
return v___x_3705_;
}
else
{
lean_object* v___x_3706_; 
v___x_3706_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_val_3567_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3802_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3709_ = v___x_3706_;
v_isShared_3710_ = v_isSharedCheck_3802_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3706_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3802_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
if (lean_obj_tag(v_a_3707_) == 1)
{
lean_object* v_val_3711_; uint8_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___f_3716_; lean_object* v___x_3717_; 
lean_del_object(v___x_3709_);
v_val_3711_ = lean_ctor_get(v_a_3707_, 0);
lean_inc(v_val_3711_);
lean_dec_ref(v_a_3707_);
v___x_3712_ = 0;
v___x_3713_ = lean_box(v___x_3712_);
v___x_3714_ = lean_box(v___x_3668_);
v___x_3715_ = lean_box(v___x_3561_);
v___f_3716_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3716_, 0, v___x_3713_);
lean_closure_set(v___f_3716_, 1, v___x_3714_);
lean_closure_set(v___f_3716_, 2, v___x_3715_);
v___x_3717_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_motive_3574_, v___f_3716_, v___x_3668_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
v___x_3719_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_3572_, v_toMatcherInfo_3571_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; uint8_t v_foApprox_3721_; uint8_t v_ctxApprox_3722_; uint8_t v_quasiPatternApprox_3723_; uint8_t v_constApprox_3724_; uint8_t v_isDefEqStuckEx_3725_; uint8_t v_unificationHints_3726_; uint8_t v_proofIrrelevance_3727_; uint8_t v_assignSyntheticOpaque_3728_; uint8_t v_offsetCnstrs_3729_; uint8_t v_etaStruct_3730_; uint8_t v_univApprox_3731_; uint8_t v_iota_3732_; uint8_t v_beta_3733_; uint8_t v_proj_3734_; uint8_t v_zeta_3735_; uint8_t v_zetaDelta_3736_; uint8_t v_zetaUnused_3737_; uint8_t v_zetaHave_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3781_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref(v___x_3719_);
v_foApprox_3721_ = lean_ctor_get_uint8(v___x_3671_, 0);
v_ctxApprox_3722_ = lean_ctor_get_uint8(v___x_3671_, 1);
v_quasiPatternApprox_3723_ = lean_ctor_get_uint8(v___x_3671_, 2);
v_constApprox_3724_ = lean_ctor_get_uint8(v___x_3671_, 3);
v_isDefEqStuckEx_3725_ = lean_ctor_get_uint8(v___x_3671_, 4);
v_unificationHints_3726_ = lean_ctor_get_uint8(v___x_3671_, 5);
v_proofIrrelevance_3727_ = lean_ctor_get_uint8(v___x_3671_, 6);
v_assignSyntheticOpaque_3728_ = lean_ctor_get_uint8(v___x_3671_, 7);
v_offsetCnstrs_3729_ = lean_ctor_get_uint8(v___x_3671_, 8);
v_etaStruct_3730_ = lean_ctor_get_uint8(v___x_3671_, 10);
v_univApprox_3731_ = lean_ctor_get_uint8(v___x_3671_, 11);
v_iota_3732_ = lean_ctor_get_uint8(v___x_3671_, 12);
v_beta_3733_ = lean_ctor_get_uint8(v___x_3671_, 13);
v_proj_3734_ = lean_ctor_get_uint8(v___x_3671_, 14);
v_zeta_3735_ = lean_ctor_get_uint8(v___x_3671_, 15);
v_zetaDelta_3736_ = lean_ctor_get_uint8(v___x_3671_, 16);
v_zetaUnused_3737_ = lean_ctor_get_uint8(v___x_3671_, 17);
v_zetaHave_3738_ = lean_ctor_get_uint8(v___x_3671_, 18);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3740_ = v___x_3671_;
v_isShared_3741_ = v_isSharedCheck_3781_;
goto v_resetjp_3739_;
}
else
{
lean_dec(v___x_3671_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3781_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; size_t v_sz_3756_; lean_object* v_config_3758_; 
v___x_3742_ = l_Lean_Expr_bindingDomain_x21(v_a_3702_);
v___x_3743_ = l_Lean_Expr_bindingName_x21(v_a_3702_);
v___x_3744_ = l_Lean_Expr_bindingBody_x21(v_a_3702_);
lean_dec_ref(v_a_3702_);
lean_inc_ref(v___x_3742_);
v___x_3745_ = l_Lean_Expr_lam___override(v___x_3743_, v___x_3742_, v___x_3744_, v___x_3712_);
v___x_3746_ = lean_unsigned_to_nat(5u);
v___x_3747_ = lean_mk_empty_array_with_capacity(v___x_3746_);
v___x_3748_ = lean_array_push(v___x_3747_, v_val_3711_);
v___x_3749_ = lean_array_push(v___x_3748_, v___x_3742_);
v___x_3750_ = lean_array_push(v___x_3749_, v___x_3745_);
v___x_3751_ = lean_array_push(v___x_3750_, v___x_3667_);
v___x_3752_ = lean_array_push(v___x_3751_, v_a_3718_);
v___x_3753_ = l_Array_append___redArg(v_params_3573_, v___x_3752_);
lean_dec_ref(v___x_3752_);
v___x_3754_ = l_Array_append___redArg(v___x_3753_, v_discrs_3575_);
lean_dec_ref(v_discrs_3575_);
v___x_3755_ = l_Array_append___redArg(v___x_3754_, v_alts_3576_);
lean_dec_ref(v_alts_3576_);
v_sz_3756_ = lean_array_size(v___x_3755_);
if (v_isShared_3741_ == 0)
{
v_config_3758_ = v___x_3740_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 0, v_foApprox_3721_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 1, v_ctxApprox_3722_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 2, v_quasiPatternApprox_3723_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 3, v_constApprox_3724_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 4, v_isDefEqStuckEx_3725_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 5, v_unificationHints_3726_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 6, v_proofIrrelevance_3727_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 7, v_assignSyntheticOpaque_3728_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 8, v_offsetCnstrs_3729_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 10, v_etaStruct_3730_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 11, v_univApprox_3731_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 12, v_iota_3732_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 13, v_beta_3733_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 14, v_proj_3734_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 15, v_zeta_3735_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 16, v_zetaDelta_3736_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 17, v_zetaUnused_3737_);
lean_ctor_set_uint8(v_reuseFailAlloc_3780_, 18, v_zetaHave_3738_);
v_config_3758_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
uint64_t v___x_3759_; uint64_t v___x_3760_; uint64_t v___x_3761_; size_t v___x_3762_; lean_object* v___x_3763_; uint64_t v___x_3764_; uint64_t v___x_3765_; uint64_t v_key_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
lean_ctor_set_uint8(v_config_3758_, 9, v___x_3700_);
v___x_3759_ = l_Lean_Meta_Context_configKey(v_a_3555_);
v___x_3760_ = 2ULL;
v___x_3761_ = lean_uint64_shift_right(v___x_3759_, v___x_3760_);
v___x_3762_ = ((size_t)0ULL);
v___x_3763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_3756_, v___x_3762_, v___x_3755_);
v___x_3764_ = lean_uint64_shift_left(v___x_3761_, v___x_3760_);
v___x_3765_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7);
v_key_3766_ = lean_uint64_lor(v___x_3764_, v___x_3765_);
v___x_3767_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3767_, 0, v_config_3758_);
lean_ctor_set_uint64(v___x_3767_, sizeof(void*)*1, v_key_3766_);
lean_inc(v_canUnfold_x3f_3696_);
lean_inc(v_synthPendingDepth_3695_);
lean_inc(v_defEqCtx_x3f_3694_);
lean_inc_ref(v_localInstances_3693_);
lean_inc_ref(v_lctx_3692_);
lean_inc(v_zetaDeltaSet_3691_);
v___x_3768_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
lean_ctor_set(v___x_3768_, 1, v_zetaDeltaSet_3691_);
lean_ctor_set(v___x_3768_, 2, v_lctx_3692_);
lean_ctor_set(v___x_3768_, 3, v_localInstances_3693_);
lean_ctor_set(v___x_3768_, 4, v_defEqCtx_x3f_3694_);
lean_ctor_set(v___x_3768_, 5, v_synthPendingDepth_3695_);
lean_ctor_set(v___x_3768_, 6, v_canUnfold_x3f_3696_);
lean_ctor_set_uint8(v___x_3768_, sizeof(void*)*7, v_trackZetaDelta_3690_);
lean_ctor_set_uint8(v___x_3768_, sizeof(void*)*7 + 1, v_univApprox_3697_);
lean_ctor_set_uint8(v___x_3768_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3698_);
lean_ctor_set_uint8(v___x_3768_, sizeof(void*)*7 + 3, v_cacheInferType_3699_);
v___x_3769_ = l_Lean_Meta_mkAppOptM(v_a_3720_, v___x_3763_, v___x_3768_, v_a_3556_, v_a_3557_, v_a_3558_);
lean_dec_ref(v___x_3768_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref(v___x_3769_);
v_a_3607_ = v_a_3770_;
goto v___jp_3606_;
}
else
{
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3771_; 
v_a_3771_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3771_);
lean_dec_ref(v___x_3769_);
v_a_3607_ = v_a_3771_;
goto v___jp_3606_;
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec_ref(v_remaining_3577_);
lean_del_object(v___x_3569_);
v_a_3772_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3769_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3769_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_dec(v_a_3718_);
lean_dec(v_val_3711_);
lean_dec_ref(v_a_3702_);
lean_dec_ref(v___x_3671_);
lean_dec_ref(v___x_3667_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_params_3573_);
lean_del_object(v___x_3569_);
v_a_3782_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3719_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3719_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_dec(v_val_3711_);
lean_dec_ref(v_a_3702_);
lean_dec_ref(v___x_3671_);
lean_dec_ref(v___x_3667_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
v_a_3790_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3717_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3717_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
else
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
lean_dec(v_a_3707_);
lean_dec_ref(v_a_3702_);
lean_dec_ref(v___x_3671_);
lean_dec_ref(v___x_3667_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
v___x_3798_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v___x_3798_);
v___x_3800_ = v___x_3709_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec_ref(v_a_3702_);
lean_dec_ref(v___x_3671_);
lean_dec_ref(v___x_3667_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
v_a_3803_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3706_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3706_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec_ref(v___x_3667_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
lean_dec(v_val_3567_);
v_a_3831_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3669_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3669_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
else
{
lean_object* v___x_3839_; lean_object* v___x_3841_; 
lean_dec_ref(v___x_3667_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
lean_dec(v_val_3567_);
v___x_3839_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3839_);
v___x_3841_ = v___x_3565_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
v___jp_3606_:
{
lean_object* v___x_3608_; 
lean_inc(v_a_3558_);
lean_inc_ref(v_a_3557_);
lean_inc(v_a_3556_);
lean_inc_ref(v_a_3555_);
lean_inc_ref(v_a_3607_);
v___x_3608_ = lean_infer_type(v_a_3607_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref(v___x_3608_);
v___x_3610_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_3611_ = lean_unsigned_to_nat(3u);
v___x_3612_ = l_Lean_Expr_isAppOfArity(v_a_3609_, v___x_3610_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; 
lean_dec(v_a_3609_);
lean_dec_ref(v_remaining_3577_);
lean_del_object(v___x_3569_);
lean_inc(v_a_3558_);
lean_inc_ref(v_a_3557_);
lean_inc(v_a_3556_);
lean_inc_ref(v_a_3555_);
v___x_3613_ = lean_infer_type(v_a_3607_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref(v___x_3613_);
v___x_3615_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2);
v___x_3616_ = l_Lean_indentExpr(v_a_3614_);
v___x_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3615_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v___x_3617_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
return v___x_3618_;
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
v_a_3619_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3613_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3613_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v___x_3627_; lean_object* v___x_3629_; 
v___x_3627_ = l_Lean_Expr_appArg_x21(v_a_3609_);
lean_dec(v_a_3609_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v_a_3607_);
v___x_3629_ = v___x_3569_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3607_);
v___x_3629_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3630_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3630_, 0, v___x_3627_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
lean_ctor_set_uint8(v___x_3630_, sizeof(void*)*2, v___x_3561_);
v___x_3631_ = l_Array_toSubarray___redArg(v_remaining_3577_, v___x_3605_, v___x_3579_);
v___x_3632_ = l_Subarray_copy___redArg(v___x_3631_);
v___x_3633_ = l_Lean_Meta_Simp_Result_addExtraArgs(v___x_3630_, v___x_3632_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
lean_dec_ref(v___x_3632_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3643_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3636_ = v___x_3633_;
v_isShared_3637_ = v_isSharedCheck_3643_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3633_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3643_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3638_, 0, v_a_3634_);
v___x_3639_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 0, v___x_3639_);
v___x_3641_ = v___x_3636_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v_a_3644_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3633_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3633_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
lean_dec_ref(v_a_3607_);
lean_dec_ref(v_remaining_3577_);
lean_del_object(v___x_3569_);
v_a_3653_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3608_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3608_);
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
else
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
lean_dec_ref(v___x_3597_);
lean_dec_ref(v_remaining_3577_);
lean_dec_ref(v_alts_3576_);
lean_dec_ref(v_discrs_3575_);
lean_dec_ref(v_motive_3574_);
lean_dec_ref(v_params_3573_);
lean_dec(v_matcherName_3572_);
lean_dec_ref(v_toMatcherInfo_3571_);
lean_del_object(v___x_3569_);
lean_dec(v_val_3567_);
v___x_3843_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3843_);
v___x_3845_ = v___x_3565_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
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
}
}
}
}
else
{
lean_object* v___x_3848_; lean_object* v___x_3850_; 
lean_dec(v_a_3563_);
v___x_3848_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3848_);
v___x_3850_ = v___x_3565_;
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
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
v_a_3853_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3562_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3562_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed(lean_object* v_e_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(v_e_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec(v_a_3862_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(lean_object* v_declName_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3871_, v___y_3878_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___boxed(lean_object* v_declName_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(v_declName_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(lean_object* v_00_u03b1_3891_, lean_object* v_msg_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v___x_3901_; 
v___x_3901_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_3892_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___boxed(lean_object* v_00_u03b1_3902_, lean_object* v_msg_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(v_00_u03b1_3902_, v_msg_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3913_, lean_object* v_constName_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3924_, lean_object* v_constName_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(v_00_u03b1_3924_, v_constName_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b1_3935_, lean_object* v_ref_3936_, lean_object* v_constName_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3936_, v_constName_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b1_3947_, lean_object* v_ref_3948_, lean_object* v_constName_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(v_00_u03b1_3947_, v_ref_3948_, v_constName_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3959_, lean_object* v_ref_3960_, lean_object* v_msg_3961_, lean_object* v_declHint_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3960_, v_msg_3961_, v_declHint_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3972_, lean_object* v_ref_3973_, lean_object* v_msg_3974_, lean_object* v_declHint_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_3972_, v_ref_3973_, v_msg_3974_, v_declHint_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec(v_ref_3973_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_3985_, lean_object* v_declHint_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3985_, v_declHint_3986_, v___y_3993_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_3996_, lean_object* v_declHint_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(v_msg_3996_, v_declHint_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
lean_dec(v___y_3998_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(lean_object* v_00_u03b1_4007_, lean_object* v_ref_4008_, lean_object* v_msg_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_4008_, v_msg_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___boxed(lean_object* v_00_u03b1_4019_, lean_object* v_ref_4020_, lean_object* v_msg_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(v_00_u03b1_4019_, v_ref_4020_, v_msg_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec(v_ref_4020_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4076_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_));
v___x_4077_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_));
v___x_4078_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed), 9, 0);
v___x_4079_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4076_, v___x_4077_, v___x_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9____boxed(lean_object* v_a_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_();
return v_res_4081_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2(void){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4091_ = lean_box(0);
v___x_4092_ = lean_unsigned_to_nat(16u);
v___x_4093_ = lean_mk_array(v___x_4092_, v___x_4091_);
return v___x_4093_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3(void){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4094_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2);
v___x_4095_ = lean_unsigned_to_nat(0u);
v___x_4096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
lean_ctor_set(v___x_4096_, 1, v___x_4094_);
return v___x_4096_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4(void){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4097_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5(void){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4098_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4);
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
return v___x_4099_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6(void){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; uint8_t v___x_4102_; lean_object* v___x_4103_; 
v___x_4100_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4101_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3);
v___x_4102_ = 1;
v___x_4103_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4103_, 0, v___x_4101_);
lean_ctor_set(v___x_4103_, 1, v___x_4100_);
lean_ctor_set_uint8(v___x_4103_, sizeof(void*)*2, v___x_4102_);
return v___x_4103_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4104_ = lean_unsigned_to_nat(0u);
v___x_4105_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
lean_ctor_set(v___x_4106_, 1, v___x_4104_);
return v___x_4106_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8(void){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4107_ = lean_unsigned_to_nat(32u);
v___x_4108_ = lean_mk_empty_array_with_capacity(v___x_4107_);
v___x_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
return v___x_4109_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9(void){
_start:
{
size_t v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4110_ = ((size_t)5ULL);
v___x_4111_ = lean_unsigned_to_nat(0u);
v___x_4112_ = lean_unsigned_to_nat(32u);
v___x_4113_ = lean_mk_empty_array_with_capacity(v___x_4112_);
v___x_4114_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8);
v___x_4115_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
lean_ctor_set(v___x_4115_, 1, v___x_4113_);
lean_ctor_set(v___x_4115_, 2, v___x_4111_);
lean_ctor_set(v___x_4115_, 3, v___x_4111_);
lean_ctor_set_usize(v___x_4115_, 4, v___x_4110_);
return v___x_4115_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10(void){
_start:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4116_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9);
v___x_4117_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4118_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
lean_ctor_set(v___x_4118_, 2, v___x_4117_);
lean_ctor_set(v___x_4118_, 3, v___x_4116_);
return v___x_4118_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11(void){
_start:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4119_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10);
v___x_4120_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7);
v___x_4121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
lean_ctor_set(v___x_4121_, 1, v___x_4119_);
return v___x_4121_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13(void){
_start:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12));
v___x_4124_ = l_Lean_stringToMessageData(v___x_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object* v_declName_4125_, lean_object* v_mvarId_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_){
_start:
{
uint8_t v___x_4132_; uint8_t v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; uint8_t v_foApprox_4137_; uint8_t v_ctxApprox_4138_; uint8_t v_quasiPatternApprox_4139_; uint8_t v_constApprox_4140_; uint8_t v_isDefEqStuckEx_4141_; uint8_t v_unificationHints_4142_; uint8_t v_proofIrrelevance_4143_; uint8_t v_assignSyntheticOpaque_4144_; uint8_t v_offsetCnstrs_4145_; uint8_t v_etaStruct_4146_; uint8_t v_univApprox_4147_; uint8_t v_iota_4148_; uint8_t v_beta_4149_; uint8_t v_proj_4150_; uint8_t v_zeta_4151_; uint8_t v_zetaDelta_4152_; uint8_t v_zetaUnused_4153_; uint8_t v_zetaHave_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4256_; 
v___x_4132_ = 0;
v___x_4133_ = 1;
v___x_4134_ = lean_box(0);
v___x_4135_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0));
v___x_4136_ = l_Lean_Meta_Context_config(v_a_4127_);
v_foApprox_4137_ = lean_ctor_get_uint8(v___x_4136_, 0);
v_ctxApprox_4138_ = lean_ctor_get_uint8(v___x_4136_, 1);
v_quasiPatternApprox_4139_ = lean_ctor_get_uint8(v___x_4136_, 2);
v_constApprox_4140_ = lean_ctor_get_uint8(v___x_4136_, 3);
v_isDefEqStuckEx_4141_ = lean_ctor_get_uint8(v___x_4136_, 4);
v_unificationHints_4142_ = lean_ctor_get_uint8(v___x_4136_, 5);
v_proofIrrelevance_4143_ = lean_ctor_get_uint8(v___x_4136_, 6);
v_assignSyntheticOpaque_4144_ = lean_ctor_get_uint8(v___x_4136_, 7);
v_offsetCnstrs_4145_ = lean_ctor_get_uint8(v___x_4136_, 8);
v_etaStruct_4146_ = lean_ctor_get_uint8(v___x_4136_, 10);
v_univApprox_4147_ = lean_ctor_get_uint8(v___x_4136_, 11);
v_iota_4148_ = lean_ctor_get_uint8(v___x_4136_, 12);
v_beta_4149_ = lean_ctor_get_uint8(v___x_4136_, 13);
v_proj_4150_ = lean_ctor_get_uint8(v___x_4136_, 14);
v_zeta_4151_ = lean_ctor_get_uint8(v___x_4136_, 15);
v_zetaDelta_4152_ = lean_ctor_get_uint8(v___x_4136_, 16);
v_zetaUnused_4153_ = lean_ctor_get_uint8(v___x_4136_, 17);
v_zetaHave_4154_ = lean_ctor_get_uint8(v___x_4136_, 18);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4156_ = v___x_4136_;
v_isShared_4157_ = v_isSharedCheck_4256_;
goto v_resetjp_4155_;
}
else
{
lean_dec(v___x_4136_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4256_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
uint8_t v_trackZetaDelta_4158_; lean_object* v_zetaDeltaSet_4159_; lean_object* v_lctx_4160_; lean_object* v_localInstances_4161_; lean_object* v_defEqCtx_x3f_4162_; lean_object* v_synthPendingDepth_4163_; lean_object* v_canUnfold_x3f_4164_; uint8_t v_univApprox_4165_; uint8_t v_inTypeClassResolution_4166_; uint8_t v_cacheInferType_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; lean_object* v_config_4171_; 
v_trackZetaDelta_4158_ = lean_ctor_get_uint8(v_a_4127_, sizeof(void*)*7);
v_zetaDeltaSet_4159_ = lean_ctor_get(v_a_4127_, 1);
v_lctx_4160_ = lean_ctor_get(v_a_4127_, 2);
v_localInstances_4161_ = lean_ctor_get(v_a_4127_, 3);
v_defEqCtx_x3f_4162_ = lean_ctor_get(v_a_4127_, 4);
v_synthPendingDepth_4163_ = lean_ctor_get(v_a_4127_, 5);
v_canUnfold_x3f_4164_ = lean_ctor_get(v_a_4127_, 6);
v_univApprox_4165_ = lean_ctor_get_uint8(v_a_4127_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4166_ = lean_ctor_get_uint8(v_a_4127_, sizeof(void*)*7 + 2);
v_cacheInferType_4167_ = lean_ctor_get_uint8(v_a_4127_, sizeof(void*)*7 + 3);
v___x_4168_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1));
v___x_4169_ = 0;
if (v_isShared_4157_ == 0)
{
v_config_4171_ = v___x_4156_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 0, v_foApprox_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 1, v_ctxApprox_4138_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 2, v_quasiPatternApprox_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 3, v_constApprox_4140_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 4, v_isDefEqStuckEx_4141_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 5, v_unificationHints_4142_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 6, v_proofIrrelevance_4143_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 7, v_assignSyntheticOpaque_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 8, v_offsetCnstrs_4145_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 10, v_etaStruct_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 11, v_univApprox_4147_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 12, v_iota_4148_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 13, v_beta_4149_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 14, v_proj_4150_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 15, v_zeta_4151_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 16, v_zetaDelta_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 17, v_zetaUnused_4153_);
lean_ctor_set_uint8(v_reuseFailAlloc_4255_, 18, v_zetaHave_4154_);
v_config_4171_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
uint64_t v___x_4172_; uint64_t v___x_4173_; uint64_t v___x_4174_; lean_object* v___x_4175_; uint64_t v___x_4176_; uint64_t v___x_4177_; uint64_t v_key_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
lean_ctor_set_uint8(v_config_4171_, 9, v___x_4169_);
v___x_4172_ = l_Lean_Meta_Context_configKey(v_a_4127_);
v___x_4173_ = 2ULL;
v___x_4174_ = lean_uint64_shift_right(v___x_4172_, v___x_4173_);
v___x_4175_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6);
v___x_4176_ = lean_uint64_shift_left(v___x_4174_, v___x_4173_);
v___x_4177_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7);
v_key_4178_ = lean_uint64_lor(v___x_4176_, v___x_4177_);
v___x_4179_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4179_, 0, v_config_4171_);
lean_ctor_set_uint64(v___x_4179_, sizeof(void*)*1, v_key_4178_);
lean_inc(v_canUnfold_x3f_4164_);
lean_inc(v_synthPendingDepth_4163_);
lean_inc(v_defEqCtx_x3f_4162_);
lean_inc_ref(v_localInstances_4161_);
lean_inc_ref(v_lctx_4160_);
lean_inc(v_zetaDeltaSet_4159_);
v___x_4180_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
lean_ctor_set(v___x_4180_, 1, v_zetaDeltaSet_4159_);
lean_ctor_set(v___x_4180_, 2, v_lctx_4160_);
lean_ctor_set(v___x_4180_, 3, v_localInstances_4161_);
lean_ctor_set(v___x_4180_, 4, v_defEqCtx_x3f_4162_);
lean_ctor_set(v___x_4180_, 5, v_synthPendingDepth_4163_);
lean_ctor_set(v___x_4180_, 6, v_canUnfold_x3f_4164_);
lean_ctor_set_uint8(v___x_4180_, sizeof(void*)*7, v_trackZetaDelta_4158_);
lean_ctor_set_uint8(v___x_4180_, sizeof(void*)*7 + 1, v_univApprox_4165_);
lean_ctor_set_uint8(v___x_4180_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4166_);
lean_ctor_set_uint8(v___x_4180_, sizeof(void*)*7 + 3, v_cacheInferType_4167_);
v___x_4181_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_4135_, v___x_4168_, v___x_4175_, v___x_4180_, v_a_4129_, v_a_4130_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref(v___x_4181_);
v___x_4183_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_));
v___x_4184_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_4168_, v___x_4183_, v___x_4132_, v_a_4129_, v_a_4130_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v_a_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4185_);
lean_dec_ref(v___x_4184_);
v___x_4186_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11);
v___x_4187_ = l_Lean_Meta_simpTarget(v_mvarId_4126_, v_a_4182_, v_a_4185_, v___x_4134_, v___x_4133_, v___x_4186_, v___x_4180_, v_a_4128_, v_a_4129_, v_a_4130_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4230_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4190_ = v___x_4187_;
v_isShared_4191_ = v_isSharedCheck_4230_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4187_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4230_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v_fst_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4228_; 
v_fst_4192_ = lean_ctor_get(v_a_4188_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v_a_4188_);
if (v_isSharedCheck_4228_ == 0)
{
lean_object* v_unused_4229_; 
v_unused_4229_ = lean_ctor_get(v_a_4188_, 1);
lean_dec(v_unused_4229_);
v___x_4194_ = v_a_4188_;
v_isShared_4195_ = v_isSharedCheck_4228_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_fst_4192_);
lean_dec(v_a_4188_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4228_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
if (lean_obj_tag(v_fst_4192_) == 0)
{
lean_object* v___x_4196_; lean_object* v___x_4198_; 
lean_del_object(v___x_4194_);
lean_dec_ref(v___x_4180_);
lean_dec(v_declName_4125_);
v___x_4196_ = lean_box(0);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v___x_4196_);
v___x_4198_ = v___x_4190_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4196_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
else
{
lean_object* v_val_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4204_; 
lean_del_object(v___x_4190_);
v_val_4200_ = lean_ctor_get(v_fst_4192_, 0);
lean_inc(v_val_4200_);
lean_dec_ref(v_fst_4192_);
v___x_4201_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13);
v___x_4202_ = l_Lean_MessageData_ofConstName(v_declName_4125_, v___x_4132_);
if (v_isShared_4195_ == 0)
{
lean_ctor_set_tag(v___x_4194_, 7);
lean_ctor_set(v___x_4194_, 1, v___x_4202_);
lean_ctor_set(v___x_4194_, 0, v___x_4201_);
v___x_4204_ = v___x_4194_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4201_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v___x_4202_);
v___x_4204_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___f_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4205_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_4206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4204_);
lean_ctor_set(v___x_4206_, 1, v___x_4205_);
v___f_4207_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4207_, 0, v___x_4206_);
v___x_4208_ = lean_box(v___x_4133_);
v___x_4209_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___boxed), 7, 2);
lean_closure_set(v___x_4209_, 0, v_val_4200_);
lean_closure_set(v___x_4209_, 1, v___x_4208_);
v___x_4210_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4209_, v___f_4207_, v___x_4180_, v_a_4128_, v_a_4129_, v_a_4130_);
lean_dec_ref(v___x_4180_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4210_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
v_a_4219_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4210_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4210_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
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
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_dec_ref(v___x_4180_);
lean_dec(v_declName_4125_);
v_a_4231_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4187_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4187_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
lean_dec(v_a_4182_);
lean_dec_ref(v___x_4180_);
lean_dec(v_mvarId_4126_);
lean_dec(v_declName_4125_);
v_a_4239_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4184_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4184_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
lean_dec_ref(v___x_4180_);
lean_dec(v_mvarId_4126_);
lean_dec(v_declName_4125_);
v_a_4247_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4181_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4181_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___boxed(lean_object* v_declName_4257_, lean_object* v_mvarId_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4257_, v_mvarId_4258_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
lean_dec(v_a_4260_);
lean_dec_ref(v_a_4259_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(lean_object* v_e_4265_, lean_object* v_k_4266_, uint8_t v_cleanupAnnotations_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v___f_4273_; uint8_t v___x_4274_; uint8_t v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___f_4273_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4273_, 0, v_k_4266_);
v___x_4274_ = 1;
v___x_4275_ = 0;
v___x_4276_ = lean_box(0);
v___x_4277_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4265_, v___x_4274_, v___x_4275_, v___x_4274_, v___x_4275_, v___x_4276_, v___f_4273_, v_cleanupAnnotations_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4277_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4277_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
v_a_4286_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4277_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4277_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg___boxed(lean_object* v_e_4294_, lean_object* v_k_4295_, lean_object* v_cleanupAnnotations_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4302_; lean_object* v_res_4303_; 
v_cleanupAnnotations_boxed_4302_ = lean_unbox(v_cleanupAnnotations_4296_);
v_res_4303_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4294_, v_k_4295_, v_cleanupAnnotations_boxed_4302_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_object* v_00_u03b1_4304_, lean_object* v_e_4305_, lean_object* v_k_4306_, uint8_t v_cleanupAnnotations_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4305_, v_k_4306_, v_cleanupAnnotations_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed(lean_object* v_00_u03b1_4314_, lean_object* v_e_4315_, lean_object* v_k_4316_, lean_object* v_cleanupAnnotations_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4323_; lean_object* v_res_4324_; 
v_cleanupAnnotations_boxed_4323_ = lean_unbox(v_cleanupAnnotations_4317_);
v_res_4324_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(v_00_u03b1_4314_, v_e_4315_, v_k_4316_, v_cleanupAnnotations_boxed_4323_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
return v_res_4324_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object* v_opts_4325_, lean_object* v_opt_4326_){
_start:
{
lean_object* v_name_4327_; lean_object* v_defValue_4328_; lean_object* v_map_4329_; lean_object* v___x_4330_; 
v_name_4327_ = lean_ctor_get(v_opt_4326_, 0);
v_defValue_4328_ = lean_ctor_get(v_opt_4326_, 1);
v_map_4329_ = lean_ctor_get(v_opts_4325_, 0);
v___x_4330_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4329_, v_name_4327_);
if (lean_obj_tag(v___x_4330_) == 0)
{
uint8_t v___x_4331_; 
v___x_4331_ = lean_unbox(v_defValue_4328_);
return v___x_4331_;
}
else
{
lean_object* v_val_4332_; 
v_val_4332_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_val_4332_);
lean_dec_ref(v___x_4330_);
if (lean_obj_tag(v_val_4332_) == 1)
{
uint8_t v_v_4333_; 
v_v_4333_ = lean_ctor_get_uint8(v_val_4332_, 0);
lean_dec_ref(v_val_4332_);
return v_v_4333_;
}
else
{
uint8_t v___x_4334_; 
lean_dec(v_val_4332_);
v___x_4334_ = lean_unbox(v_defValue_4328_);
return v___x_4334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object* v_opts_4335_, lean_object* v_opt_4336_){
_start:
{
uint8_t v_res_4337_; lean_object* v_r_4338_; 
v_res_4337_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v_opts_4335_, v_opt_4336_);
lean_dec_ref(v_opt_4336_);
lean_dec_ref(v_opts_4335_);
v_r_4338_ = lean_box(v_res_4337_);
return v_r_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(lean_object* v_opts_4339_, lean_object* v_opt_4340_){
_start:
{
lean_object* v_name_4341_; lean_object* v_defValue_4342_; lean_object* v_map_4343_; lean_object* v___x_4344_; 
v_name_4341_ = lean_ctor_get(v_opt_4340_, 0);
v_defValue_4342_ = lean_ctor_get(v_opt_4340_, 1);
v_map_4343_ = lean_ctor_get(v_opts_4339_, 0);
v___x_4344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4343_, v_name_4341_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_inc(v_defValue_4342_);
return v_defValue_4342_;
}
else
{
lean_object* v_val_4345_; 
v_val_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_val_4345_);
lean_dec_ref(v___x_4344_);
if (lean_obj_tag(v_val_4345_) == 3)
{
lean_object* v_v_4346_; 
v_v_4346_ = lean_ctor_get(v_val_4345_, 0);
lean_inc(v_v_4346_);
lean_dec_ref(v_val_4345_);
return v_v_4346_;
}
else
{
lean_dec(v_val_4345_);
lean_inc(v_defValue_4342_);
return v_defValue_4342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4___boxed(lean_object* v_opts_4347_, lean_object* v_opt_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_opts_4347_, v_opt_4348_);
lean_dec_ref(v_opt_4348_);
lean_dec_ref(v_opts_4347_);
return v_res_4349_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4350_; double v___x_4351_; 
v___x_4350_ = lean_unsigned_to_nat(0u);
v___x_4351_ = lean_float_of_nat(v___x_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(lean_object* v_cls_4355_, lean_object* v_msg_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v_ref_4362_; lean_object* v___x_4363_; lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4408_; 
v_ref_4362_ = lean_ctor_get(v___y_4359_, 5);
v___x_4363_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4366_ = v___x_4363_;
v_isShared_4367_ = v_isSharedCheck_4408_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4363_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4408_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4368_; lean_object* v_traceState_4369_; lean_object* v_env_4370_; lean_object* v_nextMacroScope_4371_; lean_object* v_ngen_4372_; lean_object* v_auxDeclNGen_4373_; lean_object* v_cache_4374_; lean_object* v_messages_4375_; lean_object* v_infoState_4376_; lean_object* v_snapshotTasks_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4407_; 
v___x_4368_ = lean_st_ref_take(v___y_4360_);
v_traceState_4369_ = lean_ctor_get(v___x_4368_, 4);
v_env_4370_ = lean_ctor_get(v___x_4368_, 0);
v_nextMacroScope_4371_ = lean_ctor_get(v___x_4368_, 1);
v_ngen_4372_ = lean_ctor_get(v___x_4368_, 2);
v_auxDeclNGen_4373_ = lean_ctor_get(v___x_4368_, 3);
v_cache_4374_ = lean_ctor_get(v___x_4368_, 5);
v_messages_4375_ = lean_ctor_get(v___x_4368_, 6);
v_infoState_4376_ = lean_ctor_get(v___x_4368_, 7);
v_snapshotTasks_4377_ = lean_ctor_get(v___x_4368_, 8);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4379_ = v___x_4368_;
v_isShared_4380_ = v_isSharedCheck_4407_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_snapshotTasks_4377_);
lean_inc(v_infoState_4376_);
lean_inc(v_messages_4375_);
lean_inc(v_cache_4374_);
lean_inc(v_traceState_4369_);
lean_inc(v_auxDeclNGen_4373_);
lean_inc(v_ngen_4372_);
lean_inc(v_nextMacroScope_4371_);
lean_inc(v_env_4370_);
lean_dec(v___x_4368_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4407_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
uint64_t v_tid_4381_; lean_object* v_traces_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4406_; 
v_tid_4381_ = lean_ctor_get_uint64(v_traceState_4369_, sizeof(void*)*1);
v_traces_4382_ = lean_ctor_get(v_traceState_4369_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v_traceState_4369_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4384_ = v_traceState_4369_;
v_isShared_4385_ = v_isSharedCheck_4406_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_traces_4382_);
lean_dec(v_traceState_4369_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4406_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4386_; double v___x_4387_; uint8_t v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4396_; 
v___x_4386_ = lean_box(0);
v___x_4387_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0);
v___x_4388_ = 0;
v___x_4389_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__1));
v___x_4390_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4390_, 0, v_cls_4355_);
lean_ctor_set(v___x_4390_, 1, v___x_4386_);
lean_ctor_set(v___x_4390_, 2, v___x_4389_);
lean_ctor_set_float(v___x_4390_, sizeof(void*)*3, v___x_4387_);
lean_ctor_set_float(v___x_4390_, sizeof(void*)*3 + 8, v___x_4387_);
lean_ctor_set_uint8(v___x_4390_, sizeof(void*)*3 + 16, v___x_4388_);
v___x_4391_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__2));
v___x_4392_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4390_);
lean_ctor_set(v___x_4392_, 1, v_a_4364_);
lean_ctor_set(v___x_4392_, 2, v___x_4391_);
lean_inc(v_ref_4362_);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v_ref_4362_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = l_Lean_PersistentArray_push___redArg(v_traces_4382_, v___x_4393_);
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 0, v___x_4394_);
v___x_4396_ = v___x_4384_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4394_);
lean_ctor_set_uint64(v_reuseFailAlloc_4405_, sizeof(void*)*1, v_tid_4381_);
v___x_4396_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
lean_object* v___x_4398_; 
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 4, v___x_4396_);
v___x_4398_ = v___x_4379_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_env_4370_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_nextMacroScope_4371_);
lean_ctor_set(v_reuseFailAlloc_4404_, 2, v_ngen_4372_);
lean_ctor_set(v_reuseFailAlloc_4404_, 3, v_auxDeclNGen_4373_);
lean_ctor_set(v_reuseFailAlloc_4404_, 4, v___x_4396_);
lean_ctor_set(v_reuseFailAlloc_4404_, 5, v_cache_4374_);
lean_ctor_set(v_reuseFailAlloc_4404_, 6, v_messages_4375_);
lean_ctor_set(v_reuseFailAlloc_4404_, 7, v_infoState_4376_);
lean_ctor_set(v_reuseFailAlloc_4404_, 8, v_snapshotTasks_4377_);
v___x_4398_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4399_ = lean_st_ref_set(v___y_4360_, v___x_4398_);
v___x_4400_ = lean_box(0);
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 0, v___x_4400_);
v___x_4402_ = v___x_4366_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___boxed(lean_object* v_cls_4409_, lean_object* v_msg_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v_cls_4409_, v_msg_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
return v_res_4416_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4426_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4427_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4428_ = l_Lean_Name_append(v___x_4427_, v___x_4426_);
return v___x_4428_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4430_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__6));
v___x_4431_ = l_Lean_stringToMessageData(v___x_4430_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object* v_levelParams_4432_, lean_object* v_declName_4433_, lean_object* v_wfPreprocessProof_4434_, lean_object* v___x_4435_, lean_object* v_unaryPreDefName_4436_, lean_object* v_xs_4437_, lean_object* v_body_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4447_ = lean_box(0);
lean_inc(v_levelParams_4432_);
v___x_4448_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4432_, v___x_4447_);
lean_inc(v_declName_4433_);
v___x_4449_ = l_Lean_mkConst(v_declName_4433_, v___x_4448_);
v___x_4450_ = l_Lean_mkAppN(v___x_4449_, v_xs_4437_);
v___x_4451_ = l_Lean_Meta_mkEq(v___x_4450_, v_body_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc_n(v_a_4452_, 2);
lean_dec_ref(v___x_4451_);
v___x_4453_ = lean_box(0);
v___x_4454_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4452_, v___x_4453_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4456_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4455_);
lean_dec_ref(v___x_4454_);
v___x_4456_ = l_Lean_Meta_Simp_Result_addExtraArgs(v_wfPreprocessProof_4434_, v_xs_4437_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; uint8_t v___x_4460_; lean_object* v_mvarId_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_a_4457_);
lean_dec_ref(v___x_4456_);
v___x_4458_ = l_Lean_Expr_appFn_x21(v_a_4452_);
v___x_4459_ = lean_box(0);
v___x_4460_ = 1;
v___x_4534_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4534_, 0, v___x_4458_);
lean_ctor_set(v___x_4534_, 1, v___x_4459_);
lean_ctor_set_uint8(v___x_4534_, sizeof(void*)*2, v___x_4460_);
v___x_4535_ = l_Lean_Meta_Simp_mkCongr(v___x_4534_, v_a_4457_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref(v___x_4535_);
v___x_4537_ = l_Lean_Expr_mvarId_x21(v_a_4455_);
v___x_4538_ = l_Lean_Meta_applySimpResultToTarget(v___x_4537_, v_a_4452_, v_a_4536_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; uint8_t v___x_4540_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref(v___x_4538_);
v___x_4540_ = lean_name_eq(v_declName_4433_, v_unaryPreDefName_4436_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; 
v___x_4541_ = l_Lean_Elab_Eqns_deltaLHS(v_a_4539_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4542_);
lean_dec_ref(v___x_4541_);
v_mvarId_4462_ = v_a_4542_;
v___y_4463_ = v___y_4439_;
v___y_4464_ = v___y_4440_;
v___y_4465_ = v___y_4441_;
v___y_4466_ = v___y_4442_;
goto v___jp_4461_;
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_dec(v_a_4455_);
lean_dec(v_a_4452_);
lean_dec(v___x_4435_);
lean_dec(v_declName_4433_);
lean_dec(v_levelParams_4432_);
v_a_4543_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4541_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4541_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
else
{
v_mvarId_4462_ = v_a_4539_;
v___y_4463_ = v___y_4439_;
v___y_4464_ = v___y_4440_;
v___y_4465_ = v___y_4441_;
v___y_4466_ = v___y_4442_;
goto v___jp_4461_;
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_dec(v_a_4455_);
lean_dec(v_a_4452_);
lean_dec(v___x_4435_);
lean_dec(v_declName_4433_);
lean_dec(v_levelParams_4432_);
v_a_4551_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4538_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4538_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
lean_dec(v_a_4455_);
lean_dec(v_a_4452_);
lean_dec(v___x_4435_);
lean_dec(v_declName_4433_);
lean_dec(v_levelParams_4432_);
v_a_4559_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4561_ = v___x_4535_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4535_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
v___jp_4461_:
{
lean_object* v___x_4467_; 
v___x_4467_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; lean_object* v___x_4469_; 
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc(v_a_4468_);
lean_dec_ref(v___x_4467_);
v___x_4469_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4433_, v_a_4468_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v___x_4470_; lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4525_; 
lean_dec_ref(v___x_4469_);
v___x_4470_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4455_, v___y_4464_);
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4473_ = v___x_4470_;
v_isShared_4474_ = v_isSharedCheck_4525_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4470_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4525_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
uint8_t v___x_4475_; uint8_t v___x_4476_; lean_object* v___x_4477_; 
v___x_4475_ = 0;
v___x_4476_ = 1;
v___x_4477_ = l_Lean_Meta_mkForallFVars(v_xs_4437_, v_a_4452_, v___x_4475_, v___x_4460_, v___x_4460_, v___x_4476_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4479_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4478_);
lean_dec_ref(v___x_4477_);
v___x_4479_ = l_Lean_Meta_letToHave(v_a_4478_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; lean_object* v___x_4481_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref(v___x_4479_);
v___x_4481_ = l_Lean_Meta_mkLambdaFVars(v_xs_4437_, v_a_4471_, v___x_4475_, v___x_4460_, v___x_4475_, v___x_4460_, v___x_4476_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4487_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref(v___x_4481_);
lean_inc_n(v___x_4435_, 2);
v___x_4483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4435_);
lean_ctor_set(v___x_4483_, 1, v_levelParams_4432_);
lean_ctor_set(v___x_4483_, 2, v_a_4480_);
v___x_4484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4435_);
lean_ctor_set(v___x_4484_, 1, v___x_4447_);
v___x_4485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4483_);
lean_ctor_set(v___x_4485_, 1, v_a_4482_);
lean_ctor_set(v___x_4485_, 2, v___x_4484_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set_tag(v___x_4473_, 2);
lean_ctor_set(v___x_4473_, 0, v___x_4485_);
v___x_4487_ = v___x_4473_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4485_);
v___x_4487_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
lean_object* v___x_4488_; 
v___x_4488_ = l_Lean_addDecl(v___x_4487_, v___x_4475_, v___y_4465_, v___y_4466_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v___x_4489_; 
lean_dec_ref(v___x_4488_);
lean_inc(v___x_4435_);
v___x_4489_ = l_Lean_inferDefEqAttr(v___x_4435_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_options_4490_; uint8_t v_hasTrace_4491_; 
lean_dec_ref(v___x_4489_);
v_options_4490_ = lean_ctor_get(v___y_4465_, 2);
v_hasTrace_4491_ = lean_ctor_get_uint8(v_options_4490_, sizeof(void*)*1);
if (v_hasTrace_4491_ == 0)
{
lean_dec(v___x_4435_);
goto v___jp_4444_;
}
else
{
lean_object* v_inheritedTraceOptions_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; uint8_t v___x_4495_; 
v_inheritedTraceOptions_4492_ = lean_ctor_get(v___y_4465_, 13);
v___x_4493_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4494_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_4495_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4492_, v_options_4490_, v___x_4494_);
if (v___x_4495_ == 0)
{
lean_dec(v___x_4435_);
goto v___jp_4444_;
}
else
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4496_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7);
v___x_4497_ = l_Lean_MessageData_ofConstName(v___x_4435_, v___x_4475_);
v___x_4498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4496_);
lean_ctor_set(v___x_4498_, 1, v___x_4497_);
v___x_4499_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_4493_, v___x_4498_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
return v___x_4499_;
}
}
}
else
{
lean_dec(v___x_4435_);
return v___x_4489_;
}
}
else
{
lean_dec(v___x_4435_);
return v___x_4488_;
}
}
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_dec(v_a_4480_);
lean_del_object(v___x_4473_);
lean_dec(v___x_4435_);
lean_dec(v_levelParams_4432_);
v_a_4501_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4481_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4481_);
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
lean_del_object(v___x_4473_);
lean_dec(v_a_4471_);
lean_dec(v___x_4435_);
lean_dec(v_levelParams_4432_);
v_a_4509_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4479_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4479_);
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
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4524_; 
lean_del_object(v___x_4473_);
lean_dec(v_a_4471_);
lean_dec(v___x_4435_);
lean_dec(v_levelParams_4432_);
v_a_4517_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4519_ = v___x_4477_;
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4477_);
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
}
else
{
lean_dec(v_a_4455_);
lean_dec(v_a_4452_);
lean_dec(v___x_4435_);
lean_dec(v_levelParams_4432_);
return v___x_4469_;
}
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_dec(v_a_4455_);
lean_dec(v_a_4452_);
lean_dec(v___x_4435_);
lean_dec(v_declName_4433_);
lean_dec(v_levelParams_4432_);
v_a_4526_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4467_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4467_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
else
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4574_; 
lean_dec(v_a_4455_);
lean_dec(v_a_4452_);
lean_dec(v___x_4435_);
lean_dec(v_declName_4433_);
lean_dec(v_levelParams_4432_);
v_a_4567_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4569_ = v___x_4456_;
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v___x_4456_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4572_; 
if (v_isShared_4570_ == 0)
{
v___x_4572_ = v___x_4569_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_a_4567_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
lean_dec(v_a_4452_);
lean_dec(v___x_4435_);
lean_dec_ref(v_wfPreprocessProof_4434_);
lean_dec(v_declName_4433_);
lean_dec(v_levelParams_4432_);
v_a_4575_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4454_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4454_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_dec(v___x_4435_);
lean_dec_ref(v_wfPreprocessProof_4434_);
lean_dec(v_declName_4433_);
lean_dec(v_levelParams_4432_);
v_a_4583_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4451_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4451_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
v___jp_4444_:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4445_ = lean_box(0);
v___x_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4445_);
return v___x_4446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object* v_levelParams_4591_, lean_object* v_declName_4592_, lean_object* v_wfPreprocessProof_4593_, lean_object* v___x_4594_, lean_object* v_unaryPreDefName_4595_, lean_object* v_xs_4596_, lean_object* v_body_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l_Lean_Elab_WF_mkUnfoldEq___lam__0(v_levelParams_4591_, v_declName_4592_, v_wfPreprocessProof_4593_, v___x_4594_, v_unaryPreDefName_4595_, v_xs_4596_, v_body_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec_ref(v_xs_4596_);
lean_dec(v_unaryPreDefName_4595_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(lean_object* v___y_4604_, uint8_t v_isExporting_4605_, lean_object* v___x_4606_, lean_object* v___y_4607_, lean_object* v___x_4608_, lean_object* v_a_x3f_4609_){
_start:
{
lean_object* v___x_4611_; lean_object* v_env_4612_; lean_object* v_nextMacroScope_4613_; lean_object* v_ngen_4614_; lean_object* v_auxDeclNGen_4615_; lean_object* v_traceState_4616_; lean_object* v_messages_4617_; lean_object* v_infoState_4618_; lean_object* v_snapshotTasks_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4644_; 
v___x_4611_ = lean_st_ref_take(v___y_4604_);
v_env_4612_ = lean_ctor_get(v___x_4611_, 0);
v_nextMacroScope_4613_ = lean_ctor_get(v___x_4611_, 1);
v_ngen_4614_ = lean_ctor_get(v___x_4611_, 2);
v_auxDeclNGen_4615_ = lean_ctor_get(v___x_4611_, 3);
v_traceState_4616_ = lean_ctor_get(v___x_4611_, 4);
v_messages_4617_ = lean_ctor_get(v___x_4611_, 6);
v_infoState_4618_ = lean_ctor_get(v___x_4611_, 7);
v_snapshotTasks_4619_ = lean_ctor_get(v___x_4611_, 8);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4644_ == 0)
{
lean_object* v_unused_4645_; 
v_unused_4645_ = lean_ctor_get(v___x_4611_, 5);
lean_dec(v_unused_4645_);
v___x_4621_ = v___x_4611_;
v_isShared_4622_ = v_isSharedCheck_4644_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_snapshotTasks_4619_);
lean_inc(v_infoState_4618_);
lean_inc(v_messages_4617_);
lean_inc(v_traceState_4616_);
lean_inc(v_auxDeclNGen_4615_);
lean_inc(v_ngen_4614_);
lean_inc(v_nextMacroScope_4613_);
lean_inc(v_env_4612_);
lean_dec(v___x_4611_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4644_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4623_; lean_object* v___x_4625_; 
v___x_4623_ = l_Lean_Environment_setExporting(v_env_4612_, v_isExporting_4605_);
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 5, v___x_4606_);
lean_ctor_set(v___x_4621_, 0, v___x_4623_);
v___x_4625_ = v___x_4621_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v___x_4623_);
lean_ctor_set(v_reuseFailAlloc_4643_, 1, v_nextMacroScope_4613_);
lean_ctor_set(v_reuseFailAlloc_4643_, 2, v_ngen_4614_);
lean_ctor_set(v_reuseFailAlloc_4643_, 3, v_auxDeclNGen_4615_);
lean_ctor_set(v_reuseFailAlloc_4643_, 4, v_traceState_4616_);
lean_ctor_set(v_reuseFailAlloc_4643_, 5, v___x_4606_);
lean_ctor_set(v_reuseFailAlloc_4643_, 6, v_messages_4617_);
lean_ctor_set(v_reuseFailAlloc_4643_, 7, v_infoState_4618_);
lean_ctor_set(v_reuseFailAlloc_4643_, 8, v_snapshotTasks_4619_);
v___x_4625_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v_mctx_4628_; lean_object* v_zetaDeltaFVarIds_4629_; lean_object* v_postponed_4630_; lean_object* v_diag_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4641_; 
v___x_4626_ = lean_st_ref_set(v___y_4604_, v___x_4625_);
v___x_4627_ = lean_st_ref_take(v___y_4607_);
v_mctx_4628_ = lean_ctor_get(v___x_4627_, 0);
v_zetaDeltaFVarIds_4629_ = lean_ctor_get(v___x_4627_, 2);
v_postponed_4630_ = lean_ctor_get(v___x_4627_, 3);
v_diag_4631_ = lean_ctor_get(v___x_4627_, 4);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4641_ == 0)
{
lean_object* v_unused_4642_; 
v_unused_4642_ = lean_ctor_get(v___x_4627_, 1);
lean_dec(v_unused_4642_);
v___x_4633_ = v___x_4627_;
v_isShared_4634_ = v_isSharedCheck_4641_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_diag_4631_);
lean_inc(v_postponed_4630_);
lean_inc(v_zetaDeltaFVarIds_4629_);
lean_inc(v_mctx_4628_);
lean_dec(v___x_4627_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4641_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
lean_ctor_set(v___x_4633_, 1, v___x_4608_);
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_mctx_4628_);
lean_ctor_set(v_reuseFailAlloc_4640_, 1, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4640_, 2, v_zetaDeltaFVarIds_4629_);
lean_ctor_set(v_reuseFailAlloc_4640_, 3, v_postponed_4630_);
lean_ctor_set(v_reuseFailAlloc_4640_, 4, v_diag_4631_);
v___x_4636_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4637_ = lean_st_ref_set(v___y_4607_, v___x_4636_);
v___x_4638_ = lean_box(0);
v___x_4639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4638_);
return v___x_4639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v___y_4646_, lean_object* v_isExporting_4647_, lean_object* v___x_4648_, lean_object* v___y_4649_, lean_object* v___x_4650_, lean_object* v_a_x3f_4651_, lean_object* v___y_4652_){
_start:
{
uint8_t v_isExporting_boxed_4653_; lean_object* v_res_4654_; 
v_isExporting_boxed_4653_ = lean_unbox(v_isExporting_4647_);
v_res_4654_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4646_, v_isExporting_boxed_4653_, v___x_4648_, v___y_4649_, v___x_4650_, v_a_x3f_4651_);
lean_dec(v_a_x3f_4651_);
lean_dec(v___y_4649_);
lean_dec(v___y_4646_);
return v_res_4654_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4655_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0);
v___x_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
return v___x_4657_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4658_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1);
v___x_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4658_);
lean_ctor_set(v___x_4659_, 1, v___x_4658_);
return v___x_4659_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4660_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1);
v___x_4661_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4661_, 0, v___x_4660_);
lean_ctor_set(v___x_4661_, 1, v___x_4660_);
lean_ctor_set(v___x_4661_, 2, v___x_4660_);
lean_ctor_set(v___x_4661_, 3, v___x_4660_);
lean_ctor_set(v___x_4661_, 4, v___x_4660_);
lean_ctor_set(v___x_4661_, 5, v___x_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(lean_object* v_x_4662_, uint8_t v_isExporting_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v___x_4669_; lean_object* v_env_4670_; uint8_t v_isExporting_4671_; lean_object* v___x_4672_; lean_object* v_env_4673_; lean_object* v_nextMacroScope_4674_; lean_object* v_ngen_4675_; lean_object* v_auxDeclNGen_4676_; lean_object* v_traceState_4677_; lean_object* v_messages_4678_; lean_object* v_infoState_4679_; lean_object* v_snapshotTasks_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4734_; 
v___x_4669_ = lean_st_ref_get(v___y_4667_);
v_env_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc_ref(v_env_4670_);
lean_dec(v___x_4669_);
v_isExporting_4671_ = lean_ctor_get_uint8(v_env_4670_, sizeof(void*)*8);
lean_dec_ref(v_env_4670_);
v___x_4672_ = lean_st_ref_take(v___y_4667_);
v_env_4673_ = lean_ctor_get(v___x_4672_, 0);
v_nextMacroScope_4674_ = lean_ctor_get(v___x_4672_, 1);
v_ngen_4675_ = lean_ctor_get(v___x_4672_, 2);
v_auxDeclNGen_4676_ = lean_ctor_get(v___x_4672_, 3);
v_traceState_4677_ = lean_ctor_get(v___x_4672_, 4);
v_messages_4678_ = lean_ctor_get(v___x_4672_, 6);
v_infoState_4679_ = lean_ctor_get(v___x_4672_, 7);
v_snapshotTasks_4680_ = lean_ctor_get(v___x_4672_, 8);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4734_ == 0)
{
lean_object* v_unused_4735_; 
v_unused_4735_ = lean_ctor_get(v___x_4672_, 5);
lean_dec(v_unused_4735_);
v___x_4682_ = v___x_4672_;
v_isShared_4683_ = v_isSharedCheck_4734_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_snapshotTasks_4680_);
lean_inc(v_infoState_4679_);
lean_inc(v_messages_4678_);
lean_inc(v_traceState_4677_);
lean_inc(v_auxDeclNGen_4676_);
lean_inc(v_ngen_4675_);
lean_inc(v_nextMacroScope_4674_);
lean_inc(v_env_4673_);
lean_dec(v___x_4672_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4734_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4687_; 
v___x_4684_ = l_Lean_Environment_setExporting(v_env_4673_, v_isExporting_4663_);
v___x_4685_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 5, v___x_4685_);
lean_ctor_set(v___x_4682_, 0, v___x_4684_);
v___x_4687_ = v___x_4682_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4684_);
lean_ctor_set(v_reuseFailAlloc_4733_, 1, v_nextMacroScope_4674_);
lean_ctor_set(v_reuseFailAlloc_4733_, 2, v_ngen_4675_);
lean_ctor_set(v_reuseFailAlloc_4733_, 3, v_auxDeclNGen_4676_);
lean_ctor_set(v_reuseFailAlloc_4733_, 4, v_traceState_4677_);
lean_ctor_set(v_reuseFailAlloc_4733_, 5, v___x_4685_);
lean_ctor_set(v_reuseFailAlloc_4733_, 6, v_messages_4678_);
lean_ctor_set(v_reuseFailAlloc_4733_, 7, v_infoState_4679_);
lean_ctor_set(v_reuseFailAlloc_4733_, 8, v_snapshotTasks_4680_);
v___x_4687_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v_mctx_4690_; lean_object* v_zetaDeltaFVarIds_4691_; lean_object* v_postponed_4692_; lean_object* v_diag_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4731_; 
v___x_4688_ = lean_st_ref_set(v___y_4667_, v___x_4687_);
v___x_4689_ = lean_st_ref_take(v___y_4665_);
v_mctx_4690_ = lean_ctor_get(v___x_4689_, 0);
v_zetaDeltaFVarIds_4691_ = lean_ctor_get(v___x_4689_, 2);
v_postponed_4692_ = lean_ctor_get(v___x_4689_, 3);
v_diag_4693_ = lean_ctor_get(v___x_4689_, 4);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; 
v_unused_4732_ = lean_ctor_get(v___x_4689_, 1);
lean_dec(v_unused_4732_);
v___x_4695_ = v___x_4689_;
v_isShared_4696_ = v_isSharedCheck_4731_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_diag_4693_);
lean_inc(v_postponed_4692_);
lean_inc(v_zetaDeltaFVarIds_4691_);
lean_inc(v_mctx_4690_);
lean_dec(v___x_4689_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4731_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4697_; lean_object* v___x_4699_; 
v___x_4697_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3);
if (v_isShared_4696_ == 0)
{
lean_ctor_set(v___x_4695_, 1, v___x_4697_);
v___x_4699_ = v___x_4695_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_mctx_4690_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v___x_4697_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_zetaDeltaFVarIds_4691_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_postponed_4692_);
lean_ctor_set(v_reuseFailAlloc_4730_, 4, v_diag_4693_);
v___x_4699_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
lean_object* v___x_4700_; lean_object* v_r_4701_; 
v___x_4700_ = lean_st_ref_set(v___y_4665_, v___x_4699_);
lean_inc(v___y_4667_);
lean_inc_ref(v___y_4666_);
lean_inc(v___y_4665_);
lean_inc_ref(v___y_4664_);
v_r_4701_ = lean_apply_5(v_x_4662_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, lean_box(0));
if (lean_obj_tag(v_r_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4718_; 
v_a_4702_ = lean_ctor_get(v_r_4701_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v_r_4701_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4704_ = v_r_4701_;
v_isShared_4705_ = v_isSharedCheck_4718_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v_r_4701_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4718_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
lean_inc(v_a_4702_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set_tag(v___x_4704_, 1);
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
lean_object* v___x_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4715_; 
v___x_4708_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4667_, v_isExporting_4671_, v___x_4685_, v___y_4665_, v___x_4697_, v___x_4707_);
lean_dec_ref(v___x_4707_);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4715_ == 0)
{
lean_object* v_unused_4716_; 
v_unused_4716_ = lean_ctor_get(v___x_4708_, 0);
lean_dec(v_unused_4716_);
v___x_4710_ = v___x_4708_;
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
else
{
lean_dec(v___x_4708_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4713_; 
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 0, v_a_4702_);
v___x_4713_ = v___x_4710_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4702_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
v_a_4719_ = lean_ctor_get(v_r_4701_, 0);
lean_inc(v_a_4719_);
lean_dec_ref(v_r_4701_);
v___x_4720_ = lean_box(0);
v___x_4721_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4667_, v_isExporting_4671_, v___x_4685_, v___y_4665_, v___x_4697_, v___x_4720_);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4728_ == 0)
{
lean_object* v_unused_4729_; 
v_unused_4729_ = lean_ctor_get(v___x_4721_, 0);
lean_dec(v_unused_4729_);
v___x_4723_ = v___x_4721_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_dec(v___x_4721_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
lean_ctor_set_tag(v___x_4723_, 1);
lean_ctor_set(v___x_4723_, 0, v_a_4719_);
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4719_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___boxed(lean_object* v_x_4736_, lean_object* v_isExporting_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
uint8_t v_isExporting_boxed_4743_; lean_object* v_res_4744_; 
v_isExporting_boxed_4743_ = lean_unbox(v_isExporting_4737_);
v_res_4744_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4736_, v_isExporting_boxed_4743_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
lean_dec(v___y_4741_);
lean_dec_ref(v___y_4740_);
lean_dec(v___y_4739_);
lean_dec_ref(v___y_4738_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(lean_object* v_x_4745_, uint8_t v_when_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
if (v_when_4746_ == 0)
{
lean_object* v___x_4752_; 
lean_inc(v___y_4750_);
lean_inc_ref(v___y_4749_);
lean_inc(v___y_4748_);
lean_inc_ref(v___y_4747_);
v___x_4752_ = lean_apply_5(v_x_4745_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, lean_box(0));
return v___x_4752_;
}
else
{
uint8_t v___x_4753_; lean_object* v___x_4754_; 
v___x_4753_ = 0;
v___x_4754_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4745_, v___x_4753_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
return v___x_4754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg___boxed(lean_object* v_x_4755_, lean_object* v_when_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_){
_start:
{
uint8_t v_when_boxed_4762_; lean_object* v_res_4763_; 
v_when_boxed_4762_ = lean_unbox(v_when_4756_);
v_res_4763_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v_x_4755_, v_when_boxed_4762_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec(v___y_4758_);
lean_dec_ref(v___y_4757_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(lean_object* v_o_4764_, lean_object* v_k_4765_, uint8_t v_v_4766_){
_start:
{
lean_object* v_map_4767_; uint8_t v_hasTrace_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4782_; 
v_map_4767_ = lean_ctor_get(v_o_4764_, 0);
v_hasTrace_4768_ = lean_ctor_get_uint8(v_o_4764_, sizeof(void*)*1);
v_isSharedCheck_4782_ = !lean_is_exclusive(v_o_4764_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4770_ = v_o_4764_;
v_isShared_4771_ = v_isSharedCheck_4782_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_map_4767_);
lean_dec(v_o_4764_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4782_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4772_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4772_, 0, v_v_4766_);
lean_inc(v_k_4765_);
v___x_4773_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4765_, v___x_4772_, v_map_4767_);
if (v_hasTrace_4768_ == 0)
{
lean_object* v___x_4774_; uint8_t v___x_4775_; lean_object* v___x_4777_; 
v___x_4774_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4775_ = l_Lean_Name_isPrefixOf(v___x_4774_, v_k_4765_);
lean_dec(v_k_4765_);
if (v_isShared_4771_ == 0)
{
lean_ctor_set(v___x_4770_, 0, v___x_4773_);
v___x_4777_ = v___x_4770_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4773_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
lean_ctor_set_uint8(v___x_4777_, sizeof(void*)*1, v___x_4775_);
return v___x_4777_;
}
}
else
{
lean_object* v___x_4780_; 
lean_dec(v_k_4765_);
if (v_isShared_4771_ == 0)
{
lean_ctor_set(v___x_4770_, 0, v___x_4773_);
v___x_4780_ = v___x_4770_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4773_);
lean_ctor_set_uint8(v_reuseFailAlloc_4781_, sizeof(void*)*1, v_hasTrace_4768_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2___boxed(lean_object* v_o_4783_, lean_object* v_k_4784_, lean_object* v_v_4785_){
_start:
{
uint8_t v_v_boxed_4786_; lean_object* v_res_4787_; 
v_v_boxed_4786_ = lean_unbox(v_v_4785_);
v_res_4787_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(v_o_4783_, v_k_4784_, v_v_boxed_4786_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(lean_object* v_opts_4788_, lean_object* v_opt_4789_, uint8_t v_val_4790_){
_start:
{
lean_object* v_name_4791_; lean_object* v___x_4792_; 
v_name_4791_ = lean_ctor_get(v_opt_4789_, 0);
lean_inc(v_name_4791_);
lean_dec_ref(v_opt_4789_);
v___x_4792_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(v_opts_4788_, v_name_4791_, v_val_4790_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed(lean_object* v_opts_4793_, lean_object* v_opt_4794_, lean_object* v_val_4795_){
_start:
{
uint8_t v_val_boxed_4796_; lean_object* v_res_4797_; 
v_val_boxed_4796_ = lean_unbox(v_val_4795_);
v_res_4797_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_opts_4793_, v_opt_4794_, v_val_boxed_4796_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t v___x_4798_, lean_object* v___x_4799_, uint8_t v___x_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v___x_4806_; lean_object* v_fileName_4807_; lean_object* v_fileMap_4808_; lean_object* v_options_4809_; lean_object* v_currRecDepth_4810_; lean_object* v_ref_4811_; lean_object* v_currNamespace_4812_; lean_object* v_openDecls_4813_; lean_object* v_initHeartbeats_4814_; lean_object* v_maxHeartbeats_4815_; lean_object* v_quotContext_4816_; lean_object* v_currMacroScope_4817_; lean_object* v_cancelTk_x3f_4818_; uint8_t v_suppressElabErrors_4819_; lean_object* v_inheritedTraceOptions_4820_; lean_object* v_env_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; uint8_t v___x_4825_; lean_object* v_fileName_4827_; lean_object* v_fileMap_4828_; lean_object* v_currRecDepth_4829_; lean_object* v_ref_4830_; lean_object* v_currNamespace_4831_; lean_object* v_openDecls_4832_; lean_object* v_initHeartbeats_4833_; lean_object* v_maxHeartbeats_4834_; lean_object* v_quotContext_4835_; lean_object* v_currMacroScope_4836_; lean_object* v_cancelTk_x3f_4837_; uint8_t v_suppressElabErrors_4838_; lean_object* v_inheritedTraceOptions_4839_; lean_object* v___y_4840_; uint8_t v___y_4846_; uint8_t v___x_4867_; 
v___x_4806_ = lean_st_ref_get(v___y_4804_);
v_fileName_4807_ = lean_ctor_get(v___y_4803_, 0);
v_fileMap_4808_ = lean_ctor_get(v___y_4803_, 1);
v_options_4809_ = lean_ctor_get(v___y_4803_, 2);
v_currRecDepth_4810_ = lean_ctor_get(v___y_4803_, 3);
v_ref_4811_ = lean_ctor_get(v___y_4803_, 5);
v_currNamespace_4812_ = lean_ctor_get(v___y_4803_, 6);
v_openDecls_4813_ = lean_ctor_get(v___y_4803_, 7);
v_initHeartbeats_4814_ = lean_ctor_get(v___y_4803_, 8);
v_maxHeartbeats_4815_ = lean_ctor_get(v___y_4803_, 9);
v_quotContext_4816_ = lean_ctor_get(v___y_4803_, 10);
v_currMacroScope_4817_ = lean_ctor_get(v___y_4803_, 11);
v_cancelTk_x3f_4818_ = lean_ctor_get(v___y_4803_, 12);
v_suppressElabErrors_4819_ = lean_ctor_get_uint8(v___y_4803_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4820_ = lean_ctor_get(v___y_4803_, 13);
v_env_4821_ = lean_ctor_get(v___x_4806_, 0);
lean_inc_ref(v_env_4821_);
lean_dec(v___x_4806_);
v___x_4822_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_4809_);
v___x_4823_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_options_4809_, v___x_4822_, v___x_4798_);
v___x_4824_ = l_Lean_diagnostics;
v___x_4825_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v___x_4823_, v___x_4824_);
v___x_4867_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4821_);
lean_dec_ref(v_env_4821_);
if (v___x_4867_ == 0)
{
if (v___x_4825_ == 0)
{
v_fileName_4827_ = v_fileName_4807_;
v_fileMap_4828_ = v_fileMap_4808_;
v_currRecDepth_4829_ = v_currRecDepth_4810_;
v_ref_4830_ = v_ref_4811_;
v_currNamespace_4831_ = v_currNamespace_4812_;
v_openDecls_4832_ = v_openDecls_4813_;
v_initHeartbeats_4833_ = v_initHeartbeats_4814_;
v_maxHeartbeats_4834_ = v_maxHeartbeats_4815_;
v_quotContext_4835_ = v_quotContext_4816_;
v_currMacroScope_4836_ = v_currMacroScope_4817_;
v_cancelTk_x3f_4837_ = v_cancelTk_x3f_4818_;
v_suppressElabErrors_4838_ = v_suppressElabErrors_4819_;
v_inheritedTraceOptions_4839_ = v_inheritedTraceOptions_4820_;
v___y_4840_ = v___y_4804_;
goto v___jp_4826_;
}
else
{
v___y_4846_ = v___x_4867_;
goto v___jp_4845_;
}
}
else
{
v___y_4846_ = v___x_4825_;
goto v___jp_4845_;
}
v___jp_4826_:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4841_ = l_Lean_maxRecDepth;
v___x_4842_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v___x_4823_, v___x_4841_);
lean_inc_ref(v_inheritedTraceOptions_4839_);
lean_inc(v_cancelTk_x3f_4837_);
lean_inc(v_currMacroScope_4836_);
lean_inc(v_quotContext_4835_);
lean_inc(v_maxHeartbeats_4834_);
lean_inc(v_initHeartbeats_4833_);
lean_inc(v_openDecls_4832_);
lean_inc(v_currNamespace_4831_);
lean_inc(v_ref_4830_);
lean_inc(v_currRecDepth_4829_);
lean_inc_ref(v_fileMap_4828_);
lean_inc_ref(v_fileName_4827_);
v___x_4843_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4843_, 0, v_fileName_4827_);
lean_ctor_set(v___x_4843_, 1, v_fileMap_4828_);
lean_ctor_set(v___x_4843_, 2, v___x_4823_);
lean_ctor_set(v___x_4843_, 3, v_currRecDepth_4829_);
lean_ctor_set(v___x_4843_, 4, v___x_4842_);
lean_ctor_set(v___x_4843_, 5, v_ref_4830_);
lean_ctor_set(v___x_4843_, 6, v_currNamespace_4831_);
lean_ctor_set(v___x_4843_, 7, v_openDecls_4832_);
lean_ctor_set(v___x_4843_, 8, v_initHeartbeats_4833_);
lean_ctor_set(v___x_4843_, 9, v_maxHeartbeats_4834_);
lean_ctor_set(v___x_4843_, 10, v_quotContext_4835_);
lean_ctor_set(v___x_4843_, 11, v_currMacroScope_4836_);
lean_ctor_set(v___x_4843_, 12, v_cancelTk_x3f_4837_);
lean_ctor_set(v___x_4843_, 13, v_inheritedTraceOptions_4839_);
lean_ctor_set_uint8(v___x_4843_, sizeof(void*)*14, v___x_4825_);
lean_ctor_set_uint8(v___x_4843_, sizeof(void*)*14 + 1, v_suppressElabErrors_4838_);
v___x_4844_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v___x_4799_, v___x_4800_, v___y_4801_, v___y_4802_, v___x_4843_, v___y_4840_);
lean_dec_ref(v___x_4843_);
return v___x_4844_;
}
v___jp_4845_:
{
if (v___y_4846_ == 0)
{
lean_object* v___x_4847_; lean_object* v_env_4848_; lean_object* v_nextMacroScope_4849_; lean_object* v_ngen_4850_; lean_object* v_auxDeclNGen_4851_; lean_object* v_traceState_4852_; lean_object* v_messages_4853_; lean_object* v_infoState_4854_; lean_object* v_snapshotTasks_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4865_; 
v___x_4847_ = lean_st_ref_take(v___y_4804_);
v_env_4848_ = lean_ctor_get(v___x_4847_, 0);
v_nextMacroScope_4849_ = lean_ctor_get(v___x_4847_, 1);
v_ngen_4850_ = lean_ctor_get(v___x_4847_, 2);
v_auxDeclNGen_4851_ = lean_ctor_get(v___x_4847_, 3);
v_traceState_4852_ = lean_ctor_get(v___x_4847_, 4);
v_messages_4853_ = lean_ctor_get(v___x_4847_, 6);
v_infoState_4854_ = lean_ctor_get(v___x_4847_, 7);
v_snapshotTasks_4855_ = lean_ctor_get(v___x_4847_, 8);
v_isSharedCheck_4865_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4865_ == 0)
{
lean_object* v_unused_4866_; 
v_unused_4866_ = lean_ctor_get(v___x_4847_, 5);
lean_dec(v_unused_4866_);
v___x_4857_ = v___x_4847_;
v_isShared_4858_ = v_isSharedCheck_4865_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_snapshotTasks_4855_);
lean_inc(v_infoState_4854_);
lean_inc(v_messages_4853_);
lean_inc(v_traceState_4852_);
lean_inc(v_auxDeclNGen_4851_);
lean_inc(v_ngen_4850_);
lean_inc(v_nextMacroScope_4849_);
lean_inc(v_env_4848_);
lean_dec(v___x_4847_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4865_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4862_; 
v___x_4859_ = l_Lean_Kernel_enableDiag(v_env_4848_, v___x_4825_);
v___x_4860_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 5, v___x_4860_);
lean_ctor_set(v___x_4857_, 0, v___x_4859_);
v___x_4862_ = v___x_4857_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v___x_4859_);
lean_ctor_set(v_reuseFailAlloc_4864_, 1, v_nextMacroScope_4849_);
lean_ctor_set(v_reuseFailAlloc_4864_, 2, v_ngen_4850_);
lean_ctor_set(v_reuseFailAlloc_4864_, 3, v_auxDeclNGen_4851_);
lean_ctor_set(v_reuseFailAlloc_4864_, 4, v_traceState_4852_);
lean_ctor_set(v_reuseFailAlloc_4864_, 5, v___x_4860_);
lean_ctor_set(v_reuseFailAlloc_4864_, 6, v_messages_4853_);
lean_ctor_set(v_reuseFailAlloc_4864_, 7, v_infoState_4854_);
lean_ctor_set(v_reuseFailAlloc_4864_, 8, v_snapshotTasks_4855_);
v___x_4862_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
lean_object* v___x_4863_; 
v___x_4863_ = lean_st_ref_set(v___y_4804_, v___x_4862_);
v_fileName_4827_ = v_fileName_4807_;
v_fileMap_4828_ = v_fileMap_4808_;
v_currRecDepth_4829_ = v_currRecDepth_4810_;
v_ref_4830_ = v_ref_4811_;
v_currNamespace_4831_ = v_currNamespace_4812_;
v_openDecls_4832_ = v_openDecls_4813_;
v_initHeartbeats_4833_ = v_initHeartbeats_4814_;
v_maxHeartbeats_4834_ = v_maxHeartbeats_4815_;
v_quotContext_4835_ = v_quotContext_4816_;
v_currMacroScope_4836_ = v_currMacroScope_4817_;
v_cancelTk_x3f_4837_ = v_cancelTk_x3f_4818_;
v_suppressElabErrors_4838_ = v_suppressElabErrors_4819_;
v_inheritedTraceOptions_4839_ = v_inheritedTraceOptions_4820_;
v___y_4840_ = v___y_4804_;
goto v___jp_4826_;
}
}
}
else
{
v_fileName_4827_ = v_fileName_4807_;
v_fileMap_4828_ = v_fileMap_4808_;
v_currRecDepth_4829_ = v_currRecDepth_4810_;
v_ref_4830_ = v_ref_4811_;
v_currNamespace_4831_ = v_currNamespace_4812_;
v_openDecls_4832_ = v_openDecls_4813_;
v_initHeartbeats_4833_ = v_initHeartbeats_4814_;
v_maxHeartbeats_4834_ = v_maxHeartbeats_4815_;
v_quotContext_4835_ = v_quotContext_4816_;
v_currMacroScope_4836_ = v_currMacroScope_4817_;
v_cancelTk_x3f_4837_ = v_cancelTk_x3f_4818_;
v_suppressElabErrors_4838_ = v_suppressElabErrors_4819_;
v_inheritedTraceOptions_4839_ = v_inheritedTraceOptions_4820_;
v___y_4840_ = v___y_4804_;
goto v___jp_4826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object* v___x_4868_, lean_object* v___x_4869_, lean_object* v___x_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_){
_start:
{
uint8_t v___x_9920__boxed_4876_; uint8_t v___x_9922__boxed_4877_; lean_object* v_res_4878_; 
v___x_9920__boxed_4876_ = lean_unbox(v___x_4868_);
v___x_9922__boxed_4877_ = lean_unbox(v___x_4870_);
v_res_4878_ = l_Lean_Elab_WF_mkUnfoldEq___lam__2(v___x_9920__boxed_4876_, v___x_4869_, v___x_9922__boxed_4877_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
return v_res_4878_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4880_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___closed__0));
v___x_4881_ = l_Lean_stringToMessageData(v___x_4880_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object* v_preDef_4882_, lean_object* v_unaryPreDefName_4883_, lean_object* v_wfPreprocessProof_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_){
_start:
{
lean_object* v___x_4890_; lean_object* v_env_4891_; lean_object* v_levelParams_4892_; lean_object* v_declName_4893_; lean_object* v_value_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___f_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___f_4901_; uint8_t v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; uint8_t v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___f_4908_; lean_object* v___x_4909_; 
v___x_4890_ = lean_st_ref_get(v_a_4888_);
v_env_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc_ref(v_env_4891_);
lean_dec(v___x_4890_);
v_levelParams_4892_ = lean_ctor_get(v_preDef_4882_, 1);
lean_inc(v_levelParams_4892_);
v_declName_4893_ = lean_ctor_get(v_preDef_4882_, 3);
lean_inc_n(v_declName_4893_, 2);
v_value_4894_ = lean_ctor_get(v_preDef_4882_, 7);
lean_inc_ref(v_value_4894_);
lean_dec_ref(v_preDef_4882_);
v___x_4895_ = l_Lean_Meta_unfoldThmSuffix;
v___x_4896_ = l_Lean_Meta_mkEqLikeNameFor(v_env_4891_, v_declName_4893_, v___x_4895_);
lean_inc(v___x_4896_);
v___f_4897_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4897_, 0, v_levelParams_4892_);
lean_closure_set(v___f_4897_, 1, v_declName_4893_);
lean_closure_set(v___f_4897_, 2, v_wfPreprocessProof_4884_);
lean_closure_set(v___f_4897_, 3, v___x_4896_);
lean_closure_set(v___f_4897_, 4, v_unaryPreDefName_4883_);
v___x_4898_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___closed__1, &l_Lean_Elab_WF_mkUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1);
v___x_4899_ = l_Lean_MessageData_ofName(v___x_4896_);
v___x_4900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4900_, 0, v___x_4898_);
lean_ctor_set(v___x_4900_, 1, v___x_4899_);
v___f_4901_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4901_, 0, v___x_4900_);
v___x_4902_ = 0;
v___x_4903_ = lean_box(v___x_4902_);
v___x_4904_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed), 9, 4);
lean_closure_set(v___x_4904_, 0, lean_box(0));
lean_closure_set(v___x_4904_, 1, v_value_4894_);
lean_closure_set(v___x_4904_, 2, v___f_4897_);
lean_closure_set(v___x_4904_, 3, v___x_4903_);
v___x_4905_ = 1;
v___x_4906_ = lean_box(v___x_4902_);
v___x_4907_ = lean_box(v___x_4905_);
v___f_4908_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_4908_, 0, v___x_4906_);
lean_closure_set(v___f_4908_, 1, v___x_4904_);
lean_closure_set(v___f_4908_, 2, v___x_4907_);
v___x_4909_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4908_, v___f_4901_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4912_ = v___x_4909_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
else
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
v_a_4918_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___x_4909_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4909_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___boxed(lean_object* v_preDef_4926_, lean_object* v_unaryPreDefName_4927_, lean_object* v_wfPreprocessProof_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l_Lean_Elab_WF_mkUnfoldEq(v_preDef_4926_, v_unaryPreDefName_4927_, v_wfPreprocessProof_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_);
lean_dec(v_a_4932_);
lean_dec_ref(v_a_4931_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6(lean_object* v_00_u03b1_4935_, lean_object* v_x_4936_, uint8_t v_isExporting_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_){
_start:
{
lean_object* v___x_4943_; 
v___x_4943_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4936_, v_isExporting_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4944_, lean_object* v_x_4945_, lean_object* v_isExporting_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
uint8_t v_isExporting_boxed_4952_; lean_object* v_res_4953_; 
v_isExporting_boxed_4952_ = lean_unbox(v_isExporting_4946_);
v_res_4953_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6(v_00_u03b1_4944_, v_x_4945_, v_isExporting_boxed_4952_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
lean_dec(v___y_4950_);
lean_dec_ref(v___y_4949_);
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(lean_object* v_00_u03b1_4954_, lean_object* v_x_4955_, uint8_t v_when_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_){
_start:
{
lean_object* v___x_4962_; 
v___x_4962_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v_x_4955_, v_when_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_);
return v___x_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___boxed(lean_object* v_00_u03b1_4963_, lean_object* v_x_4964_, lean_object* v_when_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_){
_start:
{
uint8_t v_when_boxed_4971_; lean_object* v_res_4972_; 
v_when_boxed_4971_ = lean_unbox(v_when_4965_);
v_res_4972_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(v_00_u03b1_4963_, v_x_4964_, v_when_boxed_4971_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
lean_dec(v___y_4969_);
lean_dec_ref(v___y_4968_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
return v_res_4972_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4974_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0));
v___x_4975_ = l_Lean_stringToMessageData(v___x_4974_);
return v___x_4975_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4981_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3));
v___x_4982_ = l_Lean_stringToMessageData(v___x_4981_);
return v___x_4982_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4984_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5));
v___x_4985_ = l_Lean_stringToMessageData(v___x_4984_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object* v_levelParams_4986_, lean_object* v_declName_4987_, lean_object* v___x_4988_, lean_object* v___x_4989_, lean_object* v___x_4990_, lean_object* v_xs_4991_, lean_object* v_body_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5001_ = lean_box(0);
lean_inc(v_levelParams_4986_);
v___x_5002_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4986_, v___x_5001_);
v___x_5003_ = l_Lean_mkConst(v_declName_4987_, v___x_5002_);
v___x_5004_ = l_Lean_mkAppN(v___x_5003_, v_xs_4991_);
v___x_5005_ = l_Lean_Meta_mkEq(v___x_5004_, v_body_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
lean_inc_n(v_a_5006_, 2);
lean_dec_ref(v___x_5005_);
v___x_5007_ = lean_box(0);
v___x_5008_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_5006_, v___x_5007_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_object* v_a_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
v_a_5009_ = lean_ctor_get(v___x_5008_, 0);
lean_inc(v_a_5009_);
lean_dec_ref(v___x_5008_);
v___x_5010_ = l_Lean_Expr_mvarId_x21(v_a_5009_);
v___x_5011_ = l_Lean_Elab_Eqns_deltaLHS(v___x_5010_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; uint8_t v___x_5013_; uint8_t v___x_5014_; lean_object* v___y_5016_; lean_object* v___y_5017_; lean_object* v___y_5018_; lean_object* v___y_5019_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc_n(v_a_5012_, 2);
lean_dec_ref(v___x_5011_);
v___x_5013_ = 1;
v___x_5014_ = 0;
v___x_5075_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2));
v___x_5076_ = l_Lean_MVarId_applyConst(v_a_5012_, v___x_4988_, v___x_5075_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v_a_5077_; uint8_t v___x_5078_; 
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_a_5077_);
lean_dec_ref(v___x_5076_);
v___x_5078_ = l_List_isEmpty___redArg(v_a_5077_);
lean_dec(v_a_5077_);
if (v___x_5078_ == 0)
{
lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; 
lean_dec(v_a_5009_);
lean_dec(v_a_5006_);
lean_dec(v___x_4989_);
lean_dec(v_levelParams_4986_);
v___x_5079_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4);
v___x_5080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5079_);
lean_ctor_set(v___x_5080_, 1, v___x_4990_);
v___x_5081_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6);
v___x_5082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5082_, 0, v___x_5080_);
lean_ctor_set(v___x_5082_, 1, v___x_5081_);
v___x_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5083_, 0, v_a_5012_);
v___x_5084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5084_, 0, v___x_5082_);
lean_ctor_set(v___x_5084_, 1, v___x_5083_);
v___x_5085_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5086_, 0, v___x_5084_);
lean_ctor_set(v___x_5086_, 1, v___x_5085_);
v___x_5087_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_5086_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
return v___x_5087_;
}
else
{
lean_dec(v_a_5012_);
lean_dec_ref(v___x_4990_);
v___y_5016_ = v___y_4993_;
v___y_5017_ = v___y_4994_;
v___y_5018_ = v___y_4995_;
v___y_5019_ = v___y_4996_;
goto v___jp_5015_;
}
}
else
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
lean_dec(v_a_5012_);
lean_dec(v_a_5009_);
lean_dec(v_a_5006_);
lean_dec_ref(v___x_4990_);
lean_dec(v___x_4989_);
lean_dec(v_levelParams_4986_);
v_a_5088_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5090_ = v___x_5076_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_5076_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5093_; 
if (v_isShared_5091_ == 0)
{
v___x_5093_ = v___x_5090_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_a_5088_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
return v___x_5093_;
}
}
}
v___jp_5015_:
{
lean_object* v___x_5020_; lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5074_; 
v___x_5020_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_5009_, v___y_5017_);
v_a_5021_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5023_ = v___x_5020_;
v_isShared_5024_ = v_isSharedCheck_5074_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_5020_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5074_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
uint8_t v___x_5025_; lean_object* v___x_5026_; 
v___x_5025_ = 1;
v___x_5026_ = l_Lean_Meta_mkForallFVars(v_xs_4991_, v_a_5006_, v___x_5014_, v___x_5013_, v___x_5013_, v___x_5025_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_object* v_a_5027_; lean_object* v___x_5028_; 
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc(v_a_5027_);
lean_dec_ref(v___x_5026_);
v___x_5028_ = l_Lean_Meta_letToHave(v_a_5027_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
if (lean_obj_tag(v___x_5028_) == 0)
{
lean_object* v_a_5029_; lean_object* v___x_5030_; 
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_a_5029_);
lean_dec_ref(v___x_5028_);
v___x_5030_ = l_Lean_Meta_mkLambdaFVars(v_xs_4991_, v_a_5021_, v___x_5014_, v___x_5013_, v___x_5014_, v___x_5013_, v___x_5025_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_object* v_a_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5036_; 
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_a_5031_);
lean_dec_ref(v___x_5030_);
lean_inc_n(v___x_4989_, 2);
v___x_5032_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5032_, 0, v___x_4989_);
lean_ctor_set(v___x_5032_, 1, v_levelParams_4986_);
lean_ctor_set(v___x_5032_, 2, v_a_5029_);
v___x_5033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5033_, 0, v___x_4989_);
lean_ctor_set(v___x_5033_, 1, v___x_5001_);
v___x_5034_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5032_);
lean_ctor_set(v___x_5034_, 1, v_a_5031_);
lean_ctor_set(v___x_5034_, 2, v___x_5033_);
if (v_isShared_5024_ == 0)
{
lean_ctor_set_tag(v___x_5023_, 2);
lean_ctor_set(v___x_5023_, 0, v___x_5034_);
v___x_5036_ = v___x_5023_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
lean_object* v___x_5037_; 
v___x_5037_ = l_Lean_addDecl(v___x_5036_, v___x_5014_, v___y_5018_, v___y_5019_);
if (lean_obj_tag(v___x_5037_) == 0)
{
lean_object* v___x_5038_; 
lean_dec_ref(v___x_5037_);
lean_inc(v___x_4989_);
v___x_5038_ = l_Lean_inferDefEqAttr(v___x_4989_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_options_5039_; uint8_t v_hasTrace_5040_; 
lean_dec_ref(v___x_5038_);
v_options_5039_ = lean_ctor_get(v___y_5018_, 2);
v_hasTrace_5040_ = lean_ctor_get_uint8(v_options_5039_, sizeof(void*)*1);
if (v_hasTrace_5040_ == 0)
{
lean_dec(v___x_4989_);
goto v___jp_4998_;
}
else
{
lean_object* v_inheritedTraceOptions_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; uint8_t v___x_5044_; 
v_inheritedTraceOptions_5041_ = lean_ctor_get(v___y_5018_, 13);
v___x_5042_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_5043_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_5044_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5041_, v_options_5039_, v___x_5043_);
if (v___x_5044_ == 0)
{
lean_dec(v___x_4989_);
goto v___jp_4998_;
}
else
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5045_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1);
v___x_5046_ = l_Lean_MessageData_ofConstName(v___x_4989_, v___x_5014_);
v___x_5047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5047_, 0, v___x_5045_);
lean_ctor_set(v___x_5047_, 1, v___x_5046_);
v___x_5048_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_5042_, v___x_5047_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
return v___x_5048_;
}
}
}
else
{
lean_dec(v___x_4989_);
return v___x_5038_;
}
}
else
{
lean_dec(v___x_4989_);
return v___x_5037_;
}
}
}
else
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
lean_dec(v_a_5029_);
lean_del_object(v___x_5023_);
lean_dec(v___x_4989_);
lean_dec(v_levelParams_4986_);
v_a_5050_ = lean_ctor_get(v___x_5030_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5052_ = v___x_5030_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5030_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5053_ == 0)
{
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_a_5050_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
}
else
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5065_; 
lean_del_object(v___x_5023_);
lean_dec(v_a_5021_);
lean_dec(v___x_4989_);
lean_dec(v_levelParams_4986_);
v_a_5058_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5065_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5065_ == 0)
{
v___x_5060_ = v___x_5028_;
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_5028_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5061_ == 0)
{
v___x_5063_ = v___x_5060_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
}
}
else
{
lean_object* v_a_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5073_; 
lean_del_object(v___x_5023_);
lean_dec(v_a_5021_);
lean_dec(v___x_4989_);
lean_dec(v_levelParams_4986_);
v_a_5066_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5068_ = v___x_5026_;
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_a_5066_);
lean_dec(v___x_5026_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5071_; 
if (v_isShared_5069_ == 0)
{
v___x_5071_ = v___x_5068_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_a_5066_);
v___x_5071_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
return v___x_5071_;
}
}
}
}
}
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
lean_dec(v_a_5009_);
lean_dec(v_a_5006_);
lean_dec_ref(v___x_4990_);
lean_dec(v___x_4989_);
lean_dec(v___x_4988_);
lean_dec(v_levelParams_4986_);
v_a_5096_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_5011_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5011_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5101_; 
if (v_isShared_5099_ == 0)
{
v___x_5101_ = v___x_5098_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5096_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
}
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5111_; 
lean_dec(v_a_5006_);
lean_dec_ref(v___x_4990_);
lean_dec(v___x_4989_);
lean_dec(v___x_4988_);
lean_dec(v_levelParams_4986_);
v_a_5104_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_5008_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_5008_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5109_; 
if (v_isShared_5107_ == 0)
{
v___x_5109_ = v___x_5106_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
}
}
else
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
lean_dec_ref(v___x_4990_);
lean_dec(v___x_4989_);
lean_dec(v___x_4988_);
lean_dec(v_levelParams_4986_);
v_a_5112_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5114_ = v___x_5005_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5005_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
v___jp_4998_:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4999_ = lean_box(0);
v___x_5000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
return v___x_5000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed(lean_object* v_levelParams_5120_, lean_object* v_declName_5121_, lean_object* v___x_5122_, lean_object* v___x_5123_, lean_object* v___x_5124_, lean_object* v_xs_5125_, lean_object* v_body_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
lean_object* v_res_5132_; 
v_res_5132_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(v_levelParams_5120_, v_declName_5121_, v___x_5122_, v___x_5123_, v___x_5124_, v_xs_5125_, v_body_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
lean_dec(v___y_5130_);
lean_dec_ref(v___y_5129_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
lean_dec_ref(v_xs_5125_);
return v_res_5132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(uint8_t v___x_5133_, lean_object* v_value_5134_, lean_object* v___f_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_){
_start:
{
lean_object* v___x_5141_; lean_object* v_fileName_5142_; lean_object* v_fileMap_5143_; lean_object* v_options_5144_; lean_object* v_currRecDepth_5145_; lean_object* v_ref_5146_; lean_object* v_currNamespace_5147_; lean_object* v_openDecls_5148_; lean_object* v_initHeartbeats_5149_; lean_object* v_maxHeartbeats_5150_; lean_object* v_quotContext_5151_; lean_object* v_currMacroScope_5152_; lean_object* v_cancelTk_x3f_5153_; uint8_t v_suppressElabErrors_5154_; lean_object* v_inheritedTraceOptions_5155_; lean_object* v_env_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; uint8_t v___x_5160_; lean_object* v_fileName_5162_; lean_object* v_fileMap_5163_; lean_object* v_currRecDepth_5164_; lean_object* v_ref_5165_; lean_object* v_currNamespace_5166_; lean_object* v_openDecls_5167_; lean_object* v_initHeartbeats_5168_; lean_object* v_maxHeartbeats_5169_; lean_object* v_quotContext_5170_; lean_object* v_currMacroScope_5171_; lean_object* v_cancelTk_x3f_5172_; uint8_t v_suppressElabErrors_5173_; lean_object* v_inheritedTraceOptions_5174_; lean_object* v___y_5175_; uint8_t v___y_5181_; uint8_t v___x_5202_; 
v___x_5141_ = lean_st_ref_get(v___y_5139_);
v_fileName_5142_ = lean_ctor_get(v___y_5138_, 0);
v_fileMap_5143_ = lean_ctor_get(v___y_5138_, 1);
v_options_5144_ = lean_ctor_get(v___y_5138_, 2);
v_currRecDepth_5145_ = lean_ctor_get(v___y_5138_, 3);
v_ref_5146_ = lean_ctor_get(v___y_5138_, 5);
v_currNamespace_5147_ = lean_ctor_get(v___y_5138_, 6);
v_openDecls_5148_ = lean_ctor_get(v___y_5138_, 7);
v_initHeartbeats_5149_ = lean_ctor_get(v___y_5138_, 8);
v_maxHeartbeats_5150_ = lean_ctor_get(v___y_5138_, 9);
v_quotContext_5151_ = lean_ctor_get(v___y_5138_, 10);
v_currMacroScope_5152_ = lean_ctor_get(v___y_5138_, 11);
v_cancelTk_x3f_5153_ = lean_ctor_get(v___y_5138_, 12);
v_suppressElabErrors_5154_ = lean_ctor_get_uint8(v___y_5138_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5155_ = lean_ctor_get(v___y_5138_, 13);
v_env_5156_ = lean_ctor_get(v___x_5141_, 0);
lean_inc_ref(v_env_5156_);
lean_dec(v___x_5141_);
v___x_5157_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_5144_);
v___x_5158_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_options_5144_, v___x_5157_, v___x_5133_);
v___x_5159_ = l_Lean_diagnostics;
v___x_5160_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v___x_5158_, v___x_5159_);
v___x_5202_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5156_);
lean_dec_ref(v_env_5156_);
if (v___x_5202_ == 0)
{
if (v___x_5160_ == 0)
{
v_fileName_5162_ = v_fileName_5142_;
v_fileMap_5163_ = v_fileMap_5143_;
v_currRecDepth_5164_ = v_currRecDepth_5145_;
v_ref_5165_ = v_ref_5146_;
v_currNamespace_5166_ = v_currNamespace_5147_;
v_openDecls_5167_ = v_openDecls_5148_;
v_initHeartbeats_5168_ = v_initHeartbeats_5149_;
v_maxHeartbeats_5169_ = v_maxHeartbeats_5150_;
v_quotContext_5170_ = v_quotContext_5151_;
v_currMacroScope_5171_ = v_currMacroScope_5152_;
v_cancelTk_x3f_5172_ = v_cancelTk_x3f_5153_;
v_suppressElabErrors_5173_ = v_suppressElabErrors_5154_;
v_inheritedTraceOptions_5174_ = v_inheritedTraceOptions_5155_;
v___y_5175_ = v___y_5139_;
goto v___jp_5161_;
}
else
{
v___y_5181_ = v___x_5202_;
goto v___jp_5180_;
}
}
else
{
v___y_5181_ = v___x_5160_;
goto v___jp_5180_;
}
v___jp_5161_:
{
lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; 
v___x_5176_ = l_Lean_maxRecDepth;
v___x_5177_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v___x_5158_, v___x_5176_);
lean_inc_ref(v_inheritedTraceOptions_5174_);
lean_inc(v_cancelTk_x3f_5172_);
lean_inc(v_currMacroScope_5171_);
lean_inc(v_quotContext_5170_);
lean_inc(v_maxHeartbeats_5169_);
lean_inc(v_initHeartbeats_5168_);
lean_inc(v_openDecls_5167_);
lean_inc(v_currNamespace_5166_);
lean_inc(v_ref_5165_);
lean_inc(v_currRecDepth_5164_);
lean_inc_ref(v_fileMap_5163_);
lean_inc_ref(v_fileName_5162_);
v___x_5178_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5178_, 0, v_fileName_5162_);
lean_ctor_set(v___x_5178_, 1, v_fileMap_5163_);
lean_ctor_set(v___x_5178_, 2, v___x_5158_);
lean_ctor_set(v___x_5178_, 3, v_currRecDepth_5164_);
lean_ctor_set(v___x_5178_, 4, v___x_5177_);
lean_ctor_set(v___x_5178_, 5, v_ref_5165_);
lean_ctor_set(v___x_5178_, 6, v_currNamespace_5166_);
lean_ctor_set(v___x_5178_, 7, v_openDecls_5167_);
lean_ctor_set(v___x_5178_, 8, v_initHeartbeats_5168_);
lean_ctor_set(v___x_5178_, 9, v_maxHeartbeats_5169_);
lean_ctor_set(v___x_5178_, 10, v_quotContext_5170_);
lean_ctor_set(v___x_5178_, 11, v_currMacroScope_5171_);
lean_ctor_set(v___x_5178_, 12, v_cancelTk_x3f_5172_);
lean_ctor_set(v___x_5178_, 13, v_inheritedTraceOptions_5174_);
lean_ctor_set_uint8(v___x_5178_, sizeof(void*)*14, v___x_5160_);
lean_ctor_set_uint8(v___x_5178_, sizeof(void*)*14 + 1, v_suppressElabErrors_5173_);
v___x_5179_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_value_5134_, v___f_5135_, v___x_5133_, v___y_5136_, v___y_5137_, v___x_5178_, v___y_5175_);
lean_dec_ref(v___x_5178_);
return v___x_5179_;
}
v___jp_5180_:
{
if (v___y_5181_ == 0)
{
lean_object* v___x_5182_; lean_object* v_env_5183_; lean_object* v_nextMacroScope_5184_; lean_object* v_ngen_5185_; lean_object* v_auxDeclNGen_5186_; lean_object* v_traceState_5187_; lean_object* v_messages_5188_; lean_object* v_infoState_5189_; lean_object* v_snapshotTasks_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5200_; 
v___x_5182_ = lean_st_ref_take(v___y_5139_);
v_env_5183_ = lean_ctor_get(v___x_5182_, 0);
v_nextMacroScope_5184_ = lean_ctor_get(v___x_5182_, 1);
v_ngen_5185_ = lean_ctor_get(v___x_5182_, 2);
v_auxDeclNGen_5186_ = lean_ctor_get(v___x_5182_, 3);
v_traceState_5187_ = lean_ctor_get(v___x_5182_, 4);
v_messages_5188_ = lean_ctor_get(v___x_5182_, 6);
v_infoState_5189_ = lean_ctor_get(v___x_5182_, 7);
v_snapshotTasks_5190_ = lean_ctor_get(v___x_5182_, 8);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5200_ == 0)
{
lean_object* v_unused_5201_; 
v_unused_5201_ = lean_ctor_get(v___x_5182_, 5);
lean_dec(v_unused_5201_);
v___x_5192_ = v___x_5182_;
v_isShared_5193_ = v_isSharedCheck_5200_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_snapshotTasks_5190_);
lean_inc(v_infoState_5189_);
lean_inc(v_messages_5188_);
lean_inc(v_traceState_5187_);
lean_inc(v_auxDeclNGen_5186_);
lean_inc(v_ngen_5185_);
lean_inc(v_nextMacroScope_5184_);
lean_inc(v_env_5183_);
lean_dec(v___x_5182_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5200_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5197_; 
v___x_5194_ = l_Lean_Kernel_enableDiag(v_env_5183_, v___x_5160_);
v___x_5195_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_5193_ == 0)
{
lean_ctor_set(v___x_5192_, 5, v___x_5195_);
lean_ctor_set(v___x_5192_, 0, v___x_5194_);
v___x_5197_ = v___x_5192_;
goto v_reusejp_5196_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v___x_5194_);
lean_ctor_set(v_reuseFailAlloc_5199_, 1, v_nextMacroScope_5184_);
lean_ctor_set(v_reuseFailAlloc_5199_, 2, v_ngen_5185_);
lean_ctor_set(v_reuseFailAlloc_5199_, 3, v_auxDeclNGen_5186_);
lean_ctor_set(v_reuseFailAlloc_5199_, 4, v_traceState_5187_);
lean_ctor_set(v_reuseFailAlloc_5199_, 5, v___x_5195_);
lean_ctor_set(v_reuseFailAlloc_5199_, 6, v_messages_5188_);
lean_ctor_set(v_reuseFailAlloc_5199_, 7, v_infoState_5189_);
lean_ctor_set(v_reuseFailAlloc_5199_, 8, v_snapshotTasks_5190_);
v___x_5197_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5196_;
}
v_reusejp_5196_:
{
lean_object* v___x_5198_; 
v___x_5198_ = lean_st_ref_set(v___y_5139_, v___x_5197_);
v_fileName_5162_ = v_fileName_5142_;
v_fileMap_5163_ = v_fileMap_5143_;
v_currRecDepth_5164_ = v_currRecDepth_5145_;
v_ref_5165_ = v_ref_5146_;
v_currNamespace_5166_ = v_currNamespace_5147_;
v_openDecls_5167_ = v_openDecls_5148_;
v_initHeartbeats_5168_ = v_initHeartbeats_5149_;
v_maxHeartbeats_5169_ = v_maxHeartbeats_5150_;
v_quotContext_5170_ = v_quotContext_5151_;
v_currMacroScope_5171_ = v_currMacroScope_5152_;
v_cancelTk_x3f_5172_ = v_cancelTk_x3f_5153_;
v_suppressElabErrors_5173_ = v_suppressElabErrors_5154_;
v_inheritedTraceOptions_5174_ = v_inheritedTraceOptions_5155_;
v___y_5175_ = v___y_5139_;
goto v___jp_5161_;
}
}
}
else
{
v_fileName_5162_ = v_fileName_5142_;
v_fileMap_5163_ = v_fileMap_5143_;
v_currRecDepth_5164_ = v_currRecDepth_5145_;
v_ref_5165_ = v_ref_5146_;
v_currNamespace_5166_ = v_currNamespace_5147_;
v_openDecls_5167_ = v_openDecls_5148_;
v_initHeartbeats_5168_ = v_initHeartbeats_5149_;
v_maxHeartbeats_5169_ = v_maxHeartbeats_5150_;
v_quotContext_5170_ = v_quotContext_5151_;
v_currMacroScope_5171_ = v_currMacroScope_5152_;
v_cancelTk_x3f_5172_ = v_cancelTk_x3f_5153_;
v_suppressElabErrors_5173_ = v_suppressElabErrors_5154_;
v_inheritedTraceOptions_5174_ = v_inheritedTraceOptions_5155_;
v___y_5175_ = v___y_5139_;
goto v___jp_5161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed(lean_object* v___x_5203_, lean_object* v_value_5204_, lean_object* v___f_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_){
_start:
{
uint8_t v___x_5501__boxed_5211_; lean_object* v_res_5212_; 
v___x_5501__boxed_5211_ = lean_unbox(v___x_5203_);
v_res_5212_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(v___x_5501__boxed_5211_, v_value_5204_, v___f_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_);
lean_dec(v___y_5209_);
lean_dec_ref(v___y_5208_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
return v_res_5212_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_5214_; lean_object* v___x_5215_; 
v___x_5214_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0));
v___x_5215_ = l_Lean_stringToMessageData(v___x_5214_);
return v___x_5215_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3(void){
_start:
{
lean_object* v___x_5217_; lean_object* v___x_5218_; 
v___x_5217_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__2));
v___x_5218_ = l_Lean_stringToMessageData(v___x_5217_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object* v_preDef_5219_, lean_object* v_unaryPreDefName_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_){
_start:
{
lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v_env_5228_; lean_object* v_levelParams_5229_; lean_object* v_declName_5230_; lean_object* v_value_5231_; lean_object* v_env_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___f_5242_; lean_object* v___x_5243_; lean_object* v___f_5244_; uint8_t v___x_5245_; lean_object* v___x_5246_; lean_object* v___f_5247_; lean_object* v___x_5248_; 
v___x_5226_ = lean_st_ref_get(v_a_5224_);
v___x_5227_ = lean_st_ref_get(v_a_5224_);
v_env_5228_ = lean_ctor_get(v___x_5226_, 0);
lean_inc_ref(v_env_5228_);
lean_dec(v___x_5226_);
v_levelParams_5229_ = lean_ctor_get(v_preDef_5219_, 1);
lean_inc(v_levelParams_5229_);
v_declName_5230_ = lean_ctor_get(v_preDef_5219_, 3);
lean_inc_n(v_declName_5230_, 2);
v_value_5231_ = lean_ctor_get(v_preDef_5219_, 7);
lean_inc_ref(v_value_5231_);
lean_dec_ref(v_preDef_5219_);
v_env_5232_ = lean_ctor_get(v___x_5227_, 0);
lean_inc_ref(v_env_5232_);
lean_dec(v___x_5227_);
v___x_5233_ = l_Lean_Meta_unfoldThmSuffix;
v___x_5234_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5228_, v_declName_5230_, v___x_5233_);
v___x_5235_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5232_, v_unaryPreDefName_5220_, v___x_5233_);
v___x_5236_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1);
lean_inc(v___x_5234_);
v___x_5237_ = l_Lean_MessageData_ofName(v___x_5234_);
v___x_5238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5238_, 0, v___x_5236_);
lean_ctor_set(v___x_5238_, 1, v___x_5237_);
v___x_5239_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3);
v___x_5240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5240_, 0, v___x_5238_);
lean_ctor_set(v___x_5240_, 1, v___x_5239_);
lean_inc(v___x_5235_);
v___x_5241_ = l_Lean_MessageData_ofName(v___x_5235_);
lean_inc_ref(v___x_5241_);
v___f_5242_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5242_, 0, v_levelParams_5229_);
lean_closure_set(v___f_5242_, 1, v_declName_5230_);
lean_closure_set(v___f_5242_, 2, v___x_5235_);
lean_closure_set(v___f_5242_, 3, v___x_5234_);
lean_closure_set(v___f_5242_, 4, v___x_5241_);
v___x_5243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5243_, 0, v___x_5240_);
lean_ctor_set(v___x_5243_, 1, v___x_5241_);
v___f_5244_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_5244_, 0, v___x_5243_);
v___x_5245_ = 0;
v___x_5246_ = lean_box(v___x_5245_);
v___f_5247_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_5247_, 0, v___x_5246_);
lean_closure_set(v___f_5247_, 1, v_value_5231_);
lean_closure_set(v___f_5247_, 2, v___f_5242_);
v___x_5248_ = l_Lean_Meta_mapErrorImp___redArg(v___f_5247_, v___f_5244_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_);
if (lean_obj_tag(v___x_5248_) == 0)
{
lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5256_; 
v_a_5249_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5251_ = v___x_5248_;
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5248_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5254_; 
if (v_isShared_5252_ == 0)
{
v___x_5254_ = v___x_5251_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_a_5249_);
v___x_5254_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
return v___x_5254_;
}
}
}
else
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5264_; 
v_a_5257_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5259_ = v___x_5248_;
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5248_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5262_; 
if (v_isShared_5260_ == 0)
{
v___x_5262_ = v___x_5259_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5257_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___boxed(lean_object* v_preDef_5265_, lean_object* v_unaryPreDefName_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_){
_start:
{
lean_object* v_res_5272_; 
v_res_5272_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_preDef_5265_, v_unaryPreDefName_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_);
lean_dec(v_a_5270_);
lean_dec_ref(v_a_5269_);
lean_dec(v_a_5268_);
lean_dec_ref(v_a_5267_);
return v_res_5272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5317_; uint8_t v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; 
v___x_5317_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5318_ = 0;
v___x_5319_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5320_ = l_Lean_registerTraceClass(v___x_5317_, v___x_5318_, v___x_5319_);
return v___x_5320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2____boxed(lean_object* v_a_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_();
return v_res_5322_;
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
