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
uint8_t lean_bool_not(uint8_t);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_7427__boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v___x_7427__boxed_157_ = lean_unbox(v___x_155_);
v_res_158_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(v___x_7427__boxed_157_, v_x_156_);
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
uint8_t v___x_7435__boxed_188_; uint8_t v___x_7436__boxed_189_; lean_object* v_res_190_; 
v___x_7435__boxed_188_ = lean_unbox(v___x_179_);
v___x_7436__boxed_189_ = lean_unbox(v___x_180_);
v_res_190_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(v___x_177_, v___x_178_, v___x_7435__boxed_188_, v___x_7436__boxed_189_, v_ys_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
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
size_t v_x_7613__boxed_378_; size_t v_x_7614__boxed_379_; lean_object* v_res_380_; 
v_x_7613__boxed_378_ = lean_unbox_usize(v_x_374_);
lean_dec(v_x_374_);
v_x_7614__boxed_379_ = lean_unbox_usize(v_x_375_);
lean_dec(v_x_375_);
v_res_380_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_373_, v_x_7613__boxed_378_, v_x_7614__boxed_379_, v_x_376_, v_x_377_);
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
lean_object* v___x_392_; lean_object* v_mctx_393_; lean_object* v_cache_394_; lean_object* v_zetaDeltaFVarIds_395_; lean_object* v_postponed_396_; lean_object* v_diag_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_425_; 
v___x_392_ = lean_st_ref_take(v___y_390_);
v_mctx_393_ = lean_ctor_get(v___x_392_, 0);
v_cache_394_ = lean_ctor_get(v___x_392_, 1);
v_zetaDeltaFVarIds_395_ = lean_ctor_get(v___x_392_, 2);
v_postponed_396_ = lean_ctor_get(v___x_392_, 3);
v_diag_397_ = lean_ctor_get(v___x_392_, 4);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_425_ == 0)
{
v___x_399_ = v___x_392_;
v_isShared_400_ = v_isSharedCheck_425_;
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
v_isShared_400_ = v_isSharedCheck_425_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_depth_401_; lean_object* v_levelAssignDepth_402_; lean_object* v_lmvarCounter_403_; lean_object* v_mvarCounter_404_; lean_object* v_lDecls_405_; lean_object* v_decls_406_; lean_object* v_userNames_407_; lean_object* v_lAssignment_408_; lean_object* v_eAssignment_409_; lean_object* v_dAssignment_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_424_; 
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
v_isSharedCheck_424_ = !lean_is_exclusive(v_mctx_393_);
if (v_isSharedCheck_424_ == 0)
{
v___x_412_ = v_mctx_393_;
v_isShared_413_ = v_isSharedCheck_424_;
goto v_resetjp_411_;
}
else
{
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
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_424_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_eAssignment_409_, v_mvarId_388_, v_val_389_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 8, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_depth_401_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_levelAssignDepth_402_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_lmvarCounter_403_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_mvarCounter_404_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_lDecls_405_);
lean_ctor_set(v_reuseFailAlloc_423_, 5, v_decls_406_);
lean_ctor_set(v_reuseFailAlloc_423_, 6, v_userNames_407_);
lean_ctor_set(v_reuseFailAlloc_423_, 7, v_lAssignment_408_);
lean_ctor_set(v_reuseFailAlloc_423_, 8, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_423_, 9, v_dAssignment_410_);
v___x_416_ = v_reuseFailAlloc_423_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_416_);
v___x_418_ = v___x_399_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_cache_394_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_zetaDeltaFVarIds_395_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_postponed_396_);
lean_ctor_set(v_reuseFailAlloc_422_, 4, v_diag_397_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_st_ref_set(v___y_390_, v___x_418_);
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
size_t v_x_8392__boxed_743_; size_t v_x_8393__boxed_744_; lean_object* v_res_745_; 
v_x_8392__boxed_743_ = lean_unbox_usize(v_x_739_);
lean_dec(v_x_739_);
v_x_8393__boxed_744_ = lean_unbox_usize(v_x_740_);
lean_dec(v_x_740_);
v_res_745_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(v_00_u03b2_737_, v_x_738_, v_x_8392__boxed_743_, v_x_8393__boxed_744_, v_x_741_, v_x_742_);
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
uint8_t v___y_850_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = lean_array_get_size(v_xs_839_);
v___x_876_ = lean_nat_dec_eq(v___x_875_, v___x_838_);
if (v___x_876_ == 0)
{
v___y_850_ = v___x_876_;
goto v___jp_849_;
}
else
{
uint8_t v___x_877_; 
v___x_877_ = l_Lean_Expr_isForall(v_t_840_);
v___y_850_ = v___x_877_;
goto v___jp_849_;
}
v___jp_846_:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_box(0);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
v___jp_849_:
{
if (v___y_850_ == 0)
{
goto v___jp_846_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; uint8_t v___x_854_; 
v___x_851_ = l_Lean_Expr_bindingBody_x21(v_t_840_);
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = lean_expr_has_loose_bvar(v___x_851_, v___x_852_);
v___x_854_ = lean_bool_not(v___x_853_);
if (v___x_854_ == 0)
{
lean_dec_ref(v___x_851_);
goto v___jp_846_;
}
else
{
uint8_t v___x_855_; uint8_t v___x_856_; lean_object* v___x_857_; 
v___x_855_ = 0;
v___x_856_ = 1;
v___x_857_ = l_Lean_Meta_mkLambdaFVars(v_xs_839_, v___x_851_, v___x_855_, v___y_850_, v___x_855_, v___y_850_, v___x_856_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
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
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
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
lean_object* v___f_938_; lean_object* v___x_788__overap_939_; lean_object* v___x_940_; 
v___f_938_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_788__overap_939_ = lean_panic_fn_borrowed(v___f_938_, v_msg_932_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
v___x_940_ = lean_apply_5(v___x_788__overap_939_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, lean_box(0));
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1___boxed(lean_object* v_msg_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v_msg_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
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
v___x_971_ = lean_unsigned_to_nat(79u);
v___x_972_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0));
v___x_973_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_974_ = l_mkPanicMessageWithDecl(v___x_973_, v___x_972_, v___x_971_, v___x_970_, v___x_969_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(lean_object* v_mvarId_977_, lean_object* v_e_978_, lean_object* v_matcherInfo_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; lean_object* v_a_986_; uint8_t v___x_987_; 
v___x_985_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_978_, v_a_983_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_985_);
v___x_987_ = lean_unbox(v_a_986_);
if (v___x_987_ == 0)
{
lean_object* v_numParams_988_; lean_object* v_numDiscrs_989_; lean_object* v_nargs_990_; lean_object* v___x_991_; lean_object* v_dummy_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v_numParams_988_ = lean_ctor_get(v_matcherInfo_979_, 0);
v_numDiscrs_989_ = lean_ctor_get(v_matcherInfo_979_, 1);
v_nargs_990_ = l_Lean_Expr_getAppNumArgs(v_e_978_);
v___x_991_ = l_Lean_instInhabitedExpr;
v_dummy_992_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_990_);
v___x_993_ = lean_mk_array(v_nargs_990_, v_dummy_992_);
v___x_994_ = lean_unsigned_to_nat(1u);
v___x_995_ = lean_nat_sub(v_nargs_990_, v___x_994_);
lean_dec(v_nargs_990_);
v___x_996_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_978_, v___x_993_, v___x_995_);
v___x_997_ = lean_nat_add(v_numParams_988_, v_numDiscrs_989_);
v___x_998_ = lean_array_get(v___x_991_, v___x_996_, v___x_997_);
lean_dec(v___x_997_);
lean_dec_ref(v___x_996_);
v___x_999_ = l_Lean_Expr_isFVar(v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec(v___x_998_);
lean_dec(v_a_986_);
lean_dec(v_mvarId_977_);
v___x_1000_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2);
v___x_1001_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v___x_1000_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1002_ = l_Lean_Expr_fvarId_x21(v___x_998_);
lean_dec(v___x_998_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3));
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_unbox(v_a_986_);
lean_dec(v_a_986_);
v___x_1006_ = l_Lean_MVarId_cases(v_mvarId_977_, v___x_1002_, v___x_1003_, v___x_1005_, v___x_1004_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1018_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1018_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1018_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
size_t v_sz_1011_; size_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v_sz_1011_ = lean_array_size(v_a_1007_);
v___x_1012_ = ((size_t)0ULL);
v___x_1013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_1011_, v___x_1012_, v_a_1007_);
v___x_1014_ = lean_array_to_list(v___x_1013_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1014_);
v___x_1016_ = v___x_1009_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_a_1019_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1006_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1006_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
else
{
lean_object* v___x_1027_; 
lean_dec(v_a_986_);
v___x_1027_ = l_Lean_Meta_Split_splitMatch(v_mvarId_977_, v_e_978_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___boxed(lean_object* v_mvarId_1028_, lean_object* v_e_1029_, lean_object* v_matcherInfo_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v_mvarId_1028_, v_e_1029_, v_matcherInfo_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec_ref(v_matcherInfo_1030_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(lean_object* v_msg_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___f_1043_; lean_object* v___x_12211__overap_1044_; lean_object* v___x_1045_; 
v___f_1043_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_12211__overap_1044_ = lean_panic_fn_borrowed(v___f_1043_, v_msg_1037_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
v___x_1045_ = lean_apply_5(v___x_12211__overap_1044_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, lean_box(0));
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1___boxed(lean_object* v_msg_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v_msg_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(lean_object* v_type_1053_, lean_object* v_k_1054_, uint8_t v_cleanupAnnotations_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___f_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___f_1061_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1061_, 0, v_k_1054_);
v___x_1062_ = 0;
v___x_1063_ = lean_box(0);
v___x_1064_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1062_, v___x_1063_, v_type_1053_, v___f_1061_, v_cleanupAnnotations_1055_, v___x_1062_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_a_1073_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1064_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1064_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg___boxed(lean_object* v_type_1081_, lean_object* v_k_1082_, lean_object* v_cleanupAnnotations_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1089_; lean_object* v_res_1090_; 
v_cleanupAnnotations_boxed_1089_ = lean_unbox(v_cleanupAnnotations_1083_);
v_res_1090_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1081_, v_k_1082_, v_cleanupAnnotations_boxed_1089_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(lean_object* v_00_u03b1_1091_, lean_object* v_type_1092_, lean_object* v_k_1093_, uint8_t v_cleanupAnnotations_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1092_, v_k_1093_, v_cleanupAnnotations_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___boxed(lean_object* v_00_u03b1_1101_, lean_object* v_type_1102_, lean_object* v_k_1103_, lean_object* v_cleanupAnnotations_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1110_; lean_object* v_res_1111_; 
v_cleanupAnnotations_boxed_1110_ = lean_unbox(v_cleanupAnnotations_1104_);
v_res_1111_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(v_00_u03b1_1101_, v_type_1102_, v_k_1103_, v_cleanupAnnotations_boxed_1110_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(lean_object* v_e_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = l_Lean_Expr_hasMVar(v_e_1112_);
v___x_1116_ = lean_bool_not(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v_mctx_1118_; lean_object* v___x_1119_; lean_object* v_fst_1120_; lean_object* v_snd_1121_; lean_object* v___x_1122_; lean_object* v_cache_1123_; lean_object* v_zetaDeltaFVarIds_1124_; lean_object* v_postponed_1125_; lean_object* v_diag_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1135_; 
v___x_1117_ = lean_st_ref_get(v___y_1113_);
v_mctx_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc_ref(v_mctx_1118_);
lean_dec(v___x_1117_);
v___x_1119_ = l_Lean_instantiateMVarsCore(v_mctx_1118_, v_e_1112_);
v_fst_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_fst_1120_);
v_snd_1121_ = lean_ctor_get(v___x_1119_, 1);
lean_inc(v_snd_1121_);
lean_dec_ref(v___x_1119_);
v___x_1122_ = lean_st_ref_take(v___y_1113_);
v_cache_1123_ = lean_ctor_get(v___x_1122_, 1);
v_zetaDeltaFVarIds_1124_ = lean_ctor_get(v___x_1122_, 2);
v_postponed_1125_ = lean_ctor_get(v___x_1122_, 3);
v_diag_1126_ = lean_ctor_get(v___x_1122_, 4);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; 
v_unused_1136_ = lean_ctor_get(v___x_1122_, 0);
lean_dec(v_unused_1136_);
v___x_1128_ = v___x_1122_;
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_diag_1126_);
lean_inc(v_postponed_1125_);
lean_inc(v_zetaDeltaFVarIds_1124_);
lean_inc(v_cache_1123_);
lean_dec(v___x_1122_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v_snd_1121_);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_snd_1121_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_cache_1123_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_zetaDeltaFVarIds_1124_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_postponed_1125_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v_diag_1126_);
v___x_1131_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_st_ref_set(v___y_1113_, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_fst_1120_);
return v___x_1133_;
}
}
}
else
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_e_1112_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg___boxed(lean_object* v_e_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1138_, v___y_1139_);
lean_dec(v___y_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(lean_object* v_e_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1142_, v___y_1144_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___boxed(lean_object* v_e_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(v_e_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(lean_object* v_x_1156_, lean_object* v_motiveBody_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Meta_getLevel(v_motiveBody_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0___boxed(lean_object* v_x_1164_, lean_object* v_motiveBody_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(v_x_1164_, v_motiveBody_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec_ref(v_x_1164_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(lean_object* v___x_1172_, lean_object* v___x_1173_, lean_object* v_alpha_1174_, uint8_t v___x_1175_, lean_object* v_xs_1176_, lean_object* v_x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; uint8_t v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; 
v___x_1183_ = l_Lean_Level_ofNat(v___x_1172_);
v___x_1184_ = l_Lean_Expr_sort___override(v___x_1183_);
v___x_1185_ = l_Lean_Expr_forallE___override(v___x_1173_, v_alpha_1174_, v___x_1184_, v___x_1175_);
v___x_1186_ = 0;
v___x_1187_ = 1;
v___x_1188_ = 1;
v___x_1189_ = l_Lean_Meta_mkForallFVars(v_xs_1176_, v___x_1185_, v___x_1186_, v___x_1187_, v___x_1187_, v___x_1188_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed(lean_object* v___x_1190_, lean_object* v___x_1191_, lean_object* v_alpha_1192_, lean_object* v___x_1193_, lean_object* v_xs_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
uint8_t v___x_16378__boxed_1201_; lean_object* v_res_1202_; 
v___x_16378__boxed_1201_ = lean_unbox(v___x_1193_);
v_res_1202_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(v___x_1190_, v___x_1191_, v_alpha_1192_, v___x_16378__boxed_1201_, v_xs_1194_, v_x_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v_x_1195_);
lean_dec_ref(v_xs_1194_);
lean_dec(v___x_1190_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(lean_object* v___x_1209_, lean_object* v___x_1210_, lean_object* v_rel_1211_, lean_object* v___x_1212_, lean_object* v_beta_1213_, uint8_t v___x_1214_, lean_object* v_alpha_1215_, uint8_t v___x_1216_, lean_object* v_xs_1217_, lean_object* v_x_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1224_ = l_Lean_mkAppN(v___x_1209_, v_xs_1217_);
v___x_1225_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1226_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_xs_1217_);
v___x_1227_ = lean_array_push(v_xs_1217_, v___x_1210_);
v___x_1228_ = l_Lean_mkAppN(v_rel_1211_, v___x_1227_);
lean_dec_ref(v___x_1227_);
v___x_1229_ = l_Lean_Expr_bvar___override(v___x_1212_);
v___x_1230_ = l_Lean_Expr_app___override(v_beta_1213_, v___x_1229_);
v___x_1231_ = l_Lean_Expr_forallE___override(v___x_1226_, v___x_1228_, v___x_1230_, v___x_1214_);
v___x_1232_ = l_Lean_Expr_forallE___override(v___x_1225_, v_alpha_1215_, v___x_1231_, v___x_1214_);
v___x_1233_ = l_Lean_mkArrow(v___x_1232_, v___x_1224_, v___y_1221_, v___y_1222_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; uint8_t v___x_1235_; uint8_t v___x_1236_; lean_object* v___x_1237_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1233_, 1);
v___x_1235_ = 1;
v___x_1236_ = 1;
v___x_1237_ = l_Lean_Meta_mkLambdaFVars(v_xs_1217_, v_a_1234_, v___x_1216_, v___x_1235_, v___x_1216_, v___x_1235_, v___x_1236_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec_ref(v_xs_1217_);
return v___x_1237_;
}
else
{
lean_dec_ref(v_xs_1217_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed(lean_object* v___x_1238_, lean_object* v___x_1239_, lean_object* v_rel_1240_, lean_object* v___x_1241_, lean_object* v_beta_1242_, lean_object* v___x_1243_, lean_object* v_alpha_1244_, lean_object* v___x_1245_, lean_object* v_xs_1246_, lean_object* v_x_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v___x_16432__boxed_1253_; uint8_t v___x_16433__boxed_1254_; lean_object* v_res_1255_; 
v___x_16432__boxed_1253_ = lean_unbox(v___x_1243_);
v___x_16433__boxed_1254_ = lean_unbox(v___x_1245_);
v_res_1255_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(v___x_1238_, v___x_1239_, v_rel_1240_, v___x_1241_, v_beta_1242_, v___x_16432__boxed_1253_, v_alpha_1244_, v___x_16433__boxed_1254_, v_xs_1246_, v_x_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec_ref(v_x_1247_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(lean_object* v___x_1256_, lean_object* v___x_1257_, lean_object* v_f_1258_, uint8_t v___x_1259_, uint8_t v___x_1260_, lean_object* v_ys_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; 
v___x_1268_ = lean_array_get_borrowed(v___x_1256_, v_ys_1261_, v___x_1257_);
lean_inc(v___x_1268_);
v___x_1269_ = l_Lean_Expr_app___override(v_f_1258_, v___x_1268_);
v___x_1270_ = 1;
v___x_1271_ = l_Lean_Meta_mkLambdaFVars(v_ys_1261_, v___x_1269_, v___x_1259_, v___x_1260_, v___x_1259_, v___x_1260_, v___x_1270_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed(lean_object* v___x_1272_, lean_object* v___x_1273_, lean_object* v_f_1274_, lean_object* v___x_1275_, lean_object* v___x_1276_, lean_object* v_ys_1277_, lean_object* v_x_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
uint8_t v___x_16499__boxed_1284_; uint8_t v___x_16500__boxed_1285_; lean_object* v_res_1286_; 
v___x_16499__boxed_1284_ = lean_unbox(v___x_1275_);
v___x_16500__boxed_1285_ = lean_unbox(v___x_1276_);
v_res_1286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(v___x_1272_, v___x_1273_, v_f_1274_, v___x_16499__boxed_1284_, v___x_16500__boxed_1285_, v_ys_1277_, v_x_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec_ref(v_x_1278_);
lean_dec_ref(v_ys_1277_);
lean_dec(v___x_1273_);
lean_dec_ref(v___x_1272_);
return v_res_1286_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1));
v___x_1290_ = lean_unsigned_to_nat(10u);
v___x_1291_ = lean_unsigned_to_nat(146u);
v___x_1292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0));
v___x_1293_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_1294_ = l_mkPanicMessageWithDecl(v___x_1293_, v___x_1292_, v___x_1291_, v___x_1290_, v___x_1289_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v_f_1297_, uint8_t v___x_1298_, lean_object* v_a_1299_, lean_object* v_ys_1300_, lean_object* v_altBodyType_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
uint8_t v___x_1307_; 
v___x_1307_ = l_Lean_Expr_isForall(v_altBodyType_1301_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec_ref(v_ys_1300_);
lean_dec_ref(v_a_1299_);
lean_dec_ref(v_f_1297_);
lean_dec(v___x_1296_);
lean_dec_ref(v___x_1295_);
v___x_1308_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2);
v___x_1309_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v___x_1308_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___f_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1310_ = lean_box(v___x_1298_);
v___x_1311_ = lean_box(v___x_1307_);
v___f_1312_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1312_, 0, v___x_1295_);
lean_closure_set(v___f_1312_, 1, v___x_1296_);
lean_closure_set(v___f_1312_, 2, v_f_1297_);
lean_closure_set(v___f_1312_, 3, v___x_1310_);
lean_closure_set(v___f_1312_, 4, v___x_1311_);
v___x_1313_ = l_Lean_Expr_bindingDomain_x21(v_altBodyType_1301_);
v___x_1314_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_1315_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_1313_, v___x_1314_, v___f_1312_, v___x_1298_, v___x_1298_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
lean_inc_ref(v_ys_1300_);
v___x_1317_ = lean_array_push(v_ys_1300_, v_a_1316_);
v___x_1318_ = l_Lean_mkAppN(v_a_1299_, v___x_1317_);
lean_dec_ref(v___x_1317_);
v___x_1319_ = 1;
v___x_1320_ = l_Lean_Meta_mkLambdaFVars(v_ys_1300_, v___x_1318_, v___x_1298_, v___x_1307_, v___x_1298_, v___x_1307_, v___x_1319_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec_ref(v_ys_1300_);
return v___x_1320_;
}
else
{
lean_dec_ref(v_ys_1300_);
lean_dec_ref(v_a_1299_);
return v___x_1315_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed(lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v_f_1323_, lean_object* v___x_1324_, lean_object* v_a_1325_, lean_object* v_ys_1326_, lean_object* v_altBodyType_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
uint8_t v___x_16556__boxed_1333_; lean_object* v_res_1334_; 
v___x_16556__boxed_1333_ = lean_unbox(v___x_1324_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(v___x_1321_, v___x_1322_, v_f_1323_, v___x_16556__boxed_1333_, v_a_1325_, v_ys_1326_, v_altBodyType_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v_altBodyType_1327_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(lean_object* v_f_1335_, lean_object* v_as_1336_, size_t v_sz_1337_, size_t v_i_1338_, lean_object* v_b_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_usize_dec_lt(v_i_1338_, v_sz_1337_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec_ref(v_f_1335_);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v_b_1339_);
return v___x_1346_;
}
else
{
lean_object* v_snd_1347_; lean_object* v_fst_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1407_; 
v_snd_1347_ = lean_ctor_get(v_b_1339_, 1);
v_fst_1348_ = lean_ctor_get(v_b_1339_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_b_1339_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1350_ = v_b_1339_;
v_isShared_1351_ = v_isSharedCheck_1407_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_snd_1347_);
lean_inc(v_fst_1348_);
lean_dec(v_b_1339_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1407_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_array_1352_; lean_object* v_start_1353_; lean_object* v_stop_1354_; uint8_t v___x_1355_; 
v_array_1352_ = lean_ctor_get(v_snd_1347_, 0);
v_start_1353_ = lean_ctor_get(v_snd_1347_, 1);
v_stop_1354_ = lean_ctor_get(v_snd_1347_, 2);
v___x_1355_ = lean_nat_dec_lt(v_start_1353_, v_stop_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1357_; 
lean_dec_ref(v_f_1335_);
if (v_isShared_1351_ == 0)
{
v___x_1357_ = v___x_1350_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_fst_1348_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_snd_1347_);
v___x_1357_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
else
{
lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1403_; 
lean_inc(v_stop_1354_);
lean_inc(v_start_1353_);
lean_inc_ref(v_array_1352_);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_snd_1347_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; lean_object* v_unused_1405_; lean_object* v_unused_1406_; 
v_unused_1404_ = lean_ctor_get(v_snd_1347_, 2);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_snd_1347_, 1);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_snd_1347_, 0);
lean_dec(v_unused_1406_);
v___x_1361_ = v_snd_1347_;
v_isShared_1362_ = v_isSharedCheck_1403_;
goto v_resetjp_1360_;
}
else
{
lean_dec(v_snd_1347_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1403_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v_a_1363_; lean_object* v___x_1364_; 
v_a_1363_ = lean_array_uget_borrowed(v_as_1336_, v_i_1338_);
lean_inc(v___y_1343_);
lean_inc_ref(v___y_1342_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v_a_1363_);
v___x_1364_ = lean_infer_type(v_a_1363_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; lean_object* v___x_1369_; lean_object* v___f_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = l_Lean_instInhabitedExpr;
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = 0;
v___x_1369_ = lean_box(v___x_1368_);
lean_inc(v_a_1363_);
lean_inc_ref(v_f_1335_);
v___f_1370_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed), 12, 5);
lean_closure_set(v___f_1370_, 0, v___x_1366_);
lean_closure_set(v___f_1370_, 1, v___x_1367_);
lean_closure_set(v___f_1370_, 2, v_f_1335_);
lean_closure_set(v___f_1370_, 3, v___x_1369_);
lean_closure_set(v___f_1370_, 4, v_a_1363_);
v___x_1371_ = lean_array_fget_borrowed(v_array_1352_, v_start_1353_);
lean_inc(v___x_1371_);
v___x_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
v___x_1373_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1365_, v___x_1372_, v___f_1370_, v___x_1368_, v___x_1368_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1375_ = lean_unsigned_to_nat(1u);
v___x_1376_ = lean_nat_add(v_start_1353_, v___x_1375_);
lean_dec(v_start_1353_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v___x_1376_);
v___x_1378_ = v___x_1361_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_array_1352_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_stop_1354_);
v___x_1378_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1379_ = l_Lean_Expr_app___override(v_fst_1348_, v_a_1374_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1378_);
lean_ctor_set(v___x_1350_, 0, v___x_1379_);
v___x_1381_ = v___x_1350_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1378_);
v___x_1381_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
size_t v___x_1382_; size_t v___x_1383_; 
v___x_1382_ = ((size_t)1ULL);
v___x_1383_ = lean_usize_add(v_i_1338_, v___x_1382_);
v_i_1338_ = v___x_1383_;
v_b_1339_ = v___x_1381_;
goto _start;
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_del_object(v___x_1361_);
lean_dec(v_stop_1354_);
lean_dec(v_start_1353_);
lean_dec_ref(v_array_1352_);
lean_del_object(v___x_1350_);
lean_dec(v_fst_1348_);
lean_dec_ref(v_f_1335_);
v_a_1387_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1373_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1373_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_del_object(v___x_1361_);
lean_dec(v_stop_1354_);
lean_dec(v_start_1353_);
lean_dec_ref(v_array_1352_);
lean_del_object(v___x_1350_);
lean_dec(v_fst_1348_);
lean_dec_ref(v_f_1335_);
v_a_1395_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1364_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1364_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___boxed(lean_object* v_f_1408_, lean_object* v_as_1409_, lean_object* v_sz_1410_, lean_object* v_i_1411_, lean_object* v_b_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
size_t v_sz_boxed_1418_; size_t v_i_boxed_1419_; lean_object* v_res_1420_; 
v_sz_boxed_1418_ = lean_unbox_usize(v_sz_1410_);
lean_dec(v_sz_1410_);
v_i_boxed_1419_ = lean_unbox_usize(v_i_1411_);
lean_dec(v_i_1411_);
v_res_1420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1408_, v_as_1409_, v_sz_boxed_1418_, v_i_boxed_1419_, v_b_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec_ref(v_as_1409_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(lean_object* v_as_x27_1421_, lean_object* v_b_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
if (lean_obj_tag(v_as_x27_1421_) == 0)
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_b_1422_);
return v___x_1428_;
}
else
{
lean_object* v_head_1429_; lean_object* v_tail_1430_; uint8_t v___x_1431_; lean_object* v___x_1432_; 
v_head_1429_ = lean_ctor_get(v_as_x27_1421_, 0);
v_tail_1430_ = lean_ctor_get(v_as_x27_1421_, 1);
v___x_1431_ = 1;
lean_inc(v_head_1429_);
v___x_1432_ = l_Lean_MVarId_refl(v_head_1429_, v___x_1431_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1433_; 
lean_dec_ref_known(v___x_1432_, 1);
v___x_1433_ = lean_box(0);
v_as_x27_1421_ = v_tail_1430_;
v_b_1422_ = v___x_1433_;
goto _start;
}
else
{
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg___boxed(lean_object* v_as_x27_1435_, lean_object* v_b_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_1435_, v_b_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v_as_x27_1435_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(lean_object* v___x_1443_, lean_object* v_matcherInfo_1444_, lean_object* v___x_1445_, lean_object* v___x_1446_, lean_object* v_f_1447_, lean_object* v_discrs_1448_, lean_object* v___x_1449_, lean_object* v_rel_1450_, lean_object* v___x_1451_, uint8_t v___x_1452_, lean_object* v_alpha_1453_, lean_object* v___x_1454_, lean_object* v_beta_1455_, lean_object* v___x_1456_, uint8_t v___x_1457_, lean_object* v___x_1458_, lean_object* v___x_1459_, lean_object* v___x_1460_, lean_object* v_alts_1461_, lean_object* v_x_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; size_t v_sz_1473_; size_t v___x_1474_; lean_object* v___x_1475_; 
v___x_1468_ = l_Lean_mkAppN(v___x_1443_, v_alts_1461_);
lean_inc_ref(v_matcherInfo_1444_);
v___x_1469_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_matcherInfo_1444_);
v___x_1470_ = lean_array_get_size(v___x_1469_);
v___x_1471_ = l_Array_toSubarray___redArg(v___x_1469_, v___x_1445_, v___x_1470_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1446_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v_sz_1473_ = lean_array_size(v_alts_1461_);
v___x_1474_ = ((size_t)0ULL);
lean_inc_ref(v_f_1447_);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1447_, v_alts_1461_, v_sz_1473_, v___x_1474_, v___x_1472_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v_fst_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1571_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v_fst_1477_ = lean_ctor_get(v_a_1476_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_a_1476_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v_a_1476_, 1);
lean_dec(v_unused_1572_);
v___x_1479_ = v_a_1476_;
v_isShared_1480_ = v_isSharedCheck_1571_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_fst_1477_);
lean_dec(v_a_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1571_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1481_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1482_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_discrs_1448_);
v___x_1483_ = lean_array_push(v_discrs_1448_, v___x_1449_);
lean_inc_ref(v_rel_1450_);
v___x_1484_ = l_Lean_mkAppN(v_rel_1450_, v___x_1483_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = l_Lean_Expr_bvar___override(v___x_1451_);
lean_inc_ref(v_f_1447_);
v___x_1486_ = l_Lean_Expr_app___override(v_f_1447_, v___x_1485_);
v___x_1487_ = l_Lean_Expr_lam___override(v___x_1482_, v___x_1484_, v___x_1486_, v___x_1452_);
lean_inc_ref(v_alpha_1453_);
v___x_1488_ = l_Lean_Expr_lam___override(v___x_1481_, v_alpha_1453_, v___x_1487_, v___x_1452_);
v___x_1489_ = l_Lean_Expr_app___override(v___x_1468_, v___x_1488_);
lean_inc(v_fst_1477_);
v___x_1490_ = l_Lean_Meta_mkEq(v___x_1489_, v_fst_1477_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc_n(v_a_1491_, 2);
lean_dec_ref_known(v___x_1490_, 1);
v___x_1492_ = lean_box(0);
v___x_1493_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1491_, v___x_1492_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v___x_1495_ = l_Lean_Expr_mvarId_x21(v_a_1494_);
v___x_1496_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v___x_1495_, v_fst_1477_, v_matcherInfo_1444_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec_ref(v_matcherInfo_1444_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = lean_box(0);
v___x_1499_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_a_1497_, v___x_1498_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v_a_1497_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v___x_1500_; lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref_known(v___x_1499_, 1);
v___x_1500_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_1494_, v___y_1464_);
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1546_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1546_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; 
v___x_1505_ = lean_unsigned_to_nat(5u);
v___x_1506_ = lean_mk_empty_array_with_capacity(v___x_1505_);
v___x_1507_ = lean_array_push(v___x_1506_, v___x_1454_);
v___x_1508_ = lean_array_push(v___x_1507_, v_alpha_1453_);
v___x_1509_ = lean_array_push(v___x_1508_, v_beta_1455_);
v___x_1510_ = lean_array_push(v___x_1509_, v_f_1447_);
v___x_1511_ = lean_array_push(v___x_1510_, v_rel_1450_);
v___x_1512_ = l_Array_append___redArg(v___x_1456_, v___x_1511_);
lean_dec_ref(v___x_1511_);
v___x_1513_ = l_Array_append___redArg(v___x_1512_, v_discrs_1448_);
lean_dec_ref(v_discrs_1448_);
v___x_1514_ = l_Array_append___redArg(v___x_1513_, v_alts_1461_);
v___x_1515_ = 1;
v___x_1516_ = 1;
v___x_1517_ = l_Lean_Meta_mkForallFVars(v___x_1514_, v_a_1491_, v___x_1457_, v___x_1515_, v___x_1515_, v___x_1516_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = l_Lean_Meta_mkLambdaFVars(v___x_1514_, v_a_1501_, v___x_1457_, v___x_1515_, v___x_1457_, v___x_1515_, v___x_1516_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec_ref(v___x_1514_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
lean_inc(v___x_1458_);
v___x_1521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1458_);
lean_ctor_set(v___x_1521_, 1, v___x_1459_);
lean_ctor_set(v___x_1521_, 2, v_a_1518_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set_tag(v___x_1479_, 1);
lean_ctor_set(v___x_1479_, 1, v___x_1460_);
lean_ctor_set(v___x_1479_, 0, v___x_1458_);
v___x_1523_ = v___x_1479_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___x_1460_);
v___x_1523_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1521_);
lean_ctor_set(v___x_1524_, 1, v_a_1520_);
lean_ctor_set(v___x_1524_, 2, v___x_1523_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set_tag(v___x_1503_, 2);
lean_ctor_set(v___x_1503_, 0, v___x_1524_);
v___x_1526_ = v___x_1503_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_addDecl(v___x_1526_, v___x_1457_, v___y_1465_, v___y_1466_);
return v___x_1527_;
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec(v_a_1518_);
lean_del_object(v___x_1503_);
lean_del_object(v___x_1479_);
lean_dec(v___x_1460_);
lean_dec(v___x_1459_);
lean_dec(v___x_1458_);
v_a_1530_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1519_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1519_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref(v___x_1514_);
lean_del_object(v___x_1503_);
lean_dec(v_a_1501_);
lean_del_object(v___x_1479_);
lean_dec(v___x_1460_);
lean_dec(v___x_1459_);
lean_dec(v___x_1458_);
v_a_1538_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1517_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1517_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
else
{
lean_dec(v_a_1494_);
lean_dec(v_a_1491_);
lean_del_object(v___x_1479_);
lean_dec(v___x_1460_);
lean_dec(v___x_1459_);
lean_dec(v___x_1458_);
lean_dec_ref(v___x_1456_);
lean_dec_ref(v_beta_1455_);
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_alpha_1453_);
lean_dec_ref(v_rel_1450_);
lean_dec_ref(v_discrs_1448_);
lean_dec_ref(v_f_1447_);
return v___x_1499_;
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_a_1494_);
lean_dec(v_a_1491_);
lean_del_object(v___x_1479_);
lean_dec(v___x_1460_);
lean_dec(v___x_1459_);
lean_dec(v___x_1458_);
lean_dec_ref(v___x_1456_);
lean_dec_ref(v_beta_1455_);
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_alpha_1453_);
lean_dec_ref(v_rel_1450_);
lean_dec_ref(v_discrs_1448_);
lean_dec_ref(v_f_1447_);
v_a_1547_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1496_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1496_);
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
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_a_1491_);
lean_del_object(v___x_1479_);
lean_dec(v_fst_1477_);
lean_dec(v___x_1460_);
lean_dec(v___x_1459_);
lean_dec(v___x_1458_);
lean_dec_ref(v___x_1456_);
lean_dec_ref(v_beta_1455_);
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_alpha_1453_);
lean_dec_ref(v_rel_1450_);
lean_dec_ref(v_discrs_1448_);
lean_dec_ref(v_f_1447_);
lean_dec_ref(v_matcherInfo_1444_);
v_a_1555_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1493_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1493_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_del_object(v___x_1479_);
lean_dec(v_fst_1477_);
lean_dec(v___x_1460_);
lean_dec(v___x_1459_);
lean_dec(v___x_1458_);
lean_dec_ref(v___x_1456_);
lean_dec_ref(v_beta_1455_);
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_alpha_1453_);
lean_dec_ref(v_rel_1450_);
lean_dec_ref(v_discrs_1448_);
lean_dec_ref(v_f_1447_);
lean_dec_ref(v_matcherInfo_1444_);
v_a_1563_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1490_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1490_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v___x_1468_);
lean_dec(v___x_1460_);
lean_dec(v___x_1459_);
lean_dec(v___x_1458_);
lean_dec_ref(v___x_1456_);
lean_dec_ref(v_beta_1455_);
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_alpha_1453_);
lean_dec(v___x_1451_);
lean_dec_ref(v_rel_1450_);
lean_dec_ref(v___x_1449_);
lean_dec_ref(v_discrs_1448_);
lean_dec_ref(v_f_1447_);
lean_dec_ref(v_matcherInfo_1444_);
v_a_1573_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1475_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1475_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed(lean_object** _args){
lean_object* v___x_1581_ = _args[0];
lean_object* v_matcherInfo_1582_ = _args[1];
lean_object* v___x_1583_ = _args[2];
lean_object* v___x_1584_ = _args[3];
lean_object* v_f_1585_ = _args[4];
lean_object* v_discrs_1586_ = _args[5];
lean_object* v___x_1587_ = _args[6];
lean_object* v_rel_1588_ = _args[7];
lean_object* v___x_1589_ = _args[8];
lean_object* v___x_1590_ = _args[9];
lean_object* v_alpha_1591_ = _args[10];
lean_object* v___x_1592_ = _args[11];
lean_object* v_beta_1593_ = _args[12];
lean_object* v___x_1594_ = _args[13];
lean_object* v___x_1595_ = _args[14];
lean_object* v___x_1596_ = _args[15];
lean_object* v___x_1597_ = _args[16];
lean_object* v___x_1598_ = _args[17];
lean_object* v_alts_1599_ = _args[18];
lean_object* v_x_1600_ = _args[19];
lean_object* v___y_1601_ = _args[20];
lean_object* v___y_1602_ = _args[21];
lean_object* v___y_1603_ = _args[22];
lean_object* v___y_1604_ = _args[23];
lean_object* v___y_1605_ = _args[24];
_start:
{
uint8_t v___x_16786__boxed_1606_; uint8_t v___x_16789__boxed_1607_; lean_object* v_res_1608_; 
v___x_16786__boxed_1606_ = lean_unbox(v___x_1590_);
v___x_16789__boxed_1607_ = lean_unbox(v___x_1595_);
v_res_1608_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(v___x_1581_, v_matcherInfo_1582_, v___x_1583_, v___x_1584_, v_f_1585_, v_discrs_1586_, v___x_1587_, v_rel_1588_, v___x_1589_, v___x_16786__boxed_1606_, v_alpha_1591_, v___x_1592_, v_beta_1593_, v___x_1594_, v___x_16789__boxed_1607_, v___x_1596_, v___x_1597_, v___x_1598_, v_alts_1599_, v_x_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec_ref(v_x_1600_);
lean_dec_ref(v_alts_1599_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(lean_object* v___x_1609_, lean_object* v___x_1610_, lean_object* v_matcherInfo_1611_, lean_object* v___x_1612_, lean_object* v_f_1613_, lean_object* v___x_1614_, lean_object* v_rel_1615_, lean_object* v___x_1616_, uint8_t v___x_1617_, lean_object* v_alpha_1618_, lean_object* v___x_1619_, lean_object* v_beta_1620_, lean_object* v___x_1621_, uint8_t v___x_1622_, lean_object* v___x_1623_, lean_object* v___x_1624_, lean_object* v___x_1625_, lean_object* v_discrs_1626_, lean_object* v_x_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = l_Lean_mkAppN(v___x_1609_, v_discrs_1626_);
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc_ref(v___x_1633_);
v___x_1634_ = lean_infer_type(v___x_1633_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___f_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v___x_1636_ = l_Lean_mkAppN(v___x_1610_, v_discrs_1626_);
v___x_1637_ = lean_box(v___x_1617_);
v___x_1638_ = lean_box(v___x_1622_);
lean_inc_ref(v_matcherInfo_1611_);
v___f_1639_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1639_, 0, v___x_1633_);
lean_closure_set(v___f_1639_, 1, v_matcherInfo_1611_);
lean_closure_set(v___f_1639_, 2, v___x_1612_);
lean_closure_set(v___f_1639_, 3, v___x_1636_);
lean_closure_set(v___f_1639_, 4, v_f_1613_);
lean_closure_set(v___f_1639_, 5, v_discrs_1626_);
lean_closure_set(v___f_1639_, 6, v___x_1614_);
lean_closure_set(v___f_1639_, 7, v_rel_1615_);
lean_closure_set(v___f_1639_, 8, v___x_1616_);
lean_closure_set(v___f_1639_, 9, v___x_1637_);
lean_closure_set(v___f_1639_, 10, v_alpha_1618_);
lean_closure_set(v___f_1639_, 11, v___x_1619_);
lean_closure_set(v___f_1639_, 12, v_beta_1620_);
lean_closure_set(v___f_1639_, 13, v___x_1621_);
lean_closure_set(v___f_1639_, 14, v___x_1638_);
lean_closure_set(v___f_1639_, 15, v___x_1623_);
lean_closure_set(v___f_1639_, 16, v___x_1624_);
lean_closure_set(v___f_1639_, 17, v___x_1625_);
v___x_1640_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_matcherInfo_1611_);
lean_dec_ref(v_matcherInfo_1611_);
v___x_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
v___x_1642_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1635_, v___x_1641_, v___f_1639_, v___x_1622_, v___x_1622_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1642_;
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v___x_1633_);
lean_dec_ref(v_discrs_1626_);
lean_dec(v___x_1625_);
lean_dec(v___x_1624_);
lean_dec(v___x_1623_);
lean_dec_ref(v___x_1621_);
lean_dec_ref(v_beta_1620_);
lean_dec_ref(v___x_1619_);
lean_dec_ref(v_alpha_1618_);
lean_dec(v___x_1616_);
lean_dec_ref(v_rel_1615_);
lean_dec_ref(v___x_1614_);
lean_dec_ref(v_f_1613_);
lean_dec(v___x_1612_);
lean_dec_ref(v_matcherInfo_1611_);
lean_dec_ref(v___x_1610_);
v_a_1643_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1634_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1634_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed(lean_object** _args){
lean_object* v___x_1651_ = _args[0];
lean_object* v___x_1652_ = _args[1];
lean_object* v_matcherInfo_1653_ = _args[2];
lean_object* v___x_1654_ = _args[3];
lean_object* v_f_1655_ = _args[4];
lean_object* v___x_1656_ = _args[5];
lean_object* v_rel_1657_ = _args[6];
lean_object* v___x_1658_ = _args[7];
lean_object* v___x_1659_ = _args[8];
lean_object* v_alpha_1660_ = _args[9];
lean_object* v___x_1661_ = _args[10];
lean_object* v_beta_1662_ = _args[11];
lean_object* v___x_1663_ = _args[12];
lean_object* v___x_1664_ = _args[13];
lean_object* v___x_1665_ = _args[14];
lean_object* v___x_1666_ = _args[15];
lean_object* v___x_1667_ = _args[16];
lean_object* v_discrs_1668_ = _args[17];
lean_object* v_x_1669_ = _args[18];
lean_object* v___y_1670_ = _args[19];
lean_object* v___y_1671_ = _args[20];
lean_object* v___y_1672_ = _args[21];
lean_object* v___y_1673_ = _args[22];
lean_object* v___y_1674_ = _args[23];
_start:
{
uint8_t v___x_17067__boxed_1675_; uint8_t v___x_17070__boxed_1676_; lean_object* v_res_1677_; 
v___x_17067__boxed_1675_ = lean_unbox(v___x_1659_);
v___x_17070__boxed_1676_ = lean_unbox(v___x_1664_);
v_res_1677_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(v___x_1651_, v___x_1652_, v_matcherInfo_1653_, v___x_1654_, v_f_1655_, v___x_1656_, v_rel_1657_, v___x_1658_, v___x_17067__boxed_1675_, v_alpha_1660_, v___x_1661_, v_beta_1662_, v___x_1663_, v___x_17070__boxed_1676_, v___x_1665_, v___x_1666_, v___x_1667_, v_discrs_1668_, v_x_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec_ref(v_x_1669_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
if (lean_obj_tag(v_a_1678_) == 0)
{
lean_object* v___x_1680_; 
v___x_1680_ = l_List_reverse___redArg(v_a_1679_);
return v___x_1680_;
}
else
{
lean_object* v_head_1681_; lean_object* v_tail_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1691_; 
v_head_1681_ = lean_ctor_get(v_a_1678_, 0);
v_tail_1682_ = lean_ctor_get(v_a_1678_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_a_1678_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1684_ = v_a_1678_;
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_tail_1682_);
lean_inc(v_head_1681_);
lean_dec(v_a_1678_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = l_Lean_mkLevelParam(v_head_1681_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v_a_1679_);
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_a_1679_);
v___x_1688_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
v_a_1678_ = v_tail_1682_;
v_a_1679_ = v___x_1688_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__0));
v___x_1694_ = l_Lean_stringToMessageData(v___x_1693_);
return v___x_1694_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__2));
v___x_1697_ = l_Lean_stringToMessageData(v___x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(lean_object* v___x_1698_, lean_object* v___x_1699_, lean_object* v___x_1700_, lean_object* v_beta_1701_, uint8_t v___x_1702_, lean_object* v_alpha_1703_, uint8_t v___x_1704_, lean_object* v_numDiscrs_1705_, lean_object* v___f_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_levelParams_1709_, lean_object* v_matcherName_1710_, lean_object* v___x_1711_, lean_object* v_matcherInfo_1712_, lean_object* v___x_1713_, lean_object* v_f_1714_, lean_object* v___x_1715_, lean_object* v_uElimPos_x3f_1716_, lean_object* v_rel_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
lean_inc(v___y_1721_);
lean_inc_ref(v___y_1720_);
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1718_);
lean_inc_ref(v___x_1698_);
v___x_1723_ = lean_infer_type(v___x_1698_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = lean_box(v___x_1702_);
v___x_1726_ = lean_box(v___x_1704_);
lean_inc_ref(v_alpha_1703_);
lean_inc_ref(v_beta_1701_);
lean_inc(v___x_1700_);
lean_inc_ref(v_rel_1717_);
lean_inc_ref(v___x_1699_);
lean_inc_ref(v___x_1698_);
v___f_1727_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed), 15, 8);
lean_closure_set(v___f_1727_, 0, v___x_1698_);
lean_closure_set(v___f_1727_, 1, v___x_1699_);
lean_closure_set(v___f_1727_, 2, v_rel_1717_);
lean_closure_set(v___f_1727_, 3, v___x_1700_);
lean_closure_set(v___f_1727_, 4, v_beta_1701_);
lean_closure_set(v___f_1727_, 5, v___x_1725_);
lean_closure_set(v___f_1727_, 6, v_alpha_1703_);
lean_closure_set(v___f_1727_, 7, v___x_1726_);
v___x_1728_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1724_, v___f_1727_, v___x_1704_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc_n(v_a_1729_, 2);
lean_dec_ref_known(v___x_1728_, 1);
lean_inc(v_numDiscrs_1705_);
v___x_1730_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_a_1729_, v_numDiscrs_1705_, v___f_1706_, v___x_1704_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v_matcherLevels_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_a_1707_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1734_, 0, v_a_1708_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
lean_inc(v_levelParams_1709_);
v___x_1735_ = l_List_appendTR___redArg(v_levelParams_1709_, v___x_1734_);
v___x_1736_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_1709_, v___x_1732_);
if (lean_obj_tag(v_uElimPos_x3f_1716_) == 0)
{
uint8_t v___x_1765_; 
v___x_1765_ = l_Lean_Level_isZero(v_a_1731_);
lean_dec(v_a_1731_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v___x_1736_);
lean_dec(v___x_1735_);
lean_dec(v_a_1729_);
lean_dec_ref(v_rel_1717_);
lean_dec(v___x_1715_);
lean_dec_ref(v_f_1714_);
lean_dec(v___x_1713_);
lean_dec_ref(v_matcherInfo_1712_);
lean_dec_ref(v___x_1711_);
lean_dec(v_numDiscrs_1705_);
lean_dec_ref(v_alpha_1703_);
lean_dec_ref(v_beta_1701_);
lean_dec(v___x_1700_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v___x_1698_);
v___x_1766_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1);
v___x_1767_ = l_Lean_MessageData_ofConstName(v_matcherName_1710_, v___x_1704_);
v___x_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1766_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_1770_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
return v___x_1771_;
}
else
{
lean_inc(v___x_1736_);
v_matcherLevels_1738_ = v___x_1736_;
v___y_1739_ = v___y_1718_;
v___y_1740_ = v___y_1719_;
v___y_1741_ = v___y_1720_;
v___y_1742_ = v___y_1721_;
goto v___jp_1737_;
}
}
else
{
lean_object* v_val_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_val_1772_ = lean_ctor_get(v_uElimPos_x3f_1716_, 0);
lean_inc(v___x_1736_);
v___x_1773_ = lean_array_mk(v___x_1736_);
v___x_1774_ = lean_array_set(v___x_1773_, v_val_1772_, v_a_1731_);
v___x_1775_ = lean_array_to_list(v___x_1774_);
v_matcherLevels_1738_ = v___x_1775_;
v___y_1739_ = v___y_1718_;
v___y_1740_ = v___y_1719_;
v___y_1741_ = v___y_1720_;
v___y_1742_ = v___y_1721_;
goto v___jp_1737_;
}
v___jp_1737_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_inc(v_matcherName_1710_);
v___x_1743_ = l_Lean_Expr_const___override(v_matcherName_1710_, v_matcherLevels_1738_);
v___x_1744_ = l_Subarray_copy___redArg(v___x_1711_);
v___x_1745_ = l_Lean_mkAppN(v___x_1743_, v___x_1744_);
v___x_1746_ = l_Lean_Expr_app___override(v___x_1745_, v_a_1729_);
lean_inc(v___y_1742_);
lean_inc_ref(v___y_1741_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc_ref(v___x_1746_);
v___x_1747_ = lean_infer_type(v___x_1746_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___f_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = l_Lean_Expr_const___override(v_matcherName_1710_, v___x_1736_);
v___x_1750_ = l_Lean_mkAppN(v___x_1749_, v___x_1744_);
lean_inc_ref(v___x_1698_);
v___x_1751_ = l_Lean_Expr_app___override(v___x_1750_, v___x_1698_);
v___x_1752_ = lean_box(v___x_1702_);
v___x_1753_ = lean_box(v___x_1704_);
v___f_1754_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed), 24, 17);
lean_closure_set(v___f_1754_, 0, v___x_1746_);
lean_closure_set(v___f_1754_, 1, v___x_1751_);
lean_closure_set(v___f_1754_, 2, v_matcherInfo_1712_);
lean_closure_set(v___f_1754_, 3, v___x_1713_);
lean_closure_set(v___f_1754_, 4, v_f_1714_);
lean_closure_set(v___f_1754_, 5, v___x_1699_);
lean_closure_set(v___f_1754_, 6, v_rel_1717_);
lean_closure_set(v___f_1754_, 7, v___x_1700_);
lean_closure_set(v___f_1754_, 8, v___x_1752_);
lean_closure_set(v___f_1754_, 9, v_alpha_1703_);
lean_closure_set(v___f_1754_, 10, v___x_1698_);
lean_closure_set(v___f_1754_, 11, v_beta_1701_);
lean_closure_set(v___f_1754_, 12, v___x_1744_);
lean_closure_set(v___f_1754_, 13, v___x_1753_);
lean_closure_set(v___f_1754_, 14, v___x_1715_);
lean_closure_set(v___f_1754_, 15, v___x_1735_);
lean_closure_set(v___f_1754_, 16, v___x_1732_);
v___x_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_numDiscrs_1705_);
v___x_1756_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1748_, v___x_1755_, v___f_1754_, v___x_1704_, v___x_1704_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
return v___x_1756_;
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref(v___x_1746_);
lean_dec_ref(v___x_1744_);
lean_dec(v___x_1736_);
lean_dec(v___x_1735_);
lean_dec_ref(v_rel_1717_);
lean_dec(v___x_1715_);
lean_dec_ref(v_f_1714_);
lean_dec(v___x_1713_);
lean_dec_ref(v_matcherInfo_1712_);
lean_dec(v_matcherName_1710_);
lean_dec(v_numDiscrs_1705_);
lean_dec_ref(v_alpha_1703_);
lean_dec_ref(v_beta_1701_);
lean_dec(v___x_1700_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v___x_1698_);
v_a_1757_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1747_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1747_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec(v_a_1729_);
lean_dec_ref(v_rel_1717_);
lean_dec(v___x_1715_);
lean_dec_ref(v_f_1714_);
lean_dec(v___x_1713_);
lean_dec_ref(v_matcherInfo_1712_);
lean_dec_ref(v___x_1711_);
lean_dec(v_matcherName_1710_);
lean_dec(v_levelParams_1709_);
lean_dec(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec(v_numDiscrs_1705_);
lean_dec_ref(v_alpha_1703_);
lean_dec_ref(v_beta_1701_);
lean_dec(v___x_1700_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v___x_1698_);
v_a_1776_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1730_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1730_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec_ref(v_rel_1717_);
lean_dec(v___x_1715_);
lean_dec_ref(v_f_1714_);
lean_dec(v___x_1713_);
lean_dec_ref(v_matcherInfo_1712_);
lean_dec_ref(v___x_1711_);
lean_dec(v_matcherName_1710_);
lean_dec(v_levelParams_1709_);
lean_dec(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v___f_1706_);
lean_dec(v_numDiscrs_1705_);
lean_dec_ref(v_alpha_1703_);
lean_dec_ref(v_beta_1701_);
lean_dec(v___x_1700_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v___x_1698_);
v_a_1784_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1728_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1728_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec_ref(v_rel_1717_);
lean_dec(v___x_1715_);
lean_dec_ref(v_f_1714_);
lean_dec(v___x_1713_);
lean_dec_ref(v_matcherInfo_1712_);
lean_dec_ref(v___x_1711_);
lean_dec(v_matcherName_1710_);
lean_dec(v_levelParams_1709_);
lean_dec(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v___f_1706_);
lean_dec(v_numDiscrs_1705_);
lean_dec_ref(v_alpha_1703_);
lean_dec_ref(v_beta_1701_);
lean_dec(v___x_1700_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v___x_1698_);
v_a_1792_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1723_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1723_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed(lean_object** _args){
lean_object* v___x_1800_ = _args[0];
lean_object* v___x_1801_ = _args[1];
lean_object* v___x_1802_ = _args[2];
lean_object* v_beta_1803_ = _args[3];
lean_object* v___x_1804_ = _args[4];
lean_object* v_alpha_1805_ = _args[5];
lean_object* v___x_1806_ = _args[6];
lean_object* v_numDiscrs_1807_ = _args[7];
lean_object* v___f_1808_ = _args[8];
lean_object* v_a_1809_ = _args[9];
lean_object* v_a_1810_ = _args[10];
lean_object* v_levelParams_1811_ = _args[11];
lean_object* v_matcherName_1812_ = _args[12];
lean_object* v___x_1813_ = _args[13];
lean_object* v_matcherInfo_1814_ = _args[14];
lean_object* v___x_1815_ = _args[15];
lean_object* v_f_1816_ = _args[16];
lean_object* v___x_1817_ = _args[17];
lean_object* v_uElimPos_x3f_1818_ = _args[18];
lean_object* v_rel_1819_ = _args[19];
lean_object* v___y_1820_ = _args[20];
lean_object* v___y_1821_ = _args[21];
lean_object* v___y_1822_ = _args[22];
lean_object* v___y_1823_ = _args[23];
lean_object* v___y_1824_ = _args[24];
_start:
{
uint8_t v___x_17195__boxed_1825_; uint8_t v___x_17196__boxed_1826_; lean_object* v_res_1827_; 
v___x_17195__boxed_1825_ = lean_unbox(v___x_1804_);
v___x_17196__boxed_1826_ = lean_unbox(v___x_1806_);
v_res_1827_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(v___x_1800_, v___x_1801_, v___x_1802_, v_beta_1803_, v___x_17195__boxed_1825_, v_alpha_1805_, v___x_17196__boxed_1826_, v_numDiscrs_1807_, v___f_1808_, v_a_1809_, v_a_1810_, v_levelParams_1811_, v_matcherName_1812_, v___x_1813_, v_matcherInfo_1814_, v___x_1815_, v_f_1816_, v___x_1817_, v_uElimPos_x3f_1818_, v_rel_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v_uElimPos_x3f_1818_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(lean_object* v_k_1828_, lean_object* v_b_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
v___x_1835_ = lean_apply_6(v_k_1828_, v_b_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, lean_box(0));
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v_k_1836_, lean_object* v_b_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(v_k_1836_, v_b_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(lean_object* v_name_1844_, uint8_t v_bi_1845_, lean_object* v_type_1846_, lean_object* v_k_1847_, uint8_t v_kind_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___f_1854_; lean_object* v___x_1855_; 
v___f_1854_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1854_, 0, v_k_1847_);
v___x_1855_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1844_, v_bi_1845_, v_type_1846_, v___f_1854_, v_kind_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
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
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
v_a_1864_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1855_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1855_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___boxed(lean_object* v_name_1872_, lean_object* v_bi_1873_, lean_object* v_type_1874_, lean_object* v_k_1875_, lean_object* v_kind_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
uint8_t v_bi_boxed_1882_; uint8_t v_kind_boxed_1883_; lean_object* v_res_1884_; 
v_bi_boxed_1882_ = lean_unbox(v_bi_1873_);
v_kind_boxed_1883_ = lean_unbox(v_kind_1876_);
v_res_1884_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1872_, v_bi_boxed_1882_, v_type_1874_, v_k_1875_, v_kind_boxed_1883_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(lean_object* v_name_1885_, lean_object* v_type_1886_, lean_object* v_k_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
uint8_t v___x_1893_; uint8_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = 0;
v___x_1894_ = 0;
v___x_1895_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1885_, v___x_1893_, v_type_1886_, v_k_1887_, v___x_1894_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg___boxed(lean_object* v_name_1896_, lean_object* v_type_1897_, lean_object* v_k_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_1896_, v_type_1897_, v_k_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(lean_object* v___x_1908_, lean_object* v___f_1909_, lean_object* v___x_1910_, lean_object* v___x_1911_, lean_object* v_beta_1912_, uint8_t v___x_1913_, lean_object* v_alpha_1914_, lean_object* v_numDiscrs_1915_, lean_object* v___f_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_levelParams_1919_, lean_object* v_matcherName_1920_, lean_object* v___x_1921_, lean_object* v_matcherInfo_1922_, lean_object* v___x_1923_, lean_object* v___x_1924_, lean_object* v_uElimPos_x3f_1925_, lean_object* v_f_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; 
lean_inc(v___y_1930_);
lean_inc_ref(v___y_1929_);
lean_inc(v___y_1928_);
lean_inc_ref(v___y_1927_);
lean_inc_ref(v___x_1908_);
v___x_1932_ = lean_infer_type(v___x_1908_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; uint8_t v___x_1934_; lean_object* v___x_1935_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v___x_1934_ = 0;
v___x_1935_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1933_, v___f_1909_, v___x_1934_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___f_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = lean_box(v___x_1913_);
v___x_1938_ = lean_box(v___x_1934_);
v___f_1939_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed), 25, 19);
lean_closure_set(v___f_1939_, 0, v___x_1908_);
lean_closure_set(v___f_1939_, 1, v___x_1910_);
lean_closure_set(v___f_1939_, 2, v___x_1911_);
lean_closure_set(v___f_1939_, 3, v_beta_1912_);
lean_closure_set(v___f_1939_, 4, v___x_1937_);
lean_closure_set(v___f_1939_, 5, v_alpha_1914_);
lean_closure_set(v___f_1939_, 6, v___x_1938_);
lean_closure_set(v___f_1939_, 7, v_numDiscrs_1915_);
lean_closure_set(v___f_1939_, 8, v___f_1916_);
lean_closure_set(v___f_1939_, 9, v_a_1917_);
lean_closure_set(v___f_1939_, 10, v_a_1918_);
lean_closure_set(v___f_1939_, 11, v_levelParams_1919_);
lean_closure_set(v___f_1939_, 12, v_matcherName_1920_);
lean_closure_set(v___f_1939_, 13, v___x_1921_);
lean_closure_set(v___f_1939_, 14, v_matcherInfo_1922_);
lean_closure_set(v___f_1939_, 15, v___x_1923_);
lean_closure_set(v___f_1939_, 16, v_f_1926_);
lean_closure_set(v___f_1939_, 17, v___x_1924_);
lean_closure_set(v___f_1939_, 18, v_uElimPos_x3f_1925_);
v___x_1940_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__1));
v___x_1941_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_1940_, v_a_1936_, v___f_1939_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
return v___x_1941_;
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v_f_1926_);
lean_dec(v_uElimPos_x3f_1925_);
lean_dec(v___x_1924_);
lean_dec(v___x_1923_);
lean_dec_ref(v_matcherInfo_1922_);
lean_dec_ref(v___x_1921_);
lean_dec(v_matcherName_1920_);
lean_dec(v_levelParams_1919_);
lean_dec(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v___f_1916_);
lean_dec(v_numDiscrs_1915_);
lean_dec_ref(v_alpha_1914_);
lean_dec_ref(v_beta_1912_);
lean_dec(v___x_1911_);
lean_dec_ref(v___x_1910_);
lean_dec_ref(v___x_1908_);
v_a_1942_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1935_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1935_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_f_1926_);
lean_dec(v_uElimPos_x3f_1925_);
lean_dec(v___x_1924_);
lean_dec(v___x_1923_);
lean_dec_ref(v_matcherInfo_1922_);
lean_dec_ref(v___x_1921_);
lean_dec(v_matcherName_1920_);
lean_dec(v_levelParams_1919_);
lean_dec(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v___f_1916_);
lean_dec(v_numDiscrs_1915_);
lean_dec_ref(v_alpha_1914_);
lean_dec_ref(v_beta_1912_);
lean_dec(v___x_1911_);
lean_dec_ref(v___x_1910_);
lean_dec_ref(v___f_1909_);
lean_dec_ref(v___x_1908_);
v_a_1950_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1932_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1932_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed(lean_object** _args){
lean_object* v___x_1958_ = _args[0];
lean_object* v___f_1959_ = _args[1];
lean_object* v___x_1960_ = _args[2];
lean_object* v___x_1961_ = _args[3];
lean_object* v_beta_1962_ = _args[4];
lean_object* v___x_1963_ = _args[5];
lean_object* v_alpha_1964_ = _args[6];
lean_object* v_numDiscrs_1965_ = _args[7];
lean_object* v___f_1966_ = _args[8];
lean_object* v_a_1967_ = _args[9];
lean_object* v_a_1968_ = _args[10];
lean_object* v_levelParams_1969_ = _args[11];
lean_object* v_matcherName_1970_ = _args[12];
lean_object* v___x_1971_ = _args[13];
lean_object* v_matcherInfo_1972_ = _args[14];
lean_object* v___x_1973_ = _args[15];
lean_object* v___x_1974_ = _args[16];
lean_object* v_uElimPos_x3f_1975_ = _args[17];
lean_object* v_f_1976_ = _args[18];
lean_object* v___y_1977_ = _args[19];
lean_object* v___y_1978_ = _args[20];
lean_object* v___y_1979_ = _args[21];
lean_object* v___y_1980_ = _args[22];
lean_object* v___y_1981_ = _args[23];
_start:
{
uint8_t v___x_17499__boxed_1982_; lean_object* v_res_1983_; 
v___x_17499__boxed_1982_ = lean_unbox(v___x_1963_);
v_res_1983_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(v___x_1958_, v___f_1959_, v___x_1960_, v___x_1961_, v_beta_1962_, v___x_17499__boxed_1982_, v_alpha_1964_, v_numDiscrs_1965_, v___f_1966_, v_a_1967_, v_a_1968_, v_levelParams_1969_, v_matcherName_1970_, v___x_1971_, v_matcherInfo_1972_, v___x_1973_, v___x_1974_, v_uElimPos_x3f_1975_, v_f_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(lean_object* v___x_1990_, lean_object* v_alpha_1991_, lean_object* v___x_1992_, lean_object* v___x_1993_, lean_object* v_numDiscrs_1994_, lean_object* v___f_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_levelParams_1998_, lean_object* v_matcherName_1999_, lean_object* v___x_2000_, lean_object* v_matcherInfo_2001_, lean_object* v___x_2002_, lean_object* v_uElimPos_x3f_2003_, lean_object* v_beta_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___x_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2010_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__1));
v___x_2011_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__3));
lean_inc_n(v___x_1990_, 2);
v___x_2012_ = l_Lean_Expr_bvar___override(v___x_1990_);
lean_inc_ref(v___x_2012_);
lean_inc_ref(v_beta_2004_);
v___x_2013_ = l_Lean_Expr_app___override(v_beta_2004_, v___x_2012_);
v___x_2014_ = 0;
v___x_2015_ = lean_box(v___x_2014_);
lean_inc_ref_n(v_alpha_1991_, 2);
v___f_2016_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2016_, 0, v___x_1990_);
lean_closure_set(v___f_2016_, 1, v___x_2011_);
lean_closure_set(v___f_2016_, 2, v_alpha_1991_);
lean_closure_set(v___f_2016_, 3, v___x_2015_);
v___x_2017_ = lean_box(v___x_2014_);
v___f_2018_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed), 24, 18);
lean_closure_set(v___f_2018_, 0, v___x_1992_);
lean_closure_set(v___f_2018_, 1, v___f_2016_);
lean_closure_set(v___f_2018_, 2, v___x_2012_);
lean_closure_set(v___f_2018_, 3, v___x_1993_);
lean_closure_set(v___f_2018_, 4, v_beta_2004_);
lean_closure_set(v___f_2018_, 5, v___x_2017_);
lean_closure_set(v___f_2018_, 6, v_alpha_1991_);
lean_closure_set(v___f_2018_, 7, v_numDiscrs_1994_);
lean_closure_set(v___f_2018_, 8, v___f_1995_);
lean_closure_set(v___f_2018_, 9, v_a_1996_);
lean_closure_set(v___f_2018_, 10, v_a_1997_);
lean_closure_set(v___f_2018_, 11, v_levelParams_1998_);
lean_closure_set(v___f_2018_, 12, v_matcherName_1999_);
lean_closure_set(v___f_2018_, 13, v___x_2000_);
lean_closure_set(v___f_2018_, 14, v_matcherInfo_2001_);
lean_closure_set(v___f_2018_, 15, v___x_1990_);
lean_closure_set(v___f_2018_, 16, v___x_2002_);
lean_closure_set(v___f_2018_, 17, v_uElimPos_x3f_2003_);
v___x_2019_ = l_Lean_Expr_forallE___override(v___x_2011_, v_alpha_1991_, v___x_2013_, v___x_2014_);
v___x_2020_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2010_, v___x_2019_, v___f_2018_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed(lean_object** _args){
lean_object* v___x_2021_ = _args[0];
lean_object* v_alpha_2022_ = _args[1];
lean_object* v___x_2023_ = _args[2];
lean_object* v___x_2024_ = _args[3];
lean_object* v_numDiscrs_2025_ = _args[4];
lean_object* v___f_2026_ = _args[5];
lean_object* v_a_2027_ = _args[6];
lean_object* v_a_2028_ = _args[7];
lean_object* v_levelParams_2029_ = _args[8];
lean_object* v_matcherName_2030_ = _args[9];
lean_object* v___x_2031_ = _args[10];
lean_object* v_matcherInfo_2032_ = _args[11];
lean_object* v___x_2033_ = _args[12];
lean_object* v_uElimPos_x3f_2034_ = _args[13];
lean_object* v_beta_2035_ = _args[14];
lean_object* v___y_2036_ = _args[15];
lean_object* v___y_2037_ = _args[16];
lean_object* v___y_2038_ = _args[17];
lean_object* v___y_2039_ = _args[18];
lean_object* v___y_2040_ = _args[19];
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(v___x_2021_, v_alpha_2022_, v___x_2023_, v___x_2024_, v_numDiscrs_2025_, v___f_2026_, v_a_2027_, v_a_2028_, v_levelParams_2029_, v_matcherName_2030_, v___x_2031_, v_matcherInfo_2032_, v___x_2033_, v_uElimPos_x3f_2034_, v_beta_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(lean_object* v_a_2045_, lean_object* v___x_2046_, lean_object* v___x_2047_, lean_object* v___x_2048_, lean_object* v_numDiscrs_2049_, lean_object* v___f_2050_, lean_object* v_a_2051_, lean_object* v_levelParams_2052_, lean_object* v_matcherName_2053_, lean_object* v___x_2054_, lean_object* v_matcherInfo_2055_, lean_object* v___x_2056_, lean_object* v_uElimPos_x3f_2057_, lean_object* v_alpha_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_inc(v_a_2045_);
v___x_2064_ = l_Lean_Level_param___override(v_a_2045_);
v___x_2065_ = l_Lean_Expr_sort___override(v___x_2064_);
lean_inc_ref(v_alpha_2058_);
v___x_2066_ = l_Lean_mkArrow(v_alpha_2058_, v___x_2065_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___f_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v___f_2068_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed), 20, 14);
lean_closure_set(v___f_2068_, 0, v___x_2046_);
lean_closure_set(v___f_2068_, 1, v_alpha_2058_);
lean_closure_set(v___f_2068_, 2, v___x_2047_);
lean_closure_set(v___f_2068_, 3, v___x_2048_);
lean_closure_set(v___f_2068_, 4, v_numDiscrs_2049_);
lean_closure_set(v___f_2068_, 5, v___f_2050_);
lean_closure_set(v___f_2068_, 6, v_a_2045_);
lean_closure_set(v___f_2068_, 7, v_a_2051_);
lean_closure_set(v___f_2068_, 8, v_levelParams_2052_);
lean_closure_set(v___f_2068_, 9, v_matcherName_2053_);
lean_closure_set(v___f_2068_, 10, v___x_2054_);
lean_closure_set(v___f_2068_, 11, v_matcherInfo_2055_);
lean_closure_set(v___f_2068_, 12, v___x_2056_);
lean_closure_set(v___f_2068_, 13, v_uElimPos_x3f_2057_);
v___x_2069_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__1));
v___x_2070_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2069_, v_a_2067_, v___f_2068_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
return v___x_2070_;
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec_ref(v_alpha_2058_);
lean_dec(v_uElimPos_x3f_2057_);
lean_dec(v___x_2056_);
lean_dec_ref(v_matcherInfo_2055_);
lean_dec_ref(v___x_2054_);
lean_dec(v_matcherName_2053_);
lean_dec(v_levelParams_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v___f_2050_);
lean_dec(v_numDiscrs_2049_);
lean_dec(v___x_2048_);
lean_dec_ref(v___x_2047_);
lean_dec(v___x_2046_);
lean_dec(v_a_2045_);
v_a_2071_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2066_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2066_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed(lean_object** _args){
lean_object* v_a_2079_ = _args[0];
lean_object* v___x_2080_ = _args[1];
lean_object* v___x_2081_ = _args[2];
lean_object* v___x_2082_ = _args[3];
lean_object* v_numDiscrs_2083_ = _args[4];
lean_object* v___f_2084_ = _args[5];
lean_object* v_a_2085_ = _args[6];
lean_object* v_levelParams_2086_ = _args[7];
lean_object* v_matcherName_2087_ = _args[8];
lean_object* v___x_2088_ = _args[9];
lean_object* v_matcherInfo_2089_ = _args[10];
lean_object* v___x_2090_ = _args[11];
lean_object* v_uElimPos_x3f_2091_ = _args[12];
lean_object* v_alpha_2092_ = _args[13];
lean_object* v___y_2093_ = _args[14];
lean_object* v___y_2094_ = _args[15];
lean_object* v___y_2095_ = _args[16];
lean_object* v___y_2096_ = _args[17];
lean_object* v___y_2097_ = _args[18];
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(v_a_2079_, v___x_2080_, v___x_2081_, v___x_2082_, v_numDiscrs_2083_, v___f_2084_, v_a_2085_, v_levelParams_2086_, v_matcherName_2087_, v___x_2088_, v_matcherInfo_2089_, v___x_2090_, v_uElimPos_x3f_2091_, v_alpha_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(lean_object* v_numParams_2108_, lean_object* v___x_2109_, lean_object* v___x_2110_, lean_object* v_numDiscrs_2111_, lean_object* v___f_2112_, lean_object* v_levelParams_2113_, lean_object* v_matcherName_2114_, lean_object* v_matcherInfo_2115_, lean_object* v___x_2116_, lean_object* v_uElimPos_x3f_2117_, lean_object* v_xs_2118_, lean_object* v_x_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__1));
v___x_2126_ = l_Lean_Core_mkFreshUserName(v___x_2125_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__3));
v___x_2129_ = l_Lean_Core_mkFreshUserName(v___x_2128_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2108_);
lean_inc_ref(v_xs_2118_);
v___x_2132_ = l_Array_toSubarray___redArg(v_xs_2118_, v___x_2131_, v_numParams_2108_);
v___x_2133_ = lean_array_get(v___x_2109_, v_xs_2118_, v_numParams_2108_);
lean_dec(v_numParams_2108_);
lean_dec_ref(v_xs_2118_);
lean_inc(v_a_2127_);
v___f_2134_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed), 19, 13);
lean_closure_set(v___f_2134_, 0, v_a_2130_);
lean_closure_set(v___f_2134_, 1, v___x_2131_);
lean_closure_set(v___f_2134_, 2, v___x_2133_);
lean_closure_set(v___f_2134_, 3, v___x_2110_);
lean_closure_set(v___f_2134_, 4, v_numDiscrs_2111_);
lean_closure_set(v___f_2134_, 5, v___f_2112_);
lean_closure_set(v___f_2134_, 6, v_a_2127_);
lean_closure_set(v___f_2134_, 7, v_levelParams_2113_);
lean_closure_set(v___f_2134_, 8, v_matcherName_2114_);
lean_closure_set(v___f_2134_, 9, v___x_2132_);
lean_closure_set(v___f_2134_, 10, v_matcherInfo_2115_);
lean_closure_set(v___f_2134_, 11, v___x_2116_);
lean_closure_set(v___f_2134_, 12, v_uElimPos_x3f_2117_);
v___x_2135_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__5));
v___x_2136_ = l_Lean_Level_param___override(v_a_2127_);
v___x_2137_ = l_Lean_Expr_sort___override(v___x_2136_);
v___x_2138_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2135_, v___x_2137_, v___f_2134_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v___x_2138_;
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_a_2127_);
lean_dec_ref(v_xs_2118_);
lean_dec(v_uElimPos_x3f_2117_);
lean_dec(v___x_2116_);
lean_dec_ref(v_matcherInfo_2115_);
lean_dec(v_matcherName_2114_);
lean_dec(v_levelParams_2113_);
lean_dec_ref(v___f_2112_);
lean_dec(v_numDiscrs_2111_);
lean_dec(v___x_2110_);
lean_dec(v_numParams_2108_);
v_a_2139_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2129_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2129_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v_xs_2118_);
lean_dec(v_uElimPos_x3f_2117_);
lean_dec(v___x_2116_);
lean_dec_ref(v_matcherInfo_2115_);
lean_dec(v_matcherName_2114_);
lean_dec(v_levelParams_2113_);
lean_dec_ref(v___f_2112_);
lean_dec(v_numDiscrs_2111_);
lean_dec(v___x_2110_);
lean_dec(v_numParams_2108_);
v_a_2147_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2126_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2126_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed(lean_object** _args){
lean_object* v_numParams_2155_ = _args[0];
lean_object* v___x_2156_ = _args[1];
lean_object* v___x_2157_ = _args[2];
lean_object* v_numDiscrs_2158_ = _args[3];
lean_object* v___f_2159_ = _args[4];
lean_object* v_levelParams_2160_ = _args[5];
lean_object* v_matcherName_2161_ = _args[6];
lean_object* v_matcherInfo_2162_ = _args[7];
lean_object* v___x_2163_ = _args[8];
lean_object* v_uElimPos_x3f_2164_ = _args[9];
lean_object* v_xs_2165_ = _args[10];
lean_object* v_x_2166_ = _args[11];
lean_object* v___y_2167_ = _args[12];
lean_object* v___y_2168_ = _args[13];
lean_object* v___y_2169_ = _args[14];
lean_object* v___y_2170_ = _args[15];
lean_object* v___y_2171_ = _args[16];
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(v_numParams_2155_, v___x_2156_, v___x_2157_, v_numDiscrs_2158_, v___f_2159_, v_levelParams_2160_, v_matcherName_2161_, v_matcherInfo_2162_, v___x_2163_, v_uElimPos_x3f_2164_, v_xs_2165_, v_x_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec_ref(v_x_2166_);
lean_dec_ref(v___x_2156_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(lean_object* v_ref_2173_, lean_object* v_msg_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_fileName_2180_; lean_object* v_fileMap_2181_; lean_object* v_options_2182_; lean_object* v_currRecDepth_2183_; lean_object* v_maxRecDepth_2184_; lean_object* v_ref_2185_; lean_object* v_currNamespace_2186_; lean_object* v_openDecls_2187_; lean_object* v_initHeartbeats_2188_; lean_object* v_maxHeartbeats_2189_; lean_object* v_quotContext_2190_; lean_object* v_currMacroScope_2191_; uint8_t v_diag_2192_; lean_object* v_cancelTk_x3f_2193_; uint8_t v_suppressElabErrors_2194_; lean_object* v_inheritedTraceOptions_2195_; lean_object* v_ref_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_fileName_2180_ = lean_ctor_get(v___y_2177_, 0);
v_fileMap_2181_ = lean_ctor_get(v___y_2177_, 1);
v_options_2182_ = lean_ctor_get(v___y_2177_, 2);
v_currRecDepth_2183_ = lean_ctor_get(v___y_2177_, 3);
v_maxRecDepth_2184_ = lean_ctor_get(v___y_2177_, 4);
v_ref_2185_ = lean_ctor_get(v___y_2177_, 5);
v_currNamespace_2186_ = lean_ctor_get(v___y_2177_, 6);
v_openDecls_2187_ = lean_ctor_get(v___y_2177_, 7);
v_initHeartbeats_2188_ = lean_ctor_get(v___y_2177_, 8);
v_maxHeartbeats_2189_ = lean_ctor_get(v___y_2177_, 9);
v_quotContext_2190_ = lean_ctor_get(v___y_2177_, 10);
v_currMacroScope_2191_ = lean_ctor_get(v___y_2177_, 11);
v_diag_2192_ = lean_ctor_get_uint8(v___y_2177_, sizeof(void*)*14);
v_cancelTk_x3f_2193_ = lean_ctor_get(v___y_2177_, 12);
v_suppressElabErrors_2194_ = lean_ctor_get_uint8(v___y_2177_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2195_ = lean_ctor_get(v___y_2177_, 13);
v_ref_2196_ = l_Lean_replaceRef(v_ref_2173_, v_ref_2185_);
lean_inc_ref(v_inheritedTraceOptions_2195_);
lean_inc(v_cancelTk_x3f_2193_);
lean_inc(v_currMacroScope_2191_);
lean_inc(v_quotContext_2190_);
lean_inc(v_maxHeartbeats_2189_);
lean_inc(v_initHeartbeats_2188_);
lean_inc(v_openDecls_2187_);
lean_inc(v_currNamespace_2186_);
lean_inc(v_maxRecDepth_2184_);
lean_inc(v_currRecDepth_2183_);
lean_inc_ref(v_options_2182_);
lean_inc_ref(v_fileMap_2181_);
lean_inc_ref(v_fileName_2180_);
v___x_2197_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2197_, 0, v_fileName_2180_);
lean_ctor_set(v___x_2197_, 1, v_fileMap_2181_);
lean_ctor_set(v___x_2197_, 2, v_options_2182_);
lean_ctor_set(v___x_2197_, 3, v_currRecDepth_2183_);
lean_ctor_set(v___x_2197_, 4, v_maxRecDepth_2184_);
lean_ctor_set(v___x_2197_, 5, v_ref_2196_);
lean_ctor_set(v___x_2197_, 6, v_currNamespace_2186_);
lean_ctor_set(v___x_2197_, 7, v_openDecls_2187_);
lean_ctor_set(v___x_2197_, 8, v_initHeartbeats_2188_);
lean_ctor_set(v___x_2197_, 9, v_maxHeartbeats_2189_);
lean_ctor_set(v___x_2197_, 10, v_quotContext_2190_);
lean_ctor_set(v___x_2197_, 11, v_currMacroScope_2191_);
lean_ctor_set(v___x_2197_, 12, v_cancelTk_x3f_2193_);
lean_ctor_set(v___x_2197_, 13, v_inheritedTraceOptions_2195_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*14, v_diag_2192_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*14 + 1, v_suppressElabErrors_2194_);
v___x_2198_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_2174_, v___y_2175_, v___y_2176_, v___x_2197_, v___y_2178_);
lean_dec_ref_known(v___x_2197_, 14);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2199_, lean_object* v_msg_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2199_, v_msg_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v_ref_2199_);
return v_res_2206_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
lean_ctor_set(v___x_2212_, 2, v___x_2211_);
lean_ctor_set(v___x_2212_, 3, v___x_2211_);
lean_ctor_set(v___x_2212_, 4, v___x_2210_);
lean_ctor_set(v___x_2212_, 5, v___x_2210_);
lean_ctor_set(v___x_2212_, 6, v___x_2210_);
lean_ctor_set(v___x_2212_, 7, v___x_2210_);
lean_ctor_set(v___x_2212_, 8, v___x_2210_);
lean_ctor_set(v___x_2212_, 9, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = lean_unsigned_to_nat(32u);
v___x_2214_ = lean_mk_empty_array_with_capacity(v___x_2213_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2216_ = ((size_t)5ULL);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = lean_unsigned_to_nat(32u);
v___x_2219_ = lean_mk_empty_array_with_capacity(v___x_2218_);
v___x_2220_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3);
v___x_2221_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___x_2219_);
lean_ctor_set(v___x_2221_, 2, v___x_2217_);
lean_ctor_set(v___x_2221_, 3, v___x_2217_);
lean_ctor_set_usize(v___x_2221_, 4, v___x_2216_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2222_ = lean_box(1);
v___x_2223_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4);
v___x_2224_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set(v___x_2225_, 1, v___x_2223_);
lean_ctor_set(v___x_2225_, 2, v___x_2222_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__6));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__8));
v___x_2231_ = l_Lean_stringToMessageData(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__10));
v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__12));
v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__14));
v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16));
v___x_2243_ = l_Lean_stringToMessageData(v___x_2242_);
return v___x_2243_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18));
v___x_2246_ = l_Lean_stringToMessageData(v___x_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2247_, lean_object* v_declHint_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; lean_object* v_env_2252_; uint8_t v___y_2254_; uint8_t v___x_2310_; uint8_t v___x_2311_; 
v___x_2251_ = lean_st_ref_get(v___y_2249_);
v_env_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc_ref(v_env_2252_);
lean_dec(v___x_2251_);
v___x_2310_ = l_Lean_Name_isAnonymous(v_declHint_2248_);
v___x_2311_ = lean_bool_not(v___x_2310_);
if (v___x_2311_ == 0)
{
v___y_2254_ = v___x_2311_;
goto v___jp_2253_;
}
else
{
uint8_t v_isExporting_2312_; 
v_isExporting_2312_ = lean_ctor_get_uint8(v_env_2252_, sizeof(void*)*8);
v___y_2254_ = v_isExporting_2312_;
goto v___jp_2253_;
}
v___jp_2253_:
{
if (v___y_2254_ == 0)
{
lean_object* v___x_2255_; 
lean_dec_ref(v_env_2252_);
lean_dec(v_declHint_2248_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v_msg_2247_);
return v___x_2255_;
}
else
{
uint8_t v___x_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v___x_2256_ = 0;
lean_inc_ref(v_env_2252_);
v___x_2257_ = l_Lean_Environment_setExporting(v_env_2252_, v___x_2256_);
lean_inc(v_declHint_2248_);
lean_inc_ref(v___x_2257_);
v___x_2258_ = l_Lean_Environment_contains(v___x_2257_, v_declHint_2248_, v___y_2254_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; 
lean_dec_ref(v___x_2257_);
lean_dec_ref(v_env_2252_);
lean_dec(v_declHint_2248_);
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v_msg_2247_);
return v___x_2259_;
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_c_2265_; lean_object* v___x_2266_; 
v___x_2260_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2261_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2262_ = l_Lean_Options_empty;
v___x_2263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2257_);
lean_ctor_set(v___x_2263_, 1, v___x_2260_);
lean_ctor_set(v___x_2263_, 2, v___x_2261_);
lean_ctor_set(v___x_2263_, 3, v___x_2262_);
lean_inc(v_declHint_2248_);
v___x_2264_ = l_Lean_MessageData_ofConstName(v_declHint_2248_, v___x_2256_);
v_c_2265_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2265_, 0, v___x_2263_);
lean_ctor_set(v_c_2265_, 1, v___x_2264_);
v___x_2266_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2252_, v_declHint_2248_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec_ref(v_env_2252_);
lean_dec(v_declHint_2248_);
v___x_2267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v_c_2265_);
v___x_2269_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = l_Lean_MessageData_note(v___x_2270_);
v___x_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2272_, 0, v_msg_2247_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
return v___x_2273_;
}
else
{
lean_object* v_val_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2309_; 
v_val_2274_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2276_ = v___x_2266_;
v_isShared_2277_ = v_isSharedCheck_2309_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_val_2274_);
lean_dec(v___x_2266_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2309_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v_mod_2281_; uint8_t v___x_2282_; 
v___x_2278_ = lean_box(0);
v___x_2279_ = l_Lean_Environment_header(v_env_2252_);
lean_dec_ref(v_env_2252_);
v___x_2280_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2279_);
v_mod_2281_ = lean_array_get(v___x_2278_, v___x_2280_, v_val_2274_);
lean_dec(v_val_2274_);
lean_dec_ref(v___x_2280_);
v___x_2282_ = l_Lean_isPrivateName(v_declHint_2248_);
lean_dec(v_declHint_2248_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set(v___x_2284_, 1, v_c_2265_);
v___x_2285_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = l_Lean_MessageData_ofName(v_mod_2281_);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = l_Lean_MessageData_note(v___x_2290_);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v_msg_2247_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set_tag(v___x_2276_, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2292_);
v___x_2294_ = v___x_2276_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2296_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set(v___x_2297_, 1, v_c_2265_);
v___x_2298_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = l_Lean_MessageData_ofName(v_mod_2281_);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = l_Lean_MessageData_note(v___x_2303_);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v_msg_2247_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set_tag(v___x_2276_, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2305_);
v___x_2307_ = v___x_2276_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2313_, lean_object* v_declHint_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2313_, v_declHint_2314_, v___y_2315_);
lean_dec(v___y_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(lean_object* v_msg_2318_, lean_object* v_declHint_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2335_; 
v___x_2325_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2318_, v_declHint_2319_, v___y_2323_);
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2330_ = l_Lean_unknownIdentifierMessageTag;
v___x_2331_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
lean_ctor_set(v___x_2331_, 1, v_a_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2331_);
v___x_2333_ = v___x_2328_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11___boxed(lean_object* v_msg_2336_, lean_object* v_declHint_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2336_, v_declHint_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_ref_2344_, lean_object* v_msg_2345_, lean_object* v_declHint_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v_a_2353_; lean_object* v___x_2354_; 
v___x_2352_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2345_, v_declHint_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref(v___x_2352_);
v___x_2354_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2344_, v_a_2353_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_ref_2355_, lean_object* v_msg_2356_, lean_object* v_declHint_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2355_, v_msg_2356_, v_declHint_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v_ref_2355_);
return v_res_2363_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_2366_ = l_Lean_stringToMessageData(v___x_2365_);
return v___x_2366_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_2369_ = l_Lean_stringToMessageData(v___x_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_2370_, lean_object* v_constName_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v___x_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2377_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_2378_ = 0;
lean_inc(v_constName_2371_);
v___x_2379_ = l_Lean_MessageData_ofConstName(v_constName_2371_, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2377_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2370_, v___x_2382_, v_constName_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_2384_, lean_object* v_constName_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2384_, v_constName_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v_ref_2384_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(lean_object* v_constName_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_ref_2398_; lean_object* v___x_2399_; 
v_ref_2398_ = lean_ctor_get(v___y_2395_, 5);
v___x_2399_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2398_, v_constName_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(lean_object* v_constName_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; lean_object* v_env_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; 
v___x_2413_ = lean_st_ref_get(v___y_2411_);
v_env_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_ref(v_env_2414_);
lean_dec(v___x_2413_);
v___x_2415_ = 0;
lean_inc(v_constName_2407_);
v___x_2416_ = l_Lean_Environment_findConstVal_x3f(v_env_2414_, v_constName_2407_, v___x_2415_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
return v___x_2417_;
}
else
{
lean_object* v_val_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec(v_constName_2407_);
v_val_2418_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2416_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_val_2418_);
lean_dec(v___x_2416_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
lean_ctor_set_tag(v___x_2420_, 0);
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_val_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0___boxed(lean_object* v_constName_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_constName_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(lean_object* v_matcherName_2433_, lean_object* v_matcherInfo_2434_, lean_object* v___x_2435_, lean_object* v___f_2436_, lean_object* v___x_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; 
lean_inc(v_matcherName_2433_);
v___x_2443_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_matcherName_2433_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v_levelParams_2445_; lean_object* v_type_2446_; lean_object* v_numParams_2447_; lean_object* v_numDiscrs_2448_; lean_object* v_uElimPos_x3f_2449_; lean_object* v___x_2450_; lean_object* v___f_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; lean_object* v___x_2455_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v_levelParams_2445_ = lean_ctor_get(v_a_2444_, 1);
lean_inc(v_levelParams_2445_);
v_type_2446_ = lean_ctor_get(v_a_2444_, 2);
lean_inc_ref(v_type_2446_);
lean_dec(v_a_2444_);
v_numParams_2447_ = lean_ctor_get(v_matcherInfo_2434_, 0);
lean_inc_n(v_numParams_2447_, 2);
v_numDiscrs_2448_ = lean_ctor_get(v_matcherInfo_2434_, 1);
lean_inc(v_numDiscrs_2448_);
v_uElimPos_x3f_2449_ = lean_ctor_get(v_matcherInfo_2434_, 3);
lean_inc(v_uElimPos_x3f_2449_);
v___x_2450_ = lean_unsigned_to_nat(1u);
v___f_2451_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed), 17, 10);
lean_closure_set(v___f_2451_, 0, v_numParams_2447_);
lean_closure_set(v___f_2451_, 1, v___x_2435_);
lean_closure_set(v___f_2451_, 2, v___x_2450_);
lean_closure_set(v___f_2451_, 3, v_numDiscrs_2448_);
lean_closure_set(v___f_2451_, 4, v___f_2436_);
lean_closure_set(v___f_2451_, 5, v_levelParams_2445_);
lean_closure_set(v___f_2451_, 6, v_matcherName_2433_);
lean_closure_set(v___f_2451_, 7, v_matcherInfo_2434_);
lean_closure_set(v___f_2451_, 8, v___x_2437_);
lean_closure_set(v___f_2451_, 9, v_uElimPos_x3f_2449_);
v___x_2452_ = lean_nat_add(v_numParams_2447_, v___x_2450_);
lean_dec(v_numParams_2447_);
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
v___x_2454_ = 0;
v___x_2455_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_2446_, v___x_2453_, v___f_2451_, v___x_2454_, v___x_2454_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
return v___x_2455_;
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v___x_2437_);
lean_dec_ref(v___f_2436_);
lean_dec_ref(v___x_2435_);
lean_dec_ref(v_matcherInfo_2434_);
lean_dec(v_matcherName_2433_);
v_a_2456_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2443_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2443_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed(lean_object* v_matcherName_2464_, lean_object* v_matcherInfo_2465_, lean_object* v___x_2466_, lean_object* v___f_2467_, lean_object* v___x_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(v_matcherName_2464_, v_matcherInfo_2465_, v___x_2466_, v___f_2467_, v___x_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11(lean_object* v___x_2475_, lean_object* v_e_2476_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = l_Lean_indentD(v_e_2476_);
v___x_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2475_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(lean_object* v___f_2479_, lean_object* v___f_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2479_, v___f_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
v_a_2495_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2486_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2486_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed(lean_object* v___f_2503_, lean_object* v___f_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(v___f_2503_, v___f_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v_res_2510_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__3));
v___x_2517_ = l_Lean_stringToMessageData(v___x_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(lean_object* v_matcherName_2518_, lean_object* v_matcherInfo_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v___x_2525_; lean_object* v_env_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___f_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___f_2536_; lean_object* v___f_2537_; lean_object* v___x_2538_; 
v___x_2525_ = lean_st_ref_get(v_a_2523_);
v_env_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc_ref(v_env_2526_);
lean_dec(v___x_2525_);
v___f_2527_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__0));
v___x_2528_ = l_Lean_instInhabitedExpr;
lean_inc_n(v_matcherName_2518_, 3);
v___x_2529_ = l_Lean_mkPrivateName(v_env_2526_, v_matcherName_2518_);
lean_dec_ref(v_env_2526_);
v___x_2530_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__2));
v___x_2531_ = l_Lean_Name_append(v___x_2529_, v___x_2530_);
lean_inc_n(v___x_2531_, 2);
v___f_2532_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed), 10, 5);
lean_closure_set(v___f_2532_, 0, v_matcherName_2518_);
lean_closure_set(v___f_2532_, 1, v_matcherInfo_2519_);
lean_closure_set(v___f_2532_, 2, v___x_2528_);
lean_closure_set(v___f_2532_, 3, v___f_2527_);
lean_closure_set(v___f_2532_, 4, v___x_2531_);
v___x_2533_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4);
v___x_2534_ = l_Lean_MessageData_ofName(v_matcherName_2518_);
v___x_2535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___f_2536_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_2536_, 0, v___x_2535_);
v___f_2537_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed), 7, 2);
lean_closure_set(v___f_2537_, 0, v___f_2532_);
lean_closure_set(v___f_2537_, 1, v___f_2536_);
v___x_2538_ = l_Lean_Meta_realizeConst(v_matcherName_2518_, v___x_2531_, v___f_2537_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2545_ == 0)
{
lean_object* v_unused_2546_; 
v_unused_2546_ = lean_ctor_get(v___x_2538_, 0);
lean_dec(v_unused_2546_);
v___x_2540_ = v___x_2538_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_dec(v___x_2538_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2531_);
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2531_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v___x_2531_);
v_a_2547_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2538_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2538_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___boxed(lean_object* v_matcherName_2555_, lean_object* v_matcherInfo_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_2555_, v_matcherInfo_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(lean_object* v_as_2563_, lean_object* v_as_x27_2564_, lean_object* v_b_2565_, lean_object* v_a_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_2564_, v_b_2565_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___boxed(lean_object* v_as_2573_, lean_object* v_as_x27_2574_, lean_object* v_b_2575_, lean_object* v_a_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(v_as_2573_, v_as_x27_2574_, v_b_2575_, v_a_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v_as_x27_2574_);
lean_dec(v_as_2573_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(lean_object* v_00_u03b1_2583_, lean_object* v_name_2584_, uint8_t v_bi_2585_, lean_object* v_type_2586_, lean_object* v_k_2587_, uint8_t v_kind_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_2584_, v_bi_2585_, v_type_2586_, v_k_2587_, v_kind_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2595_, lean_object* v_name_2596_, lean_object* v_bi_2597_, lean_object* v_type_2598_, lean_object* v_k_2599_, lean_object* v_kind_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
uint8_t v_bi_boxed_2606_; uint8_t v_kind_boxed_2607_; lean_object* v_res_2608_; 
v_bi_boxed_2606_ = lean_unbox(v_bi_2597_);
v_kind_boxed_2607_ = lean_unbox(v_kind_2600_);
v_res_2608_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(v_00_u03b1_2595_, v_name_2596_, v_bi_boxed_2606_, v_type_2598_, v_k_2599_, v_kind_boxed_2607_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(lean_object* v_00_u03b1_2609_, lean_object* v_name_2610_, lean_object* v_type_2611_, lean_object* v_k_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_2610_, v_type_2611_, v_k_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___boxed(lean_object* v_00_u03b1_2619_, lean_object* v_name_2620_, lean_object* v_type_2621_, lean_object* v_k_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(v_00_u03b1_2619_, v_name_2620_, v_type_2621_, v_k_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(lean_object* v_00_u03b1_2629_, lean_object* v_constName_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2637_, lean_object* v_constName_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(v_00_u03b1_2637_, v_constName_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2645_, lean_object* v_ref_2646_, lean_object* v_constName_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2646_, v_constName_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2654_, lean_object* v_ref_2655_, lean_object* v_constName_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(v_00_u03b1_2654_, v_ref_2655_, v_constName_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v_ref_2655_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b1_2663_, lean_object* v_ref_2664_, lean_object* v_msg_2665_, lean_object* v_declHint_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2664_, v_msg_2665_, v_declHint_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b1_2673_, lean_object* v_ref_2674_, lean_object* v_msg_2675_, lean_object* v_declHint_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(v_00_u03b1_2673_, v_ref_2674_, v_msg_2675_, v_declHint_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v_ref_2674_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(lean_object* v_msg_2683_, lean_object* v_declHint_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2683_, v_declHint_2684_, v___y_2688_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_2691_, lean_object* v_declHint_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(v_msg_2691_, v_declHint_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_2699_, lean_object* v_ref_2700_, lean_object* v_msg_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2700_, v_msg_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_2708_, lean_object* v_ref_2709_, lean_object* v_msg_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(v_00_u03b1_2708_, v_ref_2709_, v_msg_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v_ref_2709_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(lean_object* v_msg_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___f_2727_; lean_object* v___x_46802__overap_2728_; lean_object* v___x_2729_; 
v___f_2727_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0));
v___x_46802__overap_2728_ = lean_panic_fn_borrowed(v___f_2727_, v_msg_2718_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
lean_inc(v___y_2719_);
v___x_2729_ = lean_apply_8(v___x_46802__overap_2728_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___boxed(lean_object* v_msg_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v_msg_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(lean_object* v_k_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v_b_2744_, lean_object* v_c_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___x_2751_; 
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2743_);
lean_inc_ref(v___y_2742_);
lean_inc(v___y_2741_);
v___x_2751_ = lean_apply_10(v_k_2740_, v_b_2744_, v_c_2745_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, lean_box(0));
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed(lean_object* v_k_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v_b_2756_, lean_object* v_c_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(v_k_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v_b_2756_, v_c_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(lean_object* v_e_2764_, lean_object* v_k_2765_, uint8_t v_cleanupAnnotations_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___f_2775_; uint8_t v___x_2776_; uint8_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_inc(v___y_2769_);
lean_inc_ref(v___y_2768_);
lean_inc(v___y_2767_);
v___f_2775_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2775_, 0, v_k_2765_);
lean_closure_set(v___f_2775_, 1, v___y_2767_);
lean_closure_set(v___f_2775_, 2, v___y_2768_);
lean_closure_set(v___f_2775_, 3, v___y_2769_);
v___x_2776_ = 1;
v___x_2777_ = 0;
v___x_2778_ = lean_box(0);
v___x_2779_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2764_, v___x_2776_, v___x_2777_, v___x_2776_, v___x_2777_, v___x_2778_, v___f_2775_, v_cleanupAnnotations_2766_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2779_) == 0)
{
return v___x_2779_;
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___boxed(lean_object* v_e_2788_, lean_object* v_k_2789_, lean_object* v_cleanupAnnotations_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2799_; lean_object* v_res_2800_; 
v_cleanupAnnotations_boxed_2799_ = lean_unbox(v_cleanupAnnotations_2790_);
v_res_2800_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2788_, v_k_2789_, v_cleanupAnnotations_boxed_2799_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(lean_object* v_00_u03b1_2801_, lean_object* v_e_2802_, lean_object* v_k_2803_, uint8_t v_cleanupAnnotations_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2802_, v_k_2803_, v_cleanupAnnotations_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___boxed(lean_object* v_00_u03b1_2814_, lean_object* v_e_2815_, lean_object* v_k_2816_, lean_object* v_cleanupAnnotations_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2826_; lean_object* v_res_2827_; 
v_cleanupAnnotations_boxed_2826_ = lean_unbox(v_cleanupAnnotations_2817_);
v_res_2827_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(v_00_u03b1_2814_, v_e_2815_, v_k_2816_, v_cleanupAnnotations_boxed_2826_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(uint8_t v___x_2828_, uint8_t v___x_2829_, uint8_t v___x_2830_, lean_object* v_xs_2831_, lean_object* v_motiveBody_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; lean_object* v___x_2848_; 
v___x_2841_ = l_Lean_Expr_bindingDomain_x21(v_motiveBody_2832_);
v___x_2842_ = l_Lean_Expr_bindingName_x21(v___x_2841_);
v___x_2843_ = l_Lean_Expr_bindingDomain_x21(v___x_2841_);
v___x_2844_ = l_Lean_Expr_bindingBody_x21(v___x_2841_);
lean_dec_ref(v___x_2841_);
v___x_2845_ = l_Lean_Expr_bindingDomain_x21(v___x_2844_);
lean_dec_ref(v___x_2844_);
v___x_2846_ = l_Lean_Expr_lam___override(v___x_2842_, v___x_2843_, v___x_2845_, v___x_2828_);
v___x_2847_ = 1;
v___x_2848_ = l_Lean_Meta_mkLambdaFVars(v_xs_2831_, v___x_2846_, v___x_2829_, v___x_2830_, v___x_2829_, v___x_2830_, v___x_2847_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed(lean_object* v___x_2849_, lean_object* v___x_2850_, lean_object* v___x_2851_, lean_object* v_xs_2852_, lean_object* v_motiveBody_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
uint8_t v___x_54595__boxed_2862_; uint8_t v___x_54596__boxed_2863_; uint8_t v___x_54597__boxed_2864_; lean_object* v_res_2865_; 
v___x_54595__boxed_2862_ = lean_unbox(v___x_2849_);
v___x_54596__boxed_2863_ = lean_unbox(v___x_2850_);
v___x_54597__boxed_2864_ = lean_unbox(v___x_2851_);
v_res_2865_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(v___x_54595__boxed_2862_, v___x_54596__boxed_2863_, v___x_54597__boxed_2864_, v_xs_2852_, v_motiveBody_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v_motiveBody_2853_);
lean_dec_ref(v_xs_2852_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(size_t v_sz_2866_, size_t v_i_2867_, lean_object* v_bs_2868_){
_start:
{
uint8_t v___x_2869_; 
v___x_2869_ = lean_usize_dec_lt(v_i_2867_, v_sz_2866_);
if (v___x_2869_ == 0)
{
return v_bs_2868_;
}
else
{
lean_object* v_v_2870_; lean_object* v___x_2871_; lean_object* v_bs_x27_2872_; lean_object* v___x_2873_; size_t v___x_2874_; size_t v___x_2875_; lean_object* v___x_2876_; 
v_v_2870_ = lean_array_uget(v_bs_2868_, v_i_2867_);
v___x_2871_ = lean_unsigned_to_nat(0u);
v_bs_x27_2872_ = lean_array_uset(v_bs_2868_, v_i_2867_, v___x_2871_);
v___x_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2873_, 0, v_v_2870_);
v___x_2874_ = ((size_t)1ULL);
v___x_2875_ = lean_usize_add(v_i_2867_, v___x_2874_);
v___x_2876_ = lean_array_uset(v_bs_x27_2872_, v_i_2867_, v___x_2873_);
v_i_2867_ = v___x_2875_;
v_bs_2868_ = v___x_2876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4___boxed(lean_object* v_sz_2878_, lean_object* v_i_2879_, lean_object* v_bs_2880_){
_start:
{
size_t v_sz_boxed_2881_; size_t v_i_boxed_2882_; lean_object* v_res_2883_; 
v_sz_boxed_2881_ = lean_unbox_usize(v_sz_2878_);
lean_dec(v_sz_2878_);
v_i_boxed_2882_ = lean_unbox_usize(v_i_2879_);
lean_dec(v_i_2879_);
v_res_2883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_boxed_2881_, v_i_boxed_2882_, v_bs_2880_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(lean_object* v_msg_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_ref_2890_; lean_object* v___x_2891_; lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2900_; 
v_ref_2890_ = lean_ctor_get(v___y_2887_, 5);
v___x_2891_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
lean_inc(v_ref_2890_);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v_ref_2890_);
lean_ctor_set(v___x_2896_, 1, v_a_2892_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set_tag(v___x_2894_, 1);
lean_ctor_set(v___x_2894_, 0, v___x_2896_);
v___x_2898_ = v___x_2894_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg___boxed(lean_object* v_msg_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(lean_object* v_declName_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v___x_2911_; lean_object* v_env_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2911_ = lean_st_ref_get(v___y_2909_);
v_env_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc_ref(v_env_2912_);
lean_dec(v___x_2911_);
v___x_2913_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2912_, v_declName_2908_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg___boxed(lean_object* v_declName_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_2915_, v___y_2916_);
lean_dec(v___y_2916_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(lean_object* v_ref_2919_, lean_object* v_msg_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_fileName_2929_; lean_object* v_fileMap_2930_; lean_object* v_options_2931_; lean_object* v_currRecDepth_2932_; lean_object* v_maxRecDepth_2933_; lean_object* v_ref_2934_; lean_object* v_currNamespace_2935_; lean_object* v_openDecls_2936_; lean_object* v_initHeartbeats_2937_; lean_object* v_maxHeartbeats_2938_; lean_object* v_quotContext_2939_; lean_object* v_currMacroScope_2940_; uint8_t v_diag_2941_; lean_object* v_cancelTk_x3f_2942_; uint8_t v_suppressElabErrors_2943_; lean_object* v_inheritedTraceOptions_2944_; lean_object* v_ref_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_fileName_2929_ = lean_ctor_get(v___y_2926_, 0);
v_fileMap_2930_ = lean_ctor_get(v___y_2926_, 1);
v_options_2931_ = lean_ctor_get(v___y_2926_, 2);
v_currRecDepth_2932_ = lean_ctor_get(v___y_2926_, 3);
v_maxRecDepth_2933_ = lean_ctor_get(v___y_2926_, 4);
v_ref_2934_ = lean_ctor_get(v___y_2926_, 5);
v_currNamespace_2935_ = lean_ctor_get(v___y_2926_, 6);
v_openDecls_2936_ = lean_ctor_get(v___y_2926_, 7);
v_initHeartbeats_2937_ = lean_ctor_get(v___y_2926_, 8);
v_maxHeartbeats_2938_ = lean_ctor_get(v___y_2926_, 9);
v_quotContext_2939_ = lean_ctor_get(v___y_2926_, 10);
v_currMacroScope_2940_ = lean_ctor_get(v___y_2926_, 11);
v_diag_2941_ = lean_ctor_get_uint8(v___y_2926_, sizeof(void*)*14);
v_cancelTk_x3f_2942_ = lean_ctor_get(v___y_2926_, 12);
v_suppressElabErrors_2943_ = lean_ctor_get_uint8(v___y_2926_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2944_ = lean_ctor_get(v___y_2926_, 13);
v_ref_2945_ = l_Lean_replaceRef(v_ref_2919_, v_ref_2934_);
lean_inc_ref(v_inheritedTraceOptions_2944_);
lean_inc(v_cancelTk_x3f_2942_);
lean_inc(v_currMacroScope_2940_);
lean_inc(v_quotContext_2939_);
lean_inc(v_maxHeartbeats_2938_);
lean_inc(v_initHeartbeats_2937_);
lean_inc(v_openDecls_2936_);
lean_inc(v_currNamespace_2935_);
lean_inc(v_maxRecDepth_2933_);
lean_inc(v_currRecDepth_2932_);
lean_inc_ref(v_options_2931_);
lean_inc_ref(v_fileMap_2930_);
lean_inc_ref(v_fileName_2929_);
v___x_2946_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2946_, 0, v_fileName_2929_);
lean_ctor_set(v___x_2946_, 1, v_fileMap_2930_);
lean_ctor_set(v___x_2946_, 2, v_options_2931_);
lean_ctor_set(v___x_2946_, 3, v_currRecDepth_2932_);
lean_ctor_set(v___x_2946_, 4, v_maxRecDepth_2933_);
lean_ctor_set(v___x_2946_, 5, v_ref_2945_);
lean_ctor_set(v___x_2946_, 6, v_currNamespace_2935_);
lean_ctor_set(v___x_2946_, 7, v_openDecls_2936_);
lean_ctor_set(v___x_2946_, 8, v_initHeartbeats_2937_);
lean_ctor_set(v___x_2946_, 9, v_maxHeartbeats_2938_);
lean_ctor_set(v___x_2946_, 10, v_quotContext_2939_);
lean_ctor_set(v___x_2946_, 11, v_currMacroScope_2940_);
lean_ctor_set(v___x_2946_, 12, v_cancelTk_x3f_2942_);
lean_ctor_set(v___x_2946_, 13, v_inheritedTraceOptions_2944_);
lean_ctor_set_uint8(v___x_2946_, sizeof(void*)*14, v_diag_2941_);
lean_ctor_set_uint8(v___x_2946_, sizeof(void*)*14 + 1, v_suppressElabErrors_2943_);
v___x_2947_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2920_, v___y_2924_, v___y_2925_, v___x_2946_, v___y_2927_);
lean_dec_ref_known(v___x_2946_, 14);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2948_, lean_object* v_msg_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_2948_, v_msg_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec(v_ref_2948_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2959_, lean_object* v_declHint_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; lean_object* v_env_2964_; uint8_t v___y_2966_; uint8_t v___x_3024_; uint8_t v___x_3025_; 
v___x_2963_ = lean_st_ref_get(v___y_2961_);
v_env_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc_ref(v_env_2964_);
lean_dec(v___x_2963_);
v___x_3024_ = l_Lean_Name_isAnonymous(v_declHint_2960_);
v___x_3025_ = lean_bool_not(v___x_3024_);
if (v___x_3025_ == 0)
{
v___y_2966_ = v___x_3025_;
goto v___jp_2965_;
}
else
{
uint8_t v_isExporting_3026_; 
v_isExporting_3026_ = lean_ctor_get_uint8(v_env_2964_, sizeof(void*)*8);
v___y_2966_ = v_isExporting_3026_;
goto v___jp_2965_;
}
v___jp_2965_:
{
if (v___y_2966_ == 0)
{
lean_object* v___x_2967_; 
lean_dec_ref(v_env_2964_);
lean_dec(v_declHint_2960_);
v___x_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2967_, 0, v_msg_2959_);
return v___x_2967_;
}
else
{
uint8_t v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; 
v___x_2968_ = 0;
lean_inc_ref(v_env_2964_);
v___x_2969_ = l_Lean_Environment_setExporting(v_env_2964_, v___x_2968_);
lean_inc(v_declHint_2960_);
lean_inc_ref(v___x_2969_);
v___x_2970_ = l_Lean_Environment_contains(v___x_2969_, v_declHint_2960_, v___y_2966_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; 
lean_dec_ref(v___x_2969_);
lean_dec_ref(v_env_2964_);
lean_dec(v_declHint_2960_);
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v_msg_2959_);
return v___x_2971_;
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v_c_2979_; lean_object* v___x_2980_; 
v___x_2972_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2973_ = lean_unsigned_to_nat(32u);
v___x_2974_ = lean_mk_empty_array_with_capacity(v___x_2973_);
lean_dec_ref(v___x_2974_);
v___x_2975_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2976_ = l_Lean_Options_empty;
v___x_2977_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2969_);
lean_ctor_set(v___x_2977_, 1, v___x_2972_);
lean_ctor_set(v___x_2977_, 2, v___x_2975_);
lean_ctor_set(v___x_2977_, 3, v___x_2976_);
lean_inc(v_declHint_2960_);
v___x_2978_ = l_Lean_MessageData_ofConstName(v_declHint_2960_, v___x_2968_);
v_c_2979_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2979_, 0, v___x_2977_);
lean_ctor_set(v_c_2979_, 1, v___x_2978_);
v___x_2980_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2964_, v_declHint_2960_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec_ref(v_env_2964_);
lean_dec(v_declHint_2960_);
v___x_2981_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
lean_ctor_set(v___x_2982_, 1, v_c_2979_);
v___x_2983_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = l_Lean_MessageData_note(v___x_2984_);
v___x_2986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2986_, 0, v_msg_2959_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
return v___x_2987_;
}
else
{
lean_object* v_val_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3023_; 
v_val_2988_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_2990_ = v___x_2980_;
v_isShared_2991_ = v_isSharedCheck_3023_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_val_2988_);
lean_dec(v___x_2980_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3023_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v_mod_2995_; uint8_t v___x_2996_; 
v___x_2992_ = lean_box(0);
v___x_2993_ = l_Lean_Environment_header(v_env_2964_);
lean_dec_ref(v_env_2964_);
v___x_2994_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2993_);
v_mod_2995_ = lean_array_get(v___x_2992_, v___x_2994_, v_val_2988_);
lean_dec(v_val_2988_);
lean_dec_ref(v___x_2994_);
v___x_2996_ = l_Lean_isPrivateName(v_declHint_2960_);
lean_dec(v_declHint_2960_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_2997_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
lean_ctor_set(v___x_2998_, 1, v_c_2979_);
v___x_2999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_3000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = l_Lean_MessageData_ofName(v_mod_2995_);
v___x_3002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3000_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_3004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3002_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = l_Lean_MessageData_note(v___x_3004_);
v___x_3006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3006_, 0, v_msg_2959_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set_tag(v___x_2990_, 0);
lean_ctor_set(v___x_2990_, 0, v___x_3006_);
v___x_3008_ = v___x_2990_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3010_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v_c_2979_);
v___x_3012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3011_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v___x_3014_ = l_Lean_MessageData_ofName(v_mod_2995_);
v___x_3015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_3017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = l_Lean_MessageData_note(v___x_3017_);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v_msg_2959_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set_tag(v___x_2990_, 0);
lean_ctor_set(v___x_2990_, 0, v___x_3019_);
v___x_3021_ = v___x_2990_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_3027_, lean_object* v_declHint_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3027_, v_declHint_3028_, v___y_3029_);
lean_dec(v___y_3029_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(lean_object* v_msg_3032_, lean_object* v_declHint_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3052_; 
v___x_3042_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3032_, v_declHint_3033_, v___y_3040_);
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3052_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3052_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3047_ = l_Lean_unknownIdentifierMessageTag;
v___x_3048_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
lean_ctor_set(v___x_3048_, 1, v_a_3043_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3048_);
v___x_3050_ = v___x_3045_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11___boxed(lean_object* v_msg_3053_, lean_object* v_declHint_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3053_, v_declHint_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object* v_ref_3064_, lean_object* v_msg_3065_, lean_object* v_declHint_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v___x_3075_; lean_object* v_a_3076_; lean_object* v___x_3077_; 
v___x_3075_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3065_, v_declHint_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref(v___x_3075_);
v___x_3077_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3064_, v_a_3076_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_ref_3078_, lean_object* v_msg_3079_, lean_object* v_declHint_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3078_, v_msg_3079_, v_declHint_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec(v_ref_3078_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(lean_object* v_ref_3090_, lean_object* v_constName_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; uint8_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3100_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3101_ = 0;
lean_inc(v_constName_3091_);
v___x_3102_ = l_Lean_MessageData_ofConstName(v_constName_3091_, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3100_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3103_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3090_, v___x_3105_, v_constName_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_ref_3107_, lean_object* v_constName_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3107_, v_constName_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec(v_ref_3107_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v_ref_3127_; lean_object* v___x_3128_; 
v_ref_3127_ = lean_ctor_get(v___y_3124_, 5);
v___x_3128_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3127_, v_constName_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(lean_object* v_constName_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; lean_object* v_env_3149_; uint8_t v___x_3150_; lean_object* v___x_3151_; 
v___x_3148_ = lean_st_ref_get(v___y_3146_);
v_env_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc_ref(v_env_3149_);
lean_dec(v___x_3148_);
v___x_3150_ = 0;
lean_inc(v_constName_3139_);
v___x_3151_ = l_Lean_Environment_find_x3f(v_env_3149_, v_constName_3139_, v___x_3150_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3152_;
}
else
{
lean_object* v_val_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v_constName_3139_);
v_val_3153_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3151_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_val_3153_);
lean_dec(v___x_3151_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 0);
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_val_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0___boxed(lean_object* v_constName_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_constName_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
return v_res_3170_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_instMonadEIO(lean_box(0));
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(lean_object* v_msg_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v_toApplicative_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3251_; 
v___x_3185_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0);
v___x_3186_ = l_StateRefT_x27_instMonad___redArg(v___x_3185_);
v_toApplicative_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v___x_3186_, 1);
lean_dec(v_unused_3252_);
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3251_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_toApplicative_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3251_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v_toFunctor_3191_; lean_object* v_toSeq_3192_; lean_object* v_toSeqLeft_3193_; lean_object* v_toSeqRight_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3249_; 
v_toFunctor_3191_ = lean_ctor_get(v_toApplicative_3187_, 0);
v_toSeq_3192_ = lean_ctor_get(v_toApplicative_3187_, 2);
v_toSeqLeft_3193_ = lean_ctor_get(v_toApplicative_3187_, 3);
v_toSeqRight_3194_ = lean_ctor_get(v_toApplicative_3187_, 4);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_toApplicative_3187_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v_toApplicative_3187_, 1);
lean_dec(v_unused_3250_);
v___x_3196_ = v_toApplicative_3187_;
v_isShared_3197_ = v_isSharedCheck_3249_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_toSeqRight_3194_);
lean_inc(v_toSeqLeft_3193_);
lean_inc(v_toSeq_3192_);
lean_inc(v_toFunctor_3191_);
lean_dec(v_toApplicative_3187_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3249_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___f_3198_; lean_object* v___f_3199_; lean_object* v___f_3200_; lean_object* v___f_3201_; lean_object* v___x_3202_; lean_object* v___f_3203_; lean_object* v___f_3204_; lean_object* v___f_3205_; lean_object* v___x_3207_; 
v___f_3198_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__1));
v___f_3199_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3191_);
v___f_3200_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3200_, 0, v_toFunctor_3191_);
v___f_3201_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3201_, 0, v_toFunctor_3191_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___f_3200_);
lean_ctor_set(v___x_3202_, 1, v___f_3201_);
v___f_3203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3203_, 0, v_toSeqRight_3194_);
v___f_3204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3204_, 0, v_toSeqLeft_3193_);
v___f_3205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3205_, 0, v_toSeq_3192_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 4, v___f_3203_);
lean_ctor_set(v___x_3196_, 3, v___f_3204_);
lean_ctor_set(v___x_3196_, 2, v___f_3205_);
lean_ctor_set(v___x_3196_, 1, v___f_3198_);
lean_ctor_set(v___x_3196_, 0, v___x_3202_);
v___x_3207_ = v___x_3196_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v___f_3198_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v___f_3205_);
lean_ctor_set(v_reuseFailAlloc_3248_, 3, v___f_3204_);
lean_ctor_set(v_reuseFailAlloc_3248_, 4, v___f_3203_);
v___x_3207_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3209_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 1, v___f_3199_);
lean_ctor_set(v___x_3189_, 0, v___x_3207_);
v___x_3209_ = v___x_3189_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3207_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v___f_3199_);
v___x_3209_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; lean_object* v_toApplicative_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3245_; 
v___x_3210_ = l_StateRefT_x27_instMonad___redArg(v___x_3209_);
v_toApplicative_3211_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v___x_3210_, 1);
lean_dec(v_unused_3246_);
v___x_3213_ = v___x_3210_;
v_isShared_3214_ = v_isSharedCheck_3245_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_toApplicative_3211_);
lean_dec(v___x_3210_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3245_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v_toFunctor_3215_; lean_object* v_toSeq_3216_; lean_object* v_toSeqLeft_3217_; lean_object* v_toSeqRight_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3243_; 
v_toFunctor_3215_ = lean_ctor_get(v_toApplicative_3211_, 0);
v_toSeq_3216_ = lean_ctor_get(v_toApplicative_3211_, 2);
v_toSeqLeft_3217_ = lean_ctor_get(v_toApplicative_3211_, 3);
v_toSeqRight_3218_ = lean_ctor_get(v_toApplicative_3211_, 4);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_toApplicative_3211_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v_toApplicative_3211_, 1);
lean_dec(v_unused_3244_);
v___x_3220_ = v_toApplicative_3211_;
v_isShared_3221_ = v_isSharedCheck_3243_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_toSeqRight_3218_);
lean_inc(v_toSeqLeft_3217_);
lean_inc(v_toSeq_3216_);
lean_inc(v_toFunctor_3215_);
lean_dec(v_toApplicative_3211_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3243_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___f_3222_; lean_object* v___f_3223_; lean_object* v___f_3224_; lean_object* v___f_3225_; lean_object* v___x_3226_; lean_object* v___f_3227_; lean_object* v___f_3228_; lean_object* v___f_3229_; lean_object* v___x_3231_; 
v___f_3222_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__3));
v___f_3223_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3215_);
v___f_3224_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3224_, 0, v_toFunctor_3215_);
v___f_3225_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3225_, 0, v_toFunctor_3215_);
v___x_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___f_3224_);
lean_ctor_set(v___x_3226_, 1, v___f_3225_);
v___f_3227_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3227_, 0, v_toSeqRight_3218_);
v___f_3228_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3228_, 0, v_toSeqLeft_3217_);
v___f_3229_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3229_, 0, v_toSeq_3216_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 4, v___f_3227_);
lean_ctor_set(v___x_3220_, 3, v___f_3228_);
lean_ctor_set(v___x_3220_, 2, v___f_3229_);
lean_ctor_set(v___x_3220_, 1, v___f_3222_);
lean_ctor_set(v___x_3220_, 0, v___x_3226_);
v___x_3231_ = v___x_3220_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3226_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v___f_3222_);
lean_ctor_set(v_reuseFailAlloc_3242_, 2, v___f_3229_);
lean_ctor_set(v_reuseFailAlloc_3242_, 3, v___f_3228_);
lean_ctor_set(v_reuseFailAlloc_3242_, 4, v___f_3227_);
v___x_3231_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3233_; 
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 1, v___f_3223_);
lean_ctor_set(v___x_3213_, 0, v___x_3231_);
v___x_3233_ = v___x_3213_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3231_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v___f_3223_);
v___x_3233_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_48876__overap_3239_; lean_object* v___x_3240_; 
v___x_3234_ = l_StateRefT_x27_instMonad___redArg(v___x_3233_);
v___x_3235_ = l_ReaderT_instMonad___redArg(v___x_3234_);
v___x_3236_ = l_ReaderT_instMonad___redArg(v___x_3235_);
v___x_3237_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3238_ = l_instInhabitedOfMonad___redArg(v___x_3236_, v___x_3237_);
v___x_48876__overap_3239_ = lean_panic_fn_borrowed(v___x_3238_, v_msg_3176_);
lean_dec(v___x_3238_);
lean_inc(v___y_3183_);
lean_inc_ref(v___y_3182_);
lean_inc(v___y_3181_);
lean_inc_ref(v___y_3180_);
lean_inc(v___y_3179_);
lean_inc_ref(v___y_3178_);
lean_inc(v___y_3177_);
v___x_3240_ = lean_apply_8(v___x_48876__overap_3239_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, lean_box(0));
return v___x_3240_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___boxed(lean_object* v_msg_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v_msg_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
return v_res_3262_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__2));
v___x_3267_ = lean_unsigned_to_nat(53u);
v___x_3268_ = lean_unsigned_to_nat(62u);
v___x_3269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__1));
v___x_3270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__0));
v___x_3271_ = l_mkPanicMessageWithDecl(v___x_3270_, v___x_3269_, v___x_3268_, v___x_3267_, v___x_3266_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(size_t v_sz_3272_, size_t v_i_3273_, lean_object* v_bs_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
uint8_t v___x_3283_; 
v___x_3283_ = lean_usize_dec_lt(v_i_3273_, v_sz_3272_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3284_, 0, v_bs_3274_);
return v___x_3284_;
}
else
{
lean_object* v_v_3285_; lean_object* v___x_3286_; 
v_v_3285_ = lean_array_uget_borrowed(v_bs_3274_, v_i_3273_);
lean_inc(v_v_3285_);
v___x_3286_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_v_3285_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; lean_object* v_bs_x27_3289_; lean_object* v_a_3291_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
v___x_3288_ = lean_unsigned_to_nat(0u);
v_bs_x27_3289_ = lean_array_uset(v_bs_3274_, v_i_3273_, v___x_3288_);
if (lean_obj_tag(v_a_3287_) == 6)
{
lean_object* v_val_3296_; lean_object* v_numFields_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; 
v_val_3296_ = lean_ctor_get(v_a_3287_, 0);
lean_inc_ref(v_val_3296_);
lean_dec_ref_known(v_a_3287_, 1);
v_numFields_3297_ = lean_ctor_get(v_val_3296_, 4);
lean_inc(v_numFields_3297_);
lean_dec_ref(v_val_3296_);
v___x_3298_ = 0;
v___x_3299_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3299_, 0, v_numFields_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3288_);
lean_ctor_set_uint8(v___x_3299_, sizeof(void*)*2, v___x_3298_);
v_a_3291_ = v___x_3299_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_dec(v_a_3287_);
v___x_3300_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3);
v___x_3301_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v___x_3300_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v_a_3291_ = v_a_3302_;
goto v___jp_3290_;
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec_ref(v_bs_x27_3289_);
v_a_3303_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3301_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3301_);
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
v___jp_3290_:
{
size_t v___x_3292_; size_t v___x_3293_; lean_object* v___x_3294_; 
v___x_3292_ = ((size_t)1ULL);
v___x_3293_ = lean_usize_add(v_i_3273_, v___x_3292_);
v___x_3294_ = lean_array_uset(v_bs_x27_3289_, v_i_3273_, v_a_3291_);
v_i_3273_ = v___x_3293_;
v_bs_3274_ = v___x_3294_;
goto _start;
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec_ref(v_bs_3274_);
v_a_3311_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3286_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3286_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___boxed(lean_object* v_sz_3319_, lean_object* v_i_3320_, lean_object* v_bs_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
size_t v_sz_boxed_3330_; size_t v_i_boxed_3331_; lean_object* v_res_3332_; 
v_sz_boxed_3330_ = lean_unbox_usize(v_sz_3319_);
lean_dec(v_sz_3319_);
v_i_boxed_3331_ = lean_unbox_usize(v_i_3320_);
lean_dec(v_i_3320_);
v_res_3332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_boxed_3330_, v_i_boxed_3331_, v_bs_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
return v_res_3332_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = lean_box(0);
v___x_3334_ = lean_unsigned_to_nat(16u);
v___x_3335_ = lean_mk_array(v___x_3334_, v___x_3333_);
return v___x_3335_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0);
v___x_3337_ = lean_unsigned_to_nat(0u);
v___x_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
lean_ctor_set(v___x_3338_, 1, v___x_3336_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(lean_object* v_e_3341_, uint8_t v_alsoCasesOn_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
uint8_t v___x_3354_; 
v___x_3354_ = l_Lean_Expr_isApp(v_e_3341_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
lean_dec_ref(v_e_3341_);
v___x_3355_ = lean_box(0);
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
return v___x_3356_;
}
else
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Lean_Expr_getAppFn(v_e_3341_);
if (lean_obj_tag(v___x_3357_) == 4)
{
lean_object* v_declName_3358_; lean_object* v_us_3359_; lean_object* v___x_3360_; lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3515_; 
v_declName_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc_n(v_declName_3358_, 2);
v_us_3359_ = lean_ctor_get(v___x_3357_, 1);
lean_inc(v_us_3359_);
lean_dec_ref_known(v___x_3357_, 2);
v___x_3360_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3358_, v___y_3349_);
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3363_ = v___x_3360_;
v_isShared_3364_ = v_isSharedCheck_3515_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3360_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3515_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
if (lean_obj_tag(v_a_3361_) == 1)
{
lean_object* v_val_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3407_; 
v_val_3365_ = lean_ctor_get(v_a_3361_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_a_3361_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3367_ = v_a_3361_;
v_isShared_3368_ = v_isSharedCheck_3407_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_val_3365_);
lean_dec(v_a_3361_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3407_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v_dummy_3369_; lean_object* v_nargs_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v_args_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; 
v_dummy_3369_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_3370_ = l_Lean_Expr_getAppNumArgs(v_e_3341_);
lean_inc(v_nargs_3370_);
v___x_3371_ = lean_mk_array(v_nargs_3370_, v_dummy_3369_);
v___x_3372_ = lean_unsigned_to_nat(1u);
v___x_3373_ = lean_nat_sub(v_nargs_3370_, v___x_3372_);
lean_dec(v_nargs_3370_);
v_args_3374_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3341_, v___x_3371_, v___x_3373_);
v___x_3375_ = lean_array_get_size(v_args_3374_);
v___x_3376_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_3365_);
v___x_3377_ = lean_nat_dec_lt(v___x_3375_, v___x_3376_);
lean_dec(v___x_3376_);
if (v___x_3377_ == 0)
{
lean_object* v_numParams_3378_; lean_object* v_numDiscrs_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v_numParams_3378_ = lean_ctor_get(v_val_3365_, 0);
v_numDiscrs_3379_ = lean_ctor_get(v_val_3365_, 1);
v___x_3380_ = lean_array_mk(v_us_3359_);
v___x_3381_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3378_);
v___x_3382_ = l_Array_extract___redArg(v_args_3374_, v___x_3381_, v_numParams_3378_);
v___x_3383_ = l_Lean_instInhabitedExpr;
v___x_3384_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3365_);
v___x_3385_ = lean_array_get(v___x_3383_, v_args_3374_, v___x_3384_);
lean_dec(v___x_3384_);
v___x_3386_ = lean_nat_add(v_numParams_3378_, v___x_3372_);
v___x_3387_ = lean_nat_add(v___x_3386_, v_numDiscrs_3379_);
lean_inc(v___x_3387_);
lean_inc_ref_n(v_args_3374_, 2);
v___x_3388_ = l_Array_toSubarray___redArg(v_args_3374_, v___x_3386_, v___x_3387_);
v___x_3389_ = l_Subarray_copy___redArg(v___x_3388_);
v___x_3390_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3365_);
v___x_3391_ = lean_nat_add(v___x_3387_, v___x_3390_);
lean_dec(v___x_3390_);
lean_inc(v___x_3391_);
v___x_3392_ = l_Array_toSubarray___redArg(v_args_3374_, v___x_3387_, v___x_3391_);
v___x_3393_ = l_Subarray_copy___redArg(v___x_3392_);
v___x_3394_ = l_Array_toSubarray___redArg(v_args_3374_, v___x_3391_, v___x_3375_);
v___x_3395_ = l_Subarray_copy___redArg(v___x_3394_);
v___x_3396_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3396_, 0, v_val_3365_);
lean_ctor_set(v___x_3396_, 1, v_declName_3358_);
lean_ctor_set(v___x_3396_, 2, v___x_3380_);
lean_ctor_set(v___x_3396_, 3, v___x_3382_);
lean_ctor_set(v___x_3396_, 4, v___x_3385_);
lean_ctor_set(v___x_3396_, 5, v___x_3389_);
lean_ctor_set(v___x_3396_, 6, v___x_3393_);
lean_ctor_set(v___x_3396_, 7, v___x_3395_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3396_);
v___x_3398_ = v___x_3367_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3400_; 
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v___x_3398_);
v___x_3400_ = v___x_3363_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
else
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
lean_dec_ref(v_args_3374_);
lean_del_object(v___x_3367_);
lean_dec(v_val_3365_);
lean_dec(v_us_3359_);
lean_dec(v_declName_3358_);
v___x_3403_ = lean_box(0);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v___x_3403_);
v___x_3405_ = v___x_3363_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v___x_3408_; 
lean_del_object(v___x_3363_);
lean_dec(v_a_3361_);
v___x_3408_ = lean_st_ref_get(v___y_3349_);
if (v_alsoCasesOn_3342_ == 0)
{
lean_dec(v___x_3408_);
lean_dec(v_us_3359_);
lean_dec(v_declName_3358_);
lean_dec_ref(v_e_3341_);
goto v___jp_3351_;
}
else
{
lean_object* v_env_3409_; uint8_t v___x_3410_; 
v_env_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc_ref(v_env_3409_);
lean_dec(v___x_3408_);
lean_inc(v_declName_3358_);
v___x_3410_ = l_Lean_isCasesOnRecursor(v_env_3409_, v_declName_3358_);
if (v___x_3410_ == 0)
{
lean_dec(v_us_3359_);
lean_dec(v_declName_3358_);
lean_dec_ref(v_e_3341_);
goto v___jp_3351_;
}
else
{
lean_object* v_indName_3411_; lean_object* v___x_3412_; 
v_indName_3411_ = l_Lean_Name_getPrefix(v_declName_3358_);
v___x_3412_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_indName_3411_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3506_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3415_ = v___x_3412_;
v_isShared_3416_ = v_isSharedCheck_3506_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3412_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3506_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
if (lean_obj_tag(v_a_3413_) == 5)
{
lean_object* v_val_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3501_; 
v_val_3417_ = lean_ctor_get(v_a_3413_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_a_3413_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3419_ = v_a_3413_;
v_isShared_3420_ = v_isSharedCheck_3501_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_val_3417_);
lean_dec(v_a_3413_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3501_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_toConstantVal_3421_; lean_object* v_numParams_3422_; lean_object* v_numIndices_3423_; lean_object* v_ctors_3424_; lean_object* v_nargs_3425_; lean_object* v_dummy_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v_args_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v_toConstantVal_3421_ = lean_ctor_get(v_val_3417_, 0);
lean_inc_ref(v_toConstantVal_3421_);
v_numParams_3422_ = lean_ctor_get(v_val_3417_, 1);
lean_inc(v_numParams_3422_);
v_numIndices_3423_ = lean_ctor_get(v_val_3417_, 2);
lean_inc(v_numIndices_3423_);
v_ctors_3424_ = lean_ctor_get(v_val_3417_, 4);
lean_inc(v_ctors_3424_);
v_nargs_3425_ = l_Lean_Expr_getAppNumArgs(v_e_3341_);
v_dummy_3426_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_3425_);
v___x_3427_ = lean_mk_array(v_nargs_3425_, v_dummy_3426_);
v___x_3428_ = lean_unsigned_to_nat(1u);
v___x_3429_ = lean_nat_sub(v_nargs_3425_, v___x_3428_);
lean_dec(v_nargs_3425_);
v_args_3430_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3341_, v___x_3427_, v___x_3429_);
v___x_3431_ = lean_nat_add(v_numParams_3422_, v___x_3428_);
v___x_3432_ = lean_nat_add(v___x_3431_, v_numIndices_3423_);
v___x_3433_ = lean_nat_add(v___x_3432_, v___x_3428_);
lean_dec(v___x_3432_);
v___x_3434_ = l_Lean_InductiveVal_numCtors(v_val_3417_);
lean_dec_ref(v_val_3417_);
v___x_3435_ = lean_nat_add(v___x_3433_, v___x_3434_);
lean_dec(v___x_3434_);
v___x_3436_ = lean_array_get_size(v_args_3430_);
v___x_3437_ = lean_nat_dec_le(v___x_3435_, v___x_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
lean_dec(v___x_3435_);
lean_dec(v___x_3433_);
lean_dec(v___x_3431_);
lean_dec_ref(v_args_3430_);
lean_dec(v_ctors_3424_);
lean_dec(v_numIndices_3423_);
lean_dec(v_numParams_3422_);
lean_dec_ref(v_toConstantVal_3421_);
lean_del_object(v___x_3419_);
lean_dec(v_us_3359_);
lean_dec(v_declName_3358_);
v___x_3438_ = lean_box(0);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v___x_3438_);
v___x_3440_ = v___x_3415_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
else
{
lean_object* v___x_3442_; lean_object* v_params_3443_; lean_object* v___x_3444_; lean_object* v_motive_3445_; lean_object* v_discrs_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v_discrInfos_3449_; lean_object* v_alts_3450_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v_lower_3492_; lean_object* v_upper_3493_; uint8_t v___x_3500_; 
lean_del_object(v___x_3415_);
v___x_3442_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3422_);
lean_inc_ref_n(v_args_3430_, 3);
v_params_3443_ = l_Array_toSubarray___redArg(v_args_3430_, v___x_3442_, v_numParams_3422_);
v___x_3444_ = l_Lean_instInhabitedExpr;
v_motive_3445_ = lean_array_get(v___x_3444_, v_args_3430_, v_numParams_3422_);
lean_dec(v_numParams_3422_);
lean_inc(v___x_3433_);
v_discrs_3446_ = l_Array_toSubarray___redArg(v_args_3430_, v___x_3431_, v___x_3433_);
v___x_3447_ = lean_nat_add(v_numIndices_3423_, v___x_3428_);
lean_dec(v_numIndices_3423_);
v___x_3448_ = lean_box(0);
v_discrInfos_3449_ = lean_mk_array(v___x_3447_, v___x_3448_);
lean_inc(v___x_3435_);
v_alts_3450_ = l_Array_toSubarray___redArg(v_args_3430_, v___x_3433_, v___x_3435_);
v___x_3500_ = lean_nat_dec_le(v___x_3435_, v___x_3442_);
if (v___x_3500_ == 0)
{
v_lower_3492_ = v___x_3435_;
v_upper_3493_ = v___x_3436_;
goto v___jp_3491_;
}
else
{
lean_dec(v___x_3435_);
v_lower_3492_ = v___x_3442_;
v_upper_3493_ = v___x_3436_;
goto v___jp_3491_;
}
v___jp_3451_:
{
lean_object* v___x_3454_; size_t v_sz_3455_; size_t v___x_3456_; lean_object* v___x_3457_; 
v___x_3454_ = lean_array_mk(v_ctors_3424_);
v_sz_3455_ = lean_array_size(v___x_3454_);
v___x_3456_ = ((size_t)0ULL);
v___x_3457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_3455_, v___x_3456_, v___x_3454_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3482_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3460_ = v___x_3457_;
v_isShared_3461_ = v_isSharedCheck_3482_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3457_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3482_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v_start_3462_; lean_object* v_stop_3463_; lean_object* v_start_3464_; lean_object* v_stop_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3477_; 
v_start_3462_ = lean_ctor_get(v_params_3443_, 1);
lean_inc(v_start_3462_);
v_stop_3463_ = lean_ctor_get(v_params_3443_, 2);
lean_inc(v_stop_3463_);
v_start_3464_ = lean_ctor_get(v_discrs_3446_, 1);
lean_inc(v_start_3464_);
v_stop_3465_ = lean_ctor_get(v_discrs_3446_, 2);
lean_inc(v_stop_3465_);
v___x_3466_ = lean_nat_sub(v_stop_3463_, v_start_3462_);
lean_dec(v_start_3462_);
lean_dec(v_stop_3463_);
v___x_3467_ = lean_nat_sub(v_stop_3465_, v_start_3464_);
lean_dec(v_start_3464_);
lean_dec(v_stop_3465_);
v___x_3468_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1);
v___x_3469_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3466_);
lean_ctor_set(v___x_3469_, 1, v___x_3467_);
lean_ctor_set(v___x_3469_, 2, v_a_3458_);
lean_ctor_set(v___x_3469_, 3, v___y_3453_);
lean_ctor_set(v___x_3469_, 4, v_discrInfos_3449_);
lean_ctor_set(v___x_3469_, 5, v___x_3468_);
v___x_3470_ = lean_array_mk(v_us_3359_);
v___x_3471_ = l_Subarray_copy___redArg(v_params_3443_);
v___x_3472_ = l_Subarray_copy___redArg(v_discrs_3446_);
v___x_3473_ = l_Subarray_copy___redArg(v_alts_3450_);
v___x_3474_ = l_Subarray_copy___redArg(v___y_3452_);
v___x_3475_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3469_);
lean_ctor_set(v___x_3475_, 1, v_declName_3358_);
lean_ctor_set(v___x_3475_, 2, v___x_3470_);
lean_ctor_set(v___x_3475_, 3, v___x_3471_);
lean_ctor_set(v___x_3475_, 4, v_motive_3445_);
lean_ctor_set(v___x_3475_, 5, v___x_3472_);
lean_ctor_set(v___x_3475_, 6, v___x_3473_);
lean_ctor_set(v___x_3475_, 7, v___x_3474_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set_tag(v___x_3419_, 1);
lean_ctor_set(v___x_3419_, 0, v___x_3475_);
v___x_3477_ = v___x_3419_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3479_; 
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3477_);
v___x_3479_ = v___x_3460_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec_ref(v_alts_3450_);
lean_dec_ref(v_discrInfos_3449_);
lean_dec_ref(v_discrs_3446_);
lean_dec(v_motive_3445_);
lean_dec_ref(v_params_3443_);
lean_del_object(v___x_3419_);
lean_dec(v_us_3359_);
lean_dec(v_declName_3358_);
v_a_3483_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3457_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3457_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
v___jp_3491_:
{
lean_object* v_levelParams_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v_levelParams_3494_ = lean_ctor_get(v_toConstantVal_3421_, 1);
lean_inc(v_levelParams_3494_);
lean_dec_ref(v_toConstantVal_3421_);
v___x_3495_ = l_Array_toSubarray___redArg(v_args_3430_, v_lower_3492_, v_upper_3493_);
v___x_3496_ = l_List_lengthTR___redArg(v_levelParams_3494_);
lean_dec(v_levelParams_3494_);
v___x_3497_ = l_List_lengthTR___redArg(v_us_3359_);
v___x_3498_ = lean_nat_dec_eq(v___x_3496_, v___x_3497_);
lean_dec(v___x_3497_);
lean_dec(v___x_3496_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
v___x_3499_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__2));
v___y_3452_ = v___x_3495_;
v___y_3453_ = v___x_3499_;
goto v___jp_3451_;
}
else
{
v___y_3452_ = v___x_3495_;
v___y_3453_ = v___x_3448_;
goto v___jp_3451_;
}
}
}
}
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
lean_dec(v_a_3413_);
lean_dec(v_us_3359_);
lean_dec(v_declName_3358_);
lean_dec_ref(v_e_3341_);
v___x_3502_ = lean_box(0);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v___x_3502_);
v___x_3504_ = v___x_3415_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
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
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec(v_us_3359_);
lean_dec(v_declName_3358_);
lean_dec_ref(v_e_3341_);
v_a_3507_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3412_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3412_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
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
lean_dec_ref(v___x_3357_);
lean_dec_ref(v_e_3341_);
goto v___jp_3351_;
}
}
v___jp_3351_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = lean_box(0);
v___x_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___boxed(lean_object* v_e_3516_, lean_object* v_alsoCasesOn_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
uint8_t v_alsoCasesOn_boxed_3526_; lean_object* v_res_3527_; 
v_alsoCasesOn_boxed_3526_ = lean_unbox(v_alsoCasesOn_3517_);
v_res_3527_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3516_, v_alsoCasesOn_boxed_3526_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
return v_res_3527_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__1));
v___x_3532_ = l_Lean_stringToMessageData(v___x_3531_);
return v___x_3532_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = lean_unsigned_to_nat(1u);
v___x_3534_ = l_Lean_Expr_bvar___override(v___x_3533_);
return v___x_3534_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3537_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__5));
v___x_3538_ = lean_unsigned_to_nat(2u);
v___x_3539_ = lean_unsigned_to_nat(182u);
v___x_3540_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__4));
v___x_3541_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_3542_ = l_mkPanicMessageWithDecl(v___x_3541_, v___x_3540_, v___x_3539_, v___x_3538_, v___x_3537_);
return v___x_3542_;
}
}
static uint64_t _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7(void){
_start:
{
uint8_t v___x_3543_; uint64_t v___x_3544_; 
v___x_3543_ = 0;
v___x_3544_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(lean_object* v_e_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_){
_start:
{
lean_object* v_e_3554_; uint8_t v___x_3555_; lean_object* v___x_3556_; 
v_e_3554_ = l_Lean_Expr_headBeta(v_e_3545_);
v___x_3555_ = 1;
v___x_3556_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3554_, v___x_3555_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3846_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3846_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3846_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
if (lean_obj_tag(v_a_3557_) == 1)
{
lean_object* v_val_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3841_; 
v_val_3561_ = lean_ctor_get(v_a_3557_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v_a_3557_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3563_ = v_a_3557_;
v_isShared_3564_ = v_isSharedCheck_3841_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_val_3561_);
lean_dec(v_a_3557_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3841_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v_toMatcherInfo_3565_; lean_object* v_matcherName_3566_; lean_object* v_params_3567_; lean_object* v_motive_3568_; lean_object* v_discrs_3569_; lean_object* v_alts_3570_; lean_object* v_remaining_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v_toMatcherInfo_3565_ = lean_ctor_get(v_val_3561_, 0);
lean_inc_ref(v_toMatcherInfo_3565_);
v_matcherName_3566_ = lean_ctor_get(v_val_3561_, 1);
lean_inc(v_matcherName_3566_);
v_params_3567_ = lean_ctor_get(v_val_3561_, 3);
lean_inc_ref(v_params_3567_);
v_motive_3568_ = lean_ctor_get(v_val_3561_, 4);
lean_inc_ref(v_motive_3568_);
v_discrs_3569_ = lean_ctor_get(v_val_3561_, 5);
lean_inc_ref(v_discrs_3569_);
v_alts_3570_ = lean_ctor_get(v_val_3561_, 6);
lean_inc_ref(v_alts_3570_);
v_remaining_3571_ = lean_ctor_get(v_val_3561_, 7);
lean_inc_ref(v_remaining_3571_);
v___x_3572_ = lean_unsigned_to_nat(0u);
v___x_3573_ = lean_array_get_size(v_remaining_3571_);
v___x_3574_ = lean_nat_dec_lt(v___x_3572_, v___x_3573_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3575_; lean_object* v___x_3577_; 
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
lean_dec(v_val_3561_);
v___x_3575_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3575_);
v___x_3577_ = v___x_3559_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
else
{
lean_object* v___x_3579_; uint8_t v___x_3580_; 
v___x_3579_ = lean_array_fget_borrowed(v_remaining_3571_, v___x_3572_);
v___x_3580_ = l_Lean_Expr_isLambda(v___x_3579_);
if (v___x_3580_ == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
lean_dec(v_val_3561_);
v___x_3581_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3581_);
v___x_3583_ = v___x_3559_;
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
v___x_3585_ = l_Lean_Expr_bindingBody_x21(v___x_3579_);
v___x_3586_ = l_Lean_Expr_isLambda(v___x_3585_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3589_; 
lean_dec_ref(v___x_3585_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
lean_dec(v_val_3561_);
v___x_3587_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3587_);
v___x_3589_ = v___x_3559_;
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
lean_dec_ref(v___x_3585_);
v___x_3592_ = l_Lean_Expr_isApp(v___x_3591_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; lean_object* v___x_3595_; 
lean_dec_ref(v___x_3591_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
lean_dec(v_val_3561_);
v___x_3593_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3593_);
v___x_3595_ = v___x_3559_;
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
uint8_t v___x_3597_; 
v___x_3597_ = lean_expr_has_loose_bvar(v___x_3591_, v___x_3572_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v_a_3601_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v___x_3598_ = l_Lean_Expr_appArg_x21(v___x_3591_);
v___x_3599_ = lean_unsigned_to_nat(1u);
v___x_3655_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3);
v___x_3656_ = lean_expr_eqv(v___x_3598_, v___x_3655_);
lean_dec_ref(v___x_3598_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3659_; 
lean_dec_ref(v___x_3591_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
lean_dec(v_val_3561_);
v___x_3657_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3657_);
v___x_3659_ = v___x_3559_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
else
{
lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___x_3661_ = l_Lean_Expr_appFn_x21(v___x_3591_);
lean_dec_ref(v___x_3591_);
v___x_3662_ = lean_expr_has_loose_bvar(v___x_3661_, v___x_3599_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; 
lean_del_object(v___x_3559_);
lean_inc(v_a_3552_);
lean_inc_ref(v_a_3551_);
lean_inc(v_a_3550_);
lean_inc_ref(v_a_3549_);
lean_inc_ref(v___x_3661_);
v___x_3663_ = lean_infer_type(v___x_3661_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3665_; uint8_t v_foApprox_3666_; uint8_t v_ctxApprox_3667_; uint8_t v_quasiPatternApprox_3668_; uint8_t v_constApprox_3669_; uint8_t v_isDefEqStuckEx_3670_; uint8_t v_unificationHints_3671_; uint8_t v_proofIrrelevance_3672_; uint8_t v_assignSyntheticOpaque_3673_; uint8_t v_offsetCnstrs_3674_; uint8_t v_etaStruct_3675_; uint8_t v_univApprox_3676_; uint8_t v_iota_3677_; uint8_t v_beta_3678_; uint8_t v_proj_3679_; uint8_t v_zeta_3680_; uint8_t v_zetaDelta_3681_; uint8_t v_zetaUnused_3682_; uint8_t v_zetaHave_3683_; uint8_t v_trackZetaDelta_3684_; lean_object* v_zetaDeltaSet_3685_; lean_object* v_lctx_3686_; lean_object* v_localInstances_3687_; lean_object* v_defEqCtx_x3f_3688_; lean_object* v_synthPendingDepth_3689_; lean_object* v_canUnfold_x3f_3690_; uint8_t v_univApprox_3691_; uint8_t v_inTypeClassResolution_3692_; uint8_t v_cacheInferType_3693_; uint8_t v___x_3694_; lean_object* v_a_3696_; lean_object* v_config_3805_; uint64_t v___x_3806_; uint64_t v___x_3807_; uint64_t v___x_3808_; uint64_t v___x_3809_; uint64_t v___x_3810_; uint64_t v_key_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
v___x_3665_ = l_Lean_Meta_Context_config(v_a_3549_);
v_foApprox_3666_ = lean_ctor_get_uint8(v___x_3665_, 0);
v_ctxApprox_3667_ = lean_ctor_get_uint8(v___x_3665_, 1);
v_quasiPatternApprox_3668_ = lean_ctor_get_uint8(v___x_3665_, 2);
v_constApprox_3669_ = lean_ctor_get_uint8(v___x_3665_, 3);
v_isDefEqStuckEx_3670_ = lean_ctor_get_uint8(v___x_3665_, 4);
v_unificationHints_3671_ = lean_ctor_get_uint8(v___x_3665_, 5);
v_proofIrrelevance_3672_ = lean_ctor_get_uint8(v___x_3665_, 6);
v_assignSyntheticOpaque_3673_ = lean_ctor_get_uint8(v___x_3665_, 7);
v_offsetCnstrs_3674_ = lean_ctor_get_uint8(v___x_3665_, 8);
v_etaStruct_3675_ = lean_ctor_get_uint8(v___x_3665_, 10);
v_univApprox_3676_ = lean_ctor_get_uint8(v___x_3665_, 11);
v_iota_3677_ = lean_ctor_get_uint8(v___x_3665_, 12);
v_beta_3678_ = lean_ctor_get_uint8(v___x_3665_, 13);
v_proj_3679_ = lean_ctor_get_uint8(v___x_3665_, 14);
v_zeta_3680_ = lean_ctor_get_uint8(v___x_3665_, 15);
v_zetaDelta_3681_ = lean_ctor_get_uint8(v___x_3665_, 16);
v_zetaUnused_3682_ = lean_ctor_get_uint8(v___x_3665_, 17);
v_zetaHave_3683_ = lean_ctor_get_uint8(v___x_3665_, 18);
v_trackZetaDelta_3684_ = lean_ctor_get_uint8(v_a_3549_, sizeof(void*)*7);
v_zetaDeltaSet_3685_ = lean_ctor_get(v_a_3549_, 1);
v_lctx_3686_ = lean_ctor_get(v_a_3549_, 2);
v_localInstances_3687_ = lean_ctor_get(v_a_3549_, 3);
v_defEqCtx_x3f_3688_ = lean_ctor_get(v_a_3549_, 4);
v_synthPendingDepth_3689_ = lean_ctor_get(v_a_3549_, 5);
v_canUnfold_x3f_3690_ = lean_ctor_get(v_a_3549_, 6);
v_univApprox_3691_ = lean_ctor_get_uint8(v_a_3549_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3692_ = lean_ctor_get_uint8(v_a_3549_, sizeof(void*)*7 + 2);
v_cacheInferType_3693_ = lean_ctor_get_uint8(v_a_3549_, sizeof(void*)*7 + 3);
v___x_3694_ = 0;
v_config_3805_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_config_3805_, 0, v_foApprox_3666_);
lean_ctor_set_uint8(v_config_3805_, 1, v_ctxApprox_3667_);
lean_ctor_set_uint8(v_config_3805_, 2, v_quasiPatternApprox_3668_);
lean_ctor_set_uint8(v_config_3805_, 3, v_constApprox_3669_);
lean_ctor_set_uint8(v_config_3805_, 4, v_isDefEqStuckEx_3670_);
lean_ctor_set_uint8(v_config_3805_, 5, v_unificationHints_3671_);
lean_ctor_set_uint8(v_config_3805_, 6, v_proofIrrelevance_3672_);
lean_ctor_set_uint8(v_config_3805_, 7, v_assignSyntheticOpaque_3673_);
lean_ctor_set_uint8(v_config_3805_, 8, v_offsetCnstrs_3674_);
lean_ctor_set_uint8(v_config_3805_, 9, v___x_3694_);
lean_ctor_set_uint8(v_config_3805_, 10, v_etaStruct_3675_);
lean_ctor_set_uint8(v_config_3805_, 11, v_univApprox_3676_);
lean_ctor_set_uint8(v_config_3805_, 12, v_iota_3677_);
lean_ctor_set_uint8(v_config_3805_, 13, v_beta_3678_);
lean_ctor_set_uint8(v_config_3805_, 14, v_proj_3679_);
lean_ctor_set_uint8(v_config_3805_, 15, v_zeta_3680_);
lean_ctor_set_uint8(v_config_3805_, 16, v_zetaDelta_3681_);
lean_ctor_set_uint8(v_config_3805_, 17, v_zetaUnused_3682_);
lean_ctor_set_uint8(v_config_3805_, 18, v_zetaHave_3683_);
v___x_3806_ = l_Lean_Meta_Context_configKey(v_a_3549_);
v___x_3807_ = 3ULL;
v___x_3808_ = lean_uint64_shift_right(v___x_3806_, v___x_3807_);
v___x_3809_ = lean_uint64_shift_left(v___x_3808_, v___x_3807_);
v___x_3810_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7);
v_key_3811_ = lean_uint64_lor(v___x_3809_, v___x_3810_);
v___x_3812_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3812_, 0, v_config_3805_);
lean_ctor_set_uint64(v___x_3812_, sizeof(void*)*1, v_key_3811_);
lean_inc(v_canUnfold_x3f_3690_);
lean_inc(v_synthPendingDepth_3689_);
lean_inc(v_defEqCtx_x3f_3688_);
lean_inc_ref(v_localInstances_3687_);
lean_inc_ref(v_lctx_3686_);
lean_inc(v_zetaDeltaSet_3685_);
v___x_3813_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
lean_ctor_set(v___x_3813_, 1, v_zetaDeltaSet_3685_);
lean_ctor_set(v___x_3813_, 2, v_lctx_3686_);
lean_ctor_set(v___x_3813_, 3, v_localInstances_3687_);
lean_ctor_set(v___x_3813_, 4, v_defEqCtx_x3f_3688_);
lean_ctor_set(v___x_3813_, 5, v_synthPendingDepth_3689_);
lean_ctor_set(v___x_3813_, 6, v_canUnfold_x3f_3690_);
lean_ctor_set_uint8(v___x_3813_, sizeof(void*)*7, v_trackZetaDelta_3684_);
lean_ctor_set_uint8(v___x_3813_, sizeof(void*)*7 + 1, v_univApprox_3691_);
lean_ctor_set_uint8(v___x_3813_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3692_);
lean_ctor_set_uint8(v___x_3813_, sizeof(void*)*7 + 3, v_cacheInferType_3693_);
v___x_3814_ = l_Lean_Meta_whnfForall(v_a_3664_, v___x_3813_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec_ref_known(v___x_3813_, 7);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v___x_3814_, 1);
v_a_3696_ = v_a_3815_;
goto v___jp_3695_;
}
else
{
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3816_; 
v_a_3816_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3814_, 1);
v_a_3696_ = v_a_3816_;
goto v___jp_3695_;
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec_ref(v___x_3665_);
lean_dec_ref(v___x_3661_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
lean_dec(v_val_3561_);
v_a_3817_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3814_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3814_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
v___jp_3695_:
{
uint8_t v___x_3697_; 
v___x_3697_ = l_Lean_Expr_isForall(v_a_3696_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec_ref(v_a_3696_);
lean_dec_ref(v___x_3665_);
lean_dec_ref(v___x_3661_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
lean_dec(v_val_3561_);
v___x_3698_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6);
v___x_3699_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v___x_3698_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
return v___x_3699_;
}
else
{
lean_object* v___x_3700_; 
v___x_3700_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_val_3561_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3796_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3796_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3796_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
if (lean_obj_tag(v_a_3701_) == 1)
{
lean_object* v_val_3705_; uint8_t v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___f_3710_; lean_object* v___x_3711_; 
lean_del_object(v___x_3703_);
v_val_3705_ = lean_ctor_get(v_a_3701_, 0);
lean_inc(v_val_3705_);
lean_dec_ref_known(v_a_3701_, 1);
v___x_3706_ = 0;
v___x_3707_ = lean_box(v___x_3706_);
v___x_3708_ = lean_box(v___x_3662_);
v___x_3709_ = lean_box(v___x_3555_);
v___f_3710_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3710_, 0, v___x_3707_);
lean_closure_set(v___f_3710_, 1, v___x_3708_);
lean_closure_set(v___f_3710_, 2, v___x_3709_);
v___x_3711_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_motive_3568_, v___f_3710_, v___x_3662_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3713_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3711_, 1);
v___x_3713_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_3566_, v_toMatcherInfo_3565_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; uint8_t v_foApprox_3715_; uint8_t v_ctxApprox_3716_; uint8_t v_quasiPatternApprox_3717_; uint8_t v_constApprox_3718_; uint8_t v_isDefEqStuckEx_3719_; uint8_t v_unificationHints_3720_; uint8_t v_proofIrrelevance_3721_; uint8_t v_assignSyntheticOpaque_3722_; uint8_t v_offsetCnstrs_3723_; uint8_t v_etaStruct_3724_; uint8_t v_univApprox_3725_; uint8_t v_iota_3726_; uint8_t v_beta_3727_; uint8_t v_proj_3728_; uint8_t v_zeta_3729_; uint8_t v_zetaDelta_3730_; uint8_t v_zetaUnused_3731_; uint8_t v_zetaHave_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3775_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v_foApprox_3715_ = lean_ctor_get_uint8(v___x_3665_, 0);
v_ctxApprox_3716_ = lean_ctor_get_uint8(v___x_3665_, 1);
v_quasiPatternApprox_3717_ = lean_ctor_get_uint8(v___x_3665_, 2);
v_constApprox_3718_ = lean_ctor_get_uint8(v___x_3665_, 3);
v_isDefEqStuckEx_3719_ = lean_ctor_get_uint8(v___x_3665_, 4);
v_unificationHints_3720_ = lean_ctor_get_uint8(v___x_3665_, 5);
v_proofIrrelevance_3721_ = lean_ctor_get_uint8(v___x_3665_, 6);
v_assignSyntheticOpaque_3722_ = lean_ctor_get_uint8(v___x_3665_, 7);
v_offsetCnstrs_3723_ = lean_ctor_get_uint8(v___x_3665_, 8);
v_etaStruct_3724_ = lean_ctor_get_uint8(v___x_3665_, 10);
v_univApprox_3725_ = lean_ctor_get_uint8(v___x_3665_, 11);
v_iota_3726_ = lean_ctor_get_uint8(v___x_3665_, 12);
v_beta_3727_ = lean_ctor_get_uint8(v___x_3665_, 13);
v_proj_3728_ = lean_ctor_get_uint8(v___x_3665_, 14);
v_zeta_3729_ = lean_ctor_get_uint8(v___x_3665_, 15);
v_zetaDelta_3730_ = lean_ctor_get_uint8(v___x_3665_, 16);
v_zetaUnused_3731_ = lean_ctor_get_uint8(v___x_3665_, 17);
v_zetaHave_3732_ = lean_ctor_get_uint8(v___x_3665_, 18);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3734_ = v___x_3665_;
v_isShared_3735_ = v_isSharedCheck_3775_;
goto v_resetjp_3733_;
}
else
{
lean_dec(v___x_3665_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3775_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; size_t v_sz_3750_; lean_object* v_config_3752_; 
v___x_3736_ = l_Lean_Expr_bindingDomain_x21(v_a_3696_);
v___x_3737_ = l_Lean_Expr_bindingName_x21(v_a_3696_);
v___x_3738_ = l_Lean_Expr_bindingBody_x21(v_a_3696_);
lean_dec_ref(v_a_3696_);
lean_inc_ref(v___x_3736_);
v___x_3739_ = l_Lean_Expr_lam___override(v___x_3737_, v___x_3736_, v___x_3738_, v___x_3706_);
v___x_3740_ = lean_unsigned_to_nat(5u);
v___x_3741_ = lean_mk_empty_array_with_capacity(v___x_3740_);
v___x_3742_ = lean_array_push(v___x_3741_, v_val_3705_);
v___x_3743_ = lean_array_push(v___x_3742_, v___x_3736_);
v___x_3744_ = lean_array_push(v___x_3743_, v___x_3739_);
v___x_3745_ = lean_array_push(v___x_3744_, v___x_3661_);
v___x_3746_ = lean_array_push(v___x_3745_, v_a_3712_);
v___x_3747_ = l_Array_append___redArg(v_params_3567_, v___x_3746_);
lean_dec_ref(v___x_3746_);
v___x_3748_ = l_Array_append___redArg(v___x_3747_, v_discrs_3569_);
lean_dec_ref(v_discrs_3569_);
v___x_3749_ = l_Array_append___redArg(v___x_3748_, v_alts_3570_);
lean_dec_ref(v_alts_3570_);
v_sz_3750_ = lean_array_size(v___x_3749_);
if (v_isShared_3735_ == 0)
{
v_config_3752_ = v___x_3734_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 0, v_foApprox_3715_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 1, v_ctxApprox_3716_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 2, v_quasiPatternApprox_3717_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 3, v_constApprox_3718_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 4, v_isDefEqStuckEx_3719_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 5, v_unificationHints_3720_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 6, v_proofIrrelevance_3721_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 7, v_assignSyntheticOpaque_3722_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 8, v_offsetCnstrs_3723_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 10, v_etaStruct_3724_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 11, v_univApprox_3725_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 12, v_iota_3726_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 13, v_beta_3727_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 14, v_proj_3728_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 15, v_zeta_3729_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 16, v_zetaDelta_3730_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 17, v_zetaUnused_3731_);
lean_ctor_set_uint8(v_reuseFailAlloc_3774_, 18, v_zetaHave_3732_);
v_config_3752_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
uint64_t v___x_3753_; uint64_t v___x_3754_; uint64_t v___x_3755_; size_t v___x_3756_; lean_object* v___x_3757_; uint64_t v___x_3758_; uint64_t v___x_3759_; uint64_t v_key_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
lean_ctor_set_uint8(v_config_3752_, 9, v___x_3694_);
v___x_3753_ = l_Lean_Meta_Context_configKey(v_a_3549_);
v___x_3754_ = 3ULL;
v___x_3755_ = lean_uint64_shift_right(v___x_3753_, v___x_3754_);
v___x_3756_ = ((size_t)0ULL);
v___x_3757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_3750_, v___x_3756_, v___x_3749_);
v___x_3758_ = lean_uint64_shift_left(v___x_3755_, v___x_3754_);
v___x_3759_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7);
v_key_3760_ = lean_uint64_lor(v___x_3758_, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3761_, 0, v_config_3752_);
lean_ctor_set_uint64(v___x_3761_, sizeof(void*)*1, v_key_3760_);
lean_inc(v_canUnfold_x3f_3690_);
lean_inc(v_synthPendingDepth_3689_);
lean_inc(v_defEqCtx_x3f_3688_);
lean_inc_ref(v_localInstances_3687_);
lean_inc_ref(v_lctx_3686_);
lean_inc(v_zetaDeltaSet_3685_);
v___x_3762_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set(v___x_3762_, 1, v_zetaDeltaSet_3685_);
lean_ctor_set(v___x_3762_, 2, v_lctx_3686_);
lean_ctor_set(v___x_3762_, 3, v_localInstances_3687_);
lean_ctor_set(v___x_3762_, 4, v_defEqCtx_x3f_3688_);
lean_ctor_set(v___x_3762_, 5, v_synthPendingDepth_3689_);
lean_ctor_set(v___x_3762_, 6, v_canUnfold_x3f_3690_);
lean_ctor_set_uint8(v___x_3762_, sizeof(void*)*7, v_trackZetaDelta_3684_);
lean_ctor_set_uint8(v___x_3762_, sizeof(void*)*7 + 1, v_univApprox_3691_);
lean_ctor_set_uint8(v___x_3762_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3692_);
lean_ctor_set_uint8(v___x_3762_, sizeof(void*)*7 + 3, v_cacheInferType_3693_);
v___x_3763_ = l_Lean_Meta_mkAppOptM(v_a_3714_, v___x_3757_, v___x_3762_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec_ref_known(v___x_3762_, 7);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3763_, 1);
v_a_3601_ = v_a_3764_;
goto v___jp_3600_;
}
else
{
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3765_; 
v_a_3765_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3763_, 1);
v_a_3601_ = v_a_3765_;
goto v___jp_3600_;
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_dec_ref(v_remaining_3571_);
lean_del_object(v___x_3563_);
v_a_3766_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3763_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3763_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec(v_a_3712_);
lean_dec(v_val_3705_);
lean_dec_ref(v_a_3696_);
lean_dec_ref(v___x_3665_);
lean_dec_ref(v___x_3661_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_params_3567_);
lean_del_object(v___x_3563_);
v_a_3776_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3713_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3713_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec(v_val_3705_);
lean_dec_ref(v_a_3696_);
lean_dec_ref(v___x_3665_);
lean_dec_ref(v___x_3661_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
v_a_3784_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3711_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3711_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3794_; 
lean_dec(v_a_3701_);
lean_dec_ref(v_a_3696_);
lean_dec_ref(v___x_3665_);
lean_dec_ref(v___x_3661_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
v___x_3792_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3792_);
v___x_3794_ = v___x_3703_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec_ref(v_a_3696_);
lean_dec_ref(v___x_3665_);
lean_dec_ref(v___x_3661_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
v_a_3797_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3700_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3700_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_dec_ref(v___x_3661_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
lean_dec(v_val_3561_);
v_a_3825_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3663_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3663_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
else
{
lean_object* v___x_3833_; lean_object* v___x_3835_; 
lean_dec_ref(v___x_3661_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
lean_dec(v_val_3561_);
v___x_3833_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3833_);
v___x_3835_ = v___x_3559_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3833_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
v___jp_3600_:
{
lean_object* v___x_3602_; 
lean_inc(v_a_3552_);
lean_inc_ref(v_a_3551_);
lean_inc(v_a_3550_);
lean_inc_ref(v_a_3549_);
lean_inc_ref(v_a_3601_);
v___x_3602_ = lean_infer_type(v_a_3601_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3602_, 1);
v___x_3604_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_3605_ = lean_unsigned_to_nat(3u);
v___x_3606_ = l_Lean_Expr_isAppOfArity(v_a_3603_, v___x_3604_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; 
lean_dec(v_a_3603_);
lean_dec_ref(v_remaining_3571_);
lean_del_object(v___x_3563_);
lean_inc(v_a_3552_);
lean_inc_ref(v_a_3551_);
lean_inc(v_a_3550_);
lean_inc_ref(v_a_3549_);
v___x_3607_ = lean_infer_type(v_a_3601_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
v___x_3609_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2);
v___x_3610_ = l_Lean_indentExpr(v_a_3608_);
v___x_3611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v___x_3611_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
return v___x_3612_;
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
v_a_3613_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3607_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3607_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
else
{
lean_object* v___x_3621_; lean_object* v___x_3623_; 
v___x_3621_ = l_Lean_Expr_appArg_x21(v_a_3603_);
lean_dec(v_a_3603_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 0, v_a_3601_);
v___x_3623_ = v___x_3563_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3601_);
v___x_3623_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3624_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3624_, 0, v___x_3621_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
lean_ctor_set_uint8(v___x_3624_, sizeof(void*)*2, v___x_3555_);
v___x_3625_ = l_Array_toSubarray___redArg(v_remaining_3571_, v___x_3599_, v___x_3573_);
v___x_3626_ = l_Subarray_copy___redArg(v___x_3625_);
v___x_3627_ = l_Lean_Meta_Simp_Result_addExtraArgs(v___x_3624_, v___x_3626_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec_ref(v___x_3626_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3637_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3637_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3637_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v_a_3628_);
v___x_3633_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3633_);
v___x_3635_ = v___x_3630_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
v_a_3638_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3627_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3627_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
}
}
else
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
lean_dec_ref(v_a_3601_);
lean_dec_ref(v_remaining_3571_);
lean_del_object(v___x_3563_);
v_a_3647_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3602_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3602_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3839_; 
lean_dec_ref(v___x_3591_);
lean_dec_ref(v_remaining_3571_);
lean_dec_ref(v_alts_3570_);
lean_dec_ref(v_discrs_3569_);
lean_dec_ref(v_motive_3568_);
lean_dec_ref(v_params_3567_);
lean_dec(v_matcherName_3566_);
lean_dec_ref(v_toMatcherInfo_3565_);
lean_del_object(v___x_3563_);
lean_dec(v_val_3561_);
v___x_3837_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3837_);
v___x_3839_ = v___x_3559_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
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
lean_object* v___x_3842_; lean_object* v___x_3844_; 
lean_dec(v_a_3557_);
v___x_3842_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3842_);
v___x_3844_ = v___x_3559_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
v_a_3847_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3556_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3556_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed(lean_object* v_e_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(v_e_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
lean_dec(v_a_3856_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(lean_object* v_declName_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3865_, v___y_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___boxed(lean_object* v_declName_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(v_declName_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(lean_object* v_00_u03b1_3885_, lean_object* v_msg_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_3886_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___boxed(lean_object* v_00_u03b1_3896_, lean_object* v_msg_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(v_00_u03b1_3896_, v_msg_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3907_, lean_object* v_constName_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3918_, lean_object* v_constName_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(v_00_u03b1_3918_, v_constName_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b1_3929_, lean_object* v_ref_3930_, lean_object* v_constName_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3930_, v_constName_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b1_3941_, lean_object* v_ref_3942_, lean_object* v_constName_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(v_00_u03b1_3941_, v_ref_3942_, v_constName_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec(v_ref_3942_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3953_, lean_object* v_ref_3954_, lean_object* v_msg_3955_, lean_object* v_declHint_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3954_, v_msg_3955_, v_declHint_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3966_, lean_object* v_ref_3967_, lean_object* v_msg_3968_, lean_object* v_declHint_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_3966_, v_ref_3967_, v_msg_3968_, v_declHint_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec(v_ref_3967_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_3979_, lean_object* v_declHint_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3979_, v_declHint_3980_, v___y_3987_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_3990_, lean_object* v_declHint_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(v_msg_3990_, v_declHint_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(lean_object* v_00_u03b1_4001_, lean_object* v_ref_4002_, lean_object* v_msg_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_4002_, v_msg_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___boxed(lean_object* v_00_u03b1_4013_, lean_object* v_ref_4014_, lean_object* v_msg_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(v_00_u03b1_4013_, v_ref_4014_, v_msg_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec(v_ref_4014_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4070_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_));
v___x_4071_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_));
v___x_4072_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed), 9, 0);
v___x_4073_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4070_, v___x_4071_, v___x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9____boxed(lean_object* v_a_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_();
return v_res_4075_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2(void){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4085_ = lean_box(0);
v___x_4086_ = lean_unsigned_to_nat(16u);
v___x_4087_ = lean_mk_array(v___x_4086_, v___x_4085_);
return v___x_4087_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3(void){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2);
v___x_4089_ = lean_unsigned_to_nat(0u);
v___x_4090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
lean_ctor_set(v___x_4090_, 1, v___x_4088_);
return v___x_4090_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4(void){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4091_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5(void){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4092_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4);
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
return v___x_4093_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6(void){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; uint8_t v___x_4096_; lean_object* v___x_4097_; 
v___x_4094_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4095_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3);
v___x_4096_ = 1;
v___x_4097_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4097_, 0, v___x_4095_);
lean_ctor_set(v___x_4097_, 1, v___x_4094_);
lean_ctor_set_uint8(v___x_4097_, sizeof(void*)*2, v___x_4096_);
return v___x_4097_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7(void){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = lean_unsigned_to_nat(0u);
v___x_4099_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
lean_ctor_set(v___x_4100_, 1, v___x_4098_);
return v___x_4100_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8(void){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = lean_unsigned_to_nat(32u);
v___x_4102_ = lean_mk_empty_array_with_capacity(v___x_4101_);
v___x_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4102_);
return v___x_4103_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9(void){
_start:
{
size_t v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4104_ = ((size_t)5ULL);
v___x_4105_ = lean_unsigned_to_nat(0u);
v___x_4106_ = lean_unsigned_to_nat(32u);
v___x_4107_ = lean_mk_empty_array_with_capacity(v___x_4106_);
v___x_4108_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8);
v___x_4109_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
lean_ctor_set(v___x_4109_, 1, v___x_4107_);
lean_ctor_set(v___x_4109_, 2, v___x_4105_);
lean_ctor_set(v___x_4109_, 3, v___x_4105_);
lean_ctor_set_usize(v___x_4109_, 4, v___x_4104_);
return v___x_4109_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10(void){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4110_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9);
v___x_4111_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4111_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
lean_ctor_set(v___x_4112_, 2, v___x_4111_);
lean_ctor_set(v___x_4112_, 3, v___x_4110_);
return v___x_4112_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11(void){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4113_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10);
v___x_4114_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7);
v___x_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
lean_ctor_set(v___x_4115_, 1, v___x_4113_);
return v___x_4115_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13(void){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4117_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12));
v___x_4118_ = l_Lean_stringToMessageData(v___x_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object* v_declName_4119_, lean_object* v_mvarId_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_){
_start:
{
uint8_t v___x_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; uint8_t v_foApprox_4131_; uint8_t v_ctxApprox_4132_; uint8_t v_quasiPatternApprox_4133_; uint8_t v_constApprox_4134_; uint8_t v_isDefEqStuckEx_4135_; uint8_t v_unificationHints_4136_; uint8_t v_proofIrrelevance_4137_; uint8_t v_assignSyntheticOpaque_4138_; uint8_t v_offsetCnstrs_4139_; uint8_t v_etaStruct_4140_; uint8_t v_univApprox_4141_; uint8_t v_iota_4142_; uint8_t v_beta_4143_; uint8_t v_proj_4144_; uint8_t v_zeta_4145_; uint8_t v_zetaDelta_4146_; uint8_t v_zetaUnused_4147_; uint8_t v_zetaHave_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4251_; 
v___x_4126_ = 0;
v___x_4127_ = 1;
v___x_4128_ = lean_box(0);
v___x_4129_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0));
v___x_4130_ = l_Lean_Meta_Context_config(v_a_4121_);
v_foApprox_4131_ = lean_ctor_get_uint8(v___x_4130_, 0);
v_ctxApprox_4132_ = lean_ctor_get_uint8(v___x_4130_, 1);
v_quasiPatternApprox_4133_ = lean_ctor_get_uint8(v___x_4130_, 2);
v_constApprox_4134_ = lean_ctor_get_uint8(v___x_4130_, 3);
v_isDefEqStuckEx_4135_ = lean_ctor_get_uint8(v___x_4130_, 4);
v_unificationHints_4136_ = lean_ctor_get_uint8(v___x_4130_, 5);
v_proofIrrelevance_4137_ = lean_ctor_get_uint8(v___x_4130_, 6);
v_assignSyntheticOpaque_4138_ = lean_ctor_get_uint8(v___x_4130_, 7);
v_offsetCnstrs_4139_ = lean_ctor_get_uint8(v___x_4130_, 8);
v_etaStruct_4140_ = lean_ctor_get_uint8(v___x_4130_, 10);
v_univApprox_4141_ = lean_ctor_get_uint8(v___x_4130_, 11);
v_iota_4142_ = lean_ctor_get_uint8(v___x_4130_, 12);
v_beta_4143_ = lean_ctor_get_uint8(v___x_4130_, 13);
v_proj_4144_ = lean_ctor_get_uint8(v___x_4130_, 14);
v_zeta_4145_ = lean_ctor_get_uint8(v___x_4130_, 15);
v_zetaDelta_4146_ = lean_ctor_get_uint8(v___x_4130_, 16);
v_zetaUnused_4147_ = lean_ctor_get_uint8(v___x_4130_, 17);
v_zetaHave_4148_ = lean_ctor_get_uint8(v___x_4130_, 18);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4150_ = v___x_4130_;
v_isShared_4151_ = v_isSharedCheck_4251_;
goto v_resetjp_4149_;
}
else
{
lean_dec(v___x_4130_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4251_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
uint8_t v_trackZetaDelta_4152_; lean_object* v_zetaDeltaSet_4153_; lean_object* v_lctx_4154_; lean_object* v_localInstances_4155_; lean_object* v_defEqCtx_x3f_4156_; lean_object* v_synthPendingDepth_4157_; lean_object* v_canUnfold_x3f_4158_; uint8_t v_univApprox_4159_; uint8_t v_inTypeClassResolution_4160_; uint8_t v_cacheInferType_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; lean_object* v_config_4165_; 
v_trackZetaDelta_4152_ = lean_ctor_get_uint8(v_a_4121_, sizeof(void*)*7);
v_zetaDeltaSet_4153_ = lean_ctor_get(v_a_4121_, 1);
v_lctx_4154_ = lean_ctor_get(v_a_4121_, 2);
v_localInstances_4155_ = lean_ctor_get(v_a_4121_, 3);
v_defEqCtx_x3f_4156_ = lean_ctor_get(v_a_4121_, 4);
v_synthPendingDepth_4157_ = lean_ctor_get(v_a_4121_, 5);
v_canUnfold_x3f_4158_ = lean_ctor_get(v_a_4121_, 6);
v_univApprox_4159_ = lean_ctor_get_uint8(v_a_4121_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4160_ = lean_ctor_get_uint8(v_a_4121_, sizeof(void*)*7 + 2);
v_cacheInferType_4161_ = lean_ctor_get_uint8(v_a_4121_, sizeof(void*)*7 + 3);
v___x_4162_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1));
v___x_4163_ = 0;
if (v_isShared_4151_ == 0)
{
v_config_4165_ = v___x_4150_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 0, v_foApprox_4131_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 1, v_ctxApprox_4132_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 2, v_quasiPatternApprox_4133_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 3, v_constApprox_4134_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 4, v_isDefEqStuckEx_4135_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 5, v_unificationHints_4136_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 6, v_proofIrrelevance_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 7, v_assignSyntheticOpaque_4138_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 8, v_offsetCnstrs_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 10, v_etaStruct_4140_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 11, v_univApprox_4141_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 12, v_iota_4142_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 13, v_beta_4143_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 14, v_proj_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 15, v_zeta_4145_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 16, v_zetaDelta_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 17, v_zetaUnused_4147_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, 18, v_zetaHave_4148_);
v_config_4165_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
uint64_t v___x_4166_; uint64_t v___x_4167_; uint64_t v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; uint64_t v___x_4171_; uint64_t v___x_4172_; uint64_t v_key_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_ctor_set_uint8(v_config_4165_, 9, v___x_4163_);
v___x_4166_ = l_Lean_Meta_Context_configKey(v_a_4121_);
v___x_4167_ = 3ULL;
v___x_4168_ = lean_uint64_shift_right(v___x_4166_, v___x_4167_);
v___x_4169_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6);
v___x_4170_ = l_Lean_Options_empty;
v___x_4171_ = lean_uint64_shift_left(v___x_4168_, v___x_4167_);
v___x_4172_ = lean_uint64_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__7);
v_key_4173_ = lean_uint64_lor(v___x_4171_, v___x_4172_);
v___x_4174_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4174_, 0, v_config_4165_);
lean_ctor_set_uint64(v___x_4174_, sizeof(void*)*1, v_key_4173_);
lean_inc(v_canUnfold_x3f_4158_);
lean_inc(v_synthPendingDepth_4157_);
lean_inc(v_defEqCtx_x3f_4156_);
lean_inc_ref(v_localInstances_4155_);
lean_inc_ref(v_lctx_4154_);
lean_inc(v_zetaDeltaSet_4153_);
v___x_4175_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
lean_ctor_set(v___x_4175_, 1, v_zetaDeltaSet_4153_);
lean_ctor_set(v___x_4175_, 2, v_lctx_4154_);
lean_ctor_set(v___x_4175_, 3, v_localInstances_4155_);
lean_ctor_set(v___x_4175_, 4, v_defEqCtx_x3f_4156_);
lean_ctor_set(v___x_4175_, 5, v_synthPendingDepth_4157_);
lean_ctor_set(v___x_4175_, 6, v_canUnfold_x3f_4158_);
lean_ctor_set_uint8(v___x_4175_, sizeof(void*)*7, v_trackZetaDelta_4152_);
lean_ctor_set_uint8(v___x_4175_, sizeof(void*)*7 + 1, v_univApprox_4159_);
lean_ctor_set_uint8(v___x_4175_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4160_);
lean_ctor_set_uint8(v___x_4175_, sizeof(void*)*7 + 3, v_cacheInferType_4161_);
v___x_4176_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_4129_, v___x_4162_, v___x_4169_, v___x_4170_, v___x_4175_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref_known(v___x_4176_, 1);
v___x_4178_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_9_));
v___x_4179_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_4162_, v___x_4178_, v___x_4126_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
v___x_4181_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11);
v___x_4182_ = l_Lean_Meta_simpTarget(v_mvarId_4120_, v_a_4177_, v_a_4180_, v___x_4128_, v___x_4127_, v___x_4181_, v___x_4175_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4225_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4185_ = v___x_4182_;
v_isShared_4186_ = v_isSharedCheck_4225_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4182_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4225_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v_fst_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4223_; 
v_fst_4187_ = lean_ctor_get(v_a_4183_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v_a_4183_);
if (v_isSharedCheck_4223_ == 0)
{
lean_object* v_unused_4224_; 
v_unused_4224_ = lean_ctor_get(v_a_4183_, 1);
lean_dec(v_unused_4224_);
v___x_4189_ = v_a_4183_;
v_isShared_4190_ = v_isSharedCheck_4223_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_fst_4187_);
lean_dec(v_a_4183_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4223_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
if (lean_obj_tag(v_fst_4187_) == 0)
{
lean_object* v___x_4191_; lean_object* v___x_4193_; 
lean_del_object(v___x_4189_);
lean_dec_ref_known(v___x_4175_, 7);
lean_dec(v_declName_4119_);
v___x_4191_ = lean_box(0);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 0, v___x_4191_);
v___x_4193_ = v___x_4185_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
else
{
lean_object* v_val_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4199_; 
lean_del_object(v___x_4185_);
v_val_4195_ = lean_ctor_get(v_fst_4187_, 0);
lean_inc(v_val_4195_);
lean_dec_ref_known(v_fst_4187_, 1);
v___x_4196_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13);
v___x_4197_ = l_Lean_MessageData_ofConstName(v_declName_4119_, v___x_4126_);
if (v_isShared_4190_ == 0)
{
lean_ctor_set_tag(v___x_4189_, 7);
lean_ctor_set(v___x_4189_, 1, v___x_4197_);
lean_ctor_set(v___x_4189_, 0, v___x_4196_);
v___x_4199_ = v___x_4189_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4196_);
lean_ctor_set(v_reuseFailAlloc_4222_, 1, v___x_4197_);
v___x_4199_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___f_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4200_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_4201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4199_);
lean_ctor_set(v___x_4201_, 1, v___x_4200_);
v___f_4202_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4202_, 0, v___x_4201_);
v___x_4203_ = lean_box(v___x_4127_);
v___x_4204_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___boxed), 7, 2);
lean_closure_set(v___x_4204_, 0, v_val_4195_);
lean_closure_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4204_, v___f_4202_, v___x_4175_, v_a_4122_, v_a_4123_, v_a_4124_);
lean_dec_ref_known(v___x_4175_, 7);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4205_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4205_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
v_a_4214_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4205_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4205_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
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
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec_ref_known(v___x_4175_, 7);
lean_dec(v_declName_4119_);
v_a_4226_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4182_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4182_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
lean_dec(v_a_4177_);
lean_dec_ref_known(v___x_4175_, 7);
lean_dec(v_mvarId_4120_);
lean_dec(v_declName_4119_);
v_a_4234_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4179_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4179_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec_ref_known(v___x_4175_, 7);
lean_dec(v_mvarId_4120_);
lean_dec(v_declName_4119_);
v_a_4242_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4176_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4176_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___boxed(lean_object* v_declName_4252_, lean_object* v_mvarId_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4252_, v_mvarId_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_);
lean_dec(v_a_4257_);
lean_dec_ref(v_a_4256_);
lean_dec(v_a_4255_);
lean_dec_ref(v_a_4254_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(lean_object* v_e_4260_, lean_object* v_k_4261_, uint8_t v_cleanupAnnotations_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___f_4268_; uint8_t v___x_4269_; uint8_t v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___f_4268_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4268_, 0, v_k_4261_);
v___x_4269_ = 1;
v___x_4270_ = 0;
v___x_4271_ = lean_box(0);
v___x_4272_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4260_, v___x_4269_, v___x_4270_, v___x_4269_, v___x_4270_, v___x_4271_, v___f_4268_, v_cleanupAnnotations_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4272_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4272_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
v_a_4281_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4272_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4272_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg___boxed(lean_object* v_e_4289_, lean_object* v_k_4290_, lean_object* v_cleanupAnnotations_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4297_; lean_object* v_res_4298_; 
v_cleanupAnnotations_boxed_4297_ = lean_unbox(v_cleanupAnnotations_4291_);
v_res_4298_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4289_, v_k_4290_, v_cleanupAnnotations_boxed_4297_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_object* v_00_u03b1_4299_, lean_object* v_e_4300_, lean_object* v_k_4301_, uint8_t v_cleanupAnnotations_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4300_, v_k_4301_, v_cleanupAnnotations_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed(lean_object* v_00_u03b1_4309_, lean_object* v_e_4310_, lean_object* v_k_4311_, lean_object* v_cleanupAnnotations_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4318_; lean_object* v_res_4319_; 
v_cleanupAnnotations_boxed_4318_ = lean_unbox(v_cleanupAnnotations_4312_);
v_res_4319_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(v_00_u03b1_4309_, v_e_4310_, v_k_4311_, v_cleanupAnnotations_boxed_4318_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
return v_res_4319_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object* v_opts_4320_, lean_object* v_opt_4321_){
_start:
{
lean_object* v_name_4322_; lean_object* v_defValue_4323_; lean_object* v_map_4324_; lean_object* v___x_4325_; 
v_name_4322_ = lean_ctor_get(v_opt_4321_, 0);
v_defValue_4323_ = lean_ctor_get(v_opt_4321_, 1);
v_map_4324_ = lean_ctor_get(v_opts_4320_, 0);
v___x_4325_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4324_, v_name_4322_);
if (lean_obj_tag(v___x_4325_) == 0)
{
uint8_t v___x_4326_; 
v___x_4326_ = lean_unbox(v_defValue_4323_);
return v___x_4326_;
}
else
{
lean_object* v_val_4327_; 
v_val_4327_ = lean_ctor_get(v___x_4325_, 0);
lean_inc(v_val_4327_);
lean_dec_ref_known(v___x_4325_, 1);
if (lean_obj_tag(v_val_4327_) == 1)
{
uint8_t v_v_4328_; 
v_v_4328_ = lean_ctor_get_uint8(v_val_4327_, 0);
lean_dec_ref_known(v_val_4327_, 0);
return v_v_4328_;
}
else
{
uint8_t v___x_4329_; 
lean_dec(v_val_4327_);
v___x_4329_ = lean_unbox(v_defValue_4323_);
return v___x_4329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object* v_opts_4330_, lean_object* v_opt_4331_){
_start:
{
uint8_t v_res_4332_; lean_object* v_r_4333_; 
v_res_4332_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v_opts_4330_, v_opt_4331_);
lean_dec_ref(v_opt_4331_);
lean_dec_ref(v_opts_4330_);
v_r_4333_ = lean_box(v_res_4332_);
return v_r_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(lean_object* v_opts_4334_, lean_object* v_opt_4335_){
_start:
{
lean_object* v_name_4336_; lean_object* v_defValue_4337_; lean_object* v_map_4338_; lean_object* v___x_4339_; 
v_name_4336_ = lean_ctor_get(v_opt_4335_, 0);
v_defValue_4337_ = lean_ctor_get(v_opt_4335_, 1);
v_map_4338_ = lean_ctor_get(v_opts_4334_, 0);
v___x_4339_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4338_, v_name_4336_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_inc(v_defValue_4337_);
return v_defValue_4337_;
}
else
{
lean_object* v_val_4340_; 
v_val_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_val_4340_);
lean_dec_ref_known(v___x_4339_, 1);
if (lean_obj_tag(v_val_4340_) == 3)
{
lean_object* v_v_4341_; 
v_v_4341_ = lean_ctor_get(v_val_4340_, 0);
lean_inc(v_v_4341_);
lean_dec_ref_known(v_val_4340_, 1);
return v_v_4341_;
}
else
{
lean_dec(v_val_4340_);
lean_inc(v_defValue_4337_);
return v_defValue_4337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4___boxed(lean_object* v_opts_4342_, lean_object* v_opt_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_opts_4342_, v_opt_4343_);
lean_dec_ref(v_opt_4343_);
lean_dec_ref(v_opts_4342_);
return v_res_4344_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4345_; double v___x_4346_; 
v___x_4345_ = lean_unsigned_to_nat(0u);
v___x_4346_ = lean_float_of_nat(v___x_4345_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(lean_object* v_cls_4350_, lean_object* v_msg_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v_ref_4357_; lean_object* v___x_4358_; lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4403_; 
v_ref_4357_ = lean_ctor_get(v___y_4354_, 5);
v___x_4358_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4361_ = v___x_4358_;
v_isShared_4362_ = v_isSharedCheck_4403_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4358_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4403_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4363_; lean_object* v_traceState_4364_; lean_object* v_env_4365_; lean_object* v_nextMacroScope_4366_; lean_object* v_ngen_4367_; lean_object* v_auxDeclNGen_4368_; lean_object* v_cache_4369_; lean_object* v_messages_4370_; lean_object* v_infoState_4371_; lean_object* v_snapshotTasks_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4402_; 
v___x_4363_ = lean_st_ref_take(v___y_4355_);
v_traceState_4364_ = lean_ctor_get(v___x_4363_, 4);
v_env_4365_ = lean_ctor_get(v___x_4363_, 0);
v_nextMacroScope_4366_ = lean_ctor_get(v___x_4363_, 1);
v_ngen_4367_ = lean_ctor_get(v___x_4363_, 2);
v_auxDeclNGen_4368_ = lean_ctor_get(v___x_4363_, 3);
v_cache_4369_ = lean_ctor_get(v___x_4363_, 5);
v_messages_4370_ = lean_ctor_get(v___x_4363_, 6);
v_infoState_4371_ = lean_ctor_get(v___x_4363_, 7);
v_snapshotTasks_4372_ = lean_ctor_get(v___x_4363_, 8);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4374_ = v___x_4363_;
v_isShared_4375_ = v_isSharedCheck_4402_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_snapshotTasks_4372_);
lean_inc(v_infoState_4371_);
lean_inc(v_messages_4370_);
lean_inc(v_cache_4369_);
lean_inc(v_traceState_4364_);
lean_inc(v_auxDeclNGen_4368_);
lean_inc(v_ngen_4367_);
lean_inc(v_nextMacroScope_4366_);
lean_inc(v_env_4365_);
lean_dec(v___x_4363_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4402_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
uint64_t v_tid_4376_; lean_object* v_traces_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4401_; 
v_tid_4376_ = lean_ctor_get_uint64(v_traceState_4364_, sizeof(void*)*1);
v_traces_4377_ = lean_ctor_get(v_traceState_4364_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v_traceState_4364_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4379_ = v_traceState_4364_;
v_isShared_4380_ = v_isSharedCheck_4401_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_traces_4377_);
lean_dec(v_traceState_4364_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4401_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4381_; double v___x_4382_; uint8_t v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4391_; 
v___x_4381_ = lean_box(0);
v___x_4382_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0);
v___x_4383_ = 0;
v___x_4384_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__1));
v___x_4385_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4385_, 0, v_cls_4350_);
lean_ctor_set(v___x_4385_, 1, v___x_4381_);
lean_ctor_set(v___x_4385_, 2, v___x_4384_);
lean_ctor_set_float(v___x_4385_, sizeof(void*)*3, v___x_4382_);
lean_ctor_set_float(v___x_4385_, sizeof(void*)*3 + 8, v___x_4382_);
lean_ctor_set_uint8(v___x_4385_, sizeof(void*)*3 + 16, v___x_4383_);
v___x_4386_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__2));
v___x_4387_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v_a_4359_);
lean_ctor_set(v___x_4387_, 2, v___x_4386_);
lean_inc(v_ref_4357_);
v___x_4388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4388_, 0, v_ref_4357_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
v___x_4389_ = l_Lean_PersistentArray_push___redArg(v_traces_4377_, v___x_4388_);
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 0, v___x_4389_);
v___x_4391_ = v___x_4379_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4389_);
lean_ctor_set_uint64(v_reuseFailAlloc_4400_, sizeof(void*)*1, v_tid_4376_);
v___x_4391_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
lean_object* v___x_4393_; 
if (v_isShared_4375_ == 0)
{
lean_ctor_set(v___x_4374_, 4, v___x_4391_);
v___x_4393_ = v___x_4374_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_env_4365_);
lean_ctor_set(v_reuseFailAlloc_4399_, 1, v_nextMacroScope_4366_);
lean_ctor_set(v_reuseFailAlloc_4399_, 2, v_ngen_4367_);
lean_ctor_set(v_reuseFailAlloc_4399_, 3, v_auxDeclNGen_4368_);
lean_ctor_set(v_reuseFailAlloc_4399_, 4, v___x_4391_);
lean_ctor_set(v_reuseFailAlloc_4399_, 5, v_cache_4369_);
lean_ctor_set(v_reuseFailAlloc_4399_, 6, v_messages_4370_);
lean_ctor_set(v_reuseFailAlloc_4399_, 7, v_infoState_4371_);
lean_ctor_set(v_reuseFailAlloc_4399_, 8, v_snapshotTasks_4372_);
v___x_4393_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4397_; 
v___x_4394_ = lean_st_ref_set(v___y_4355_, v___x_4393_);
v___x_4395_ = lean_box(0);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 0, v___x_4395_);
v___x_4397_ = v___x_4361_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4395_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___boxed(lean_object* v_cls_4404_, lean_object* v_msg_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v_cls_4404_, v_msg_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
return v_res_4411_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4421_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4422_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4423_ = l_Lean_Name_append(v___x_4422_, v___x_4421_);
return v___x_4423_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__6));
v___x_4426_ = l_Lean_stringToMessageData(v___x_4425_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object* v_levelParams_4427_, lean_object* v_declName_4428_, lean_object* v_wfPreprocessProof_4429_, lean_object* v___x_4430_, lean_object* v_unaryPreDefName_4431_, lean_object* v_xs_4432_, lean_object* v_body_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4442_ = lean_box(0);
lean_inc(v_levelParams_4427_);
v___x_4443_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4427_, v___x_4442_);
lean_inc(v_declName_4428_);
v___x_4444_ = l_Lean_mkConst(v_declName_4428_, v___x_4443_);
v___x_4445_ = l_Lean_mkAppN(v___x_4444_, v_xs_4432_);
v___x_4446_ = l_Lean_Meta_mkEq(v___x_4445_, v_body_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc_n(v_a_4447_, 2);
lean_dec_ref_known(v___x_4446_, 1);
v___x_4448_ = lean_box(0);
v___x_4449_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4447_, v___x_4448_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_a_4450_; lean_object* v___x_4451_; 
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
lean_dec_ref_known(v___x_4449_, 1);
v___x_4451_ = l_Lean_Meta_Simp_Result_addExtraArgs(v_wfPreprocessProof_4429_, v_xs_4432_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; uint8_t v___x_4455_; lean_object* v_mvarId_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
lean_dec_ref_known(v___x_4451_, 1);
v___x_4453_ = l_Lean_Expr_appFn_x21(v_a_4447_);
v___x_4454_ = lean_box(0);
v___x_4455_ = 1;
v___x_4529_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4529_, 0, v___x_4453_);
lean_ctor_set(v___x_4529_, 1, v___x_4454_);
lean_ctor_set_uint8(v___x_4529_, sizeof(void*)*2, v___x_4455_);
v___x_4530_ = l_Lean_Meta_Simp_mkCongr(v___x_4529_, v_a_4452_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v_a_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
lean_inc(v_a_4531_);
lean_dec_ref_known(v___x_4530_, 1);
v___x_4532_ = l_Lean_Expr_mvarId_x21(v_a_4450_);
v___x_4533_ = l_Lean_Meta_applySimpResultToTarget(v___x_4532_, v_a_4447_, v_a_4531_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; uint8_t v___x_4535_; uint8_t v___x_4536_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
lean_inc(v_a_4534_);
lean_dec_ref_known(v___x_4533_, 1);
v___x_4535_ = lean_name_eq(v_declName_4428_, v_unaryPreDefName_4431_);
v___x_4536_ = lean_bool_not(v___x_4535_);
if (v___x_4536_ == 0)
{
v_mvarId_4457_ = v_a_4534_;
v___y_4458_ = v___y_4434_;
v___y_4459_ = v___y_4435_;
v___y_4460_ = v___y_4436_;
v___y_4461_ = v___y_4437_;
goto v___jp_4456_;
}
else
{
lean_object* v___x_4537_; 
v___x_4537_ = l_Lean_Elab_Eqns_deltaLHS(v_a_4534_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
lean_dec_ref_known(v___x_4537_, 1);
v_mvarId_4457_ = v_a_4538_;
v___y_4458_ = v___y_4434_;
v___y_4459_ = v___y_4435_;
v___y_4460_ = v___y_4436_;
v___y_4461_ = v___y_4437_;
goto v___jp_4456_;
}
else
{
lean_object* v_a_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4546_; 
lean_dec(v_a_4450_);
lean_dec(v_a_4447_);
lean_dec(v___x_4430_);
lean_dec(v_declName_4428_);
lean_dec(v_levelParams_4427_);
v_a_4539_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4541_ = v___x_4537_;
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_a_4539_);
lean_dec(v___x_4537_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4542_ == 0)
{
v___x_4544_ = v___x_4541_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
}
else
{
lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4554_; 
lean_dec(v_a_4450_);
lean_dec(v_a_4447_);
lean_dec(v___x_4430_);
lean_dec(v_declName_4428_);
lean_dec(v_levelParams_4427_);
v_a_4547_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4549_ = v___x_4533_;
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_dec(v___x_4533_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4552_; 
if (v_isShared_4550_ == 0)
{
v___x_4552_ = v___x_4549_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4547_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_a_4450_);
lean_dec(v_a_4447_);
lean_dec(v___x_4430_);
lean_dec(v_declName_4428_);
lean_dec(v_levelParams_4427_);
v_a_4555_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4530_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4530_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
v___jp_4456_:
{
lean_object* v___x_4462_; 
v___x_4462_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4462_) == 0)
{
lean_object* v_a_4463_; lean_object* v___x_4464_; 
v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
lean_inc(v_a_4463_);
lean_dec_ref_known(v___x_4462_, 1);
v___x_4464_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4428_, v_a_4463_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_object* v___x_4465_; lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4520_; 
lean_dec_ref_known(v___x_4464_, 1);
v___x_4465_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4450_, v___y_4459_);
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4468_ = v___x_4465_;
v_isShared_4469_ = v_isSharedCheck_4520_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4465_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4520_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
uint8_t v___x_4470_; uint8_t v___x_4471_; lean_object* v___x_4472_; 
v___x_4470_ = 0;
v___x_4471_ = 1;
v___x_4472_ = l_Lean_Meta_mkForallFVars(v_xs_4432_, v_a_4447_, v___x_4470_, v___x_4455_, v___x_4455_, v___x_4471_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; lean_object* v___x_4474_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4473_);
lean_dec_ref_known(v___x_4472_, 1);
v___x_4474_ = l_Lean_Meta_letToHave(v_a_4473_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; lean_object* v___x_4476_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
lean_dec_ref_known(v___x_4474_, 1);
v___x_4476_ = l_Lean_Meta_mkLambdaFVars(v_xs_4432_, v_a_4466_, v___x_4470_, v___x_4455_, v___x_4470_, v___x_4455_, v___x_4471_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4482_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref_known(v___x_4476_, 1);
lean_inc_n(v___x_4430_, 2);
v___x_4478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4430_);
lean_ctor_set(v___x_4478_, 1, v_levelParams_4427_);
lean_ctor_set(v___x_4478_, 2, v_a_4475_);
v___x_4479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4430_);
lean_ctor_set(v___x_4479_, 1, v___x_4442_);
v___x_4480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4478_);
lean_ctor_set(v___x_4480_, 1, v_a_4477_);
lean_ctor_set(v___x_4480_, 2, v___x_4479_);
if (v_isShared_4469_ == 0)
{
lean_ctor_set_tag(v___x_4468_, 2);
lean_ctor_set(v___x_4468_, 0, v___x_4480_);
v___x_4482_ = v___x_4468_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4480_);
v___x_4482_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Lean_addDecl(v___x_4482_, v___x_4470_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v___x_4484_; 
lean_dec_ref_known(v___x_4483_, 1);
lean_inc(v___x_4430_);
v___x_4484_ = l_Lean_inferDefEqAttr(v___x_4430_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_options_4485_; uint8_t v_hasTrace_4486_; 
lean_dec_ref_known(v___x_4484_, 1);
v_options_4485_ = lean_ctor_get(v___y_4460_, 2);
v_hasTrace_4486_ = lean_ctor_get_uint8(v_options_4485_, sizeof(void*)*1);
if (v_hasTrace_4486_ == 0)
{
lean_dec(v___x_4430_);
goto v___jp_4439_;
}
else
{
lean_object* v_inheritedTraceOptions_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; uint8_t v___x_4490_; 
v_inheritedTraceOptions_4487_ = lean_ctor_get(v___y_4460_, 13);
v___x_4488_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4489_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_4490_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4487_, v_options_4485_, v___x_4489_);
if (v___x_4490_ == 0)
{
lean_dec(v___x_4430_);
goto v___jp_4439_;
}
else
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4491_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7);
v___x_4492_ = l_Lean_MessageData_ofConstName(v___x_4430_, v___x_4470_);
v___x_4493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4491_);
lean_ctor_set(v___x_4493_, 1, v___x_4492_);
v___x_4494_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_4488_, v___x_4493_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
return v___x_4494_;
}
}
}
else
{
lean_dec(v___x_4430_);
return v___x_4484_;
}
}
else
{
lean_dec(v___x_4430_);
return v___x_4483_;
}
}
}
else
{
lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4503_; 
lean_dec(v_a_4475_);
lean_del_object(v___x_4468_);
lean_dec(v___x_4430_);
lean_dec(v_levelParams_4427_);
v_a_4496_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4498_ = v___x_4476_;
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_dec(v___x_4476_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4496_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_del_object(v___x_4468_);
lean_dec(v_a_4466_);
lean_dec(v___x_4430_);
lean_dec(v_levelParams_4427_);
v_a_4504_ = lean_ctor_get(v___x_4474_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4474_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4474_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
lean_del_object(v___x_4468_);
lean_dec(v_a_4466_);
lean_dec(v___x_4430_);
lean_dec(v_levelParams_4427_);
v_a_4512_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4472_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4472_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
}
else
{
lean_dec(v_a_4450_);
lean_dec(v_a_4447_);
lean_dec(v___x_4430_);
lean_dec(v_levelParams_4427_);
return v___x_4464_;
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
lean_dec(v_a_4450_);
lean_dec(v_a_4447_);
lean_dec(v___x_4430_);
lean_dec(v_declName_4428_);
lean_dec(v_levelParams_4427_);
v_a_4521_ = lean_ctor_get(v___x_4462_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4462_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4462_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4462_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_a_4450_);
lean_dec(v_a_4447_);
lean_dec(v___x_4430_);
lean_dec(v_declName_4428_);
lean_dec(v_levelParams_4427_);
v_a_4563_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4451_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4451_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec(v_a_4447_);
lean_dec(v___x_4430_);
lean_dec_ref(v_wfPreprocessProof_4429_);
lean_dec(v_declName_4428_);
lean_dec(v_levelParams_4427_);
v_a_4571_ = lean_ctor_get(v___x_4449_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4449_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4449_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4449_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec(v___x_4430_);
lean_dec_ref(v_wfPreprocessProof_4429_);
lean_dec(v_declName_4428_);
lean_dec(v_levelParams_4427_);
v_a_4579_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4446_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4446_);
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
v___jp_4439_:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4440_ = lean_box(0);
v___x_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
return v___x_4441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object* v_levelParams_4587_, lean_object* v_declName_4588_, lean_object* v_wfPreprocessProof_4589_, lean_object* v___x_4590_, lean_object* v_unaryPreDefName_4591_, lean_object* v_xs_4592_, lean_object* v_body_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_Lean_Elab_WF_mkUnfoldEq___lam__0(v_levelParams_4587_, v_declName_4588_, v_wfPreprocessProof_4589_, v___x_4590_, v_unaryPreDefName_4591_, v_xs_4592_, v_body_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec_ref(v_xs_4592_);
lean_dec(v_unaryPreDefName_4591_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(lean_object* v___y_4600_, uint8_t v_isExporting_4601_, lean_object* v___x_4602_, lean_object* v___y_4603_, lean_object* v___x_4604_, lean_object* v_a_x3f_4605_){
_start:
{
lean_object* v___x_4607_; lean_object* v_env_4608_; lean_object* v_nextMacroScope_4609_; lean_object* v_ngen_4610_; lean_object* v_auxDeclNGen_4611_; lean_object* v_traceState_4612_; lean_object* v_messages_4613_; lean_object* v_infoState_4614_; lean_object* v_snapshotTasks_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4640_; 
v___x_4607_ = lean_st_ref_take(v___y_4600_);
v_env_4608_ = lean_ctor_get(v___x_4607_, 0);
v_nextMacroScope_4609_ = lean_ctor_get(v___x_4607_, 1);
v_ngen_4610_ = lean_ctor_get(v___x_4607_, 2);
v_auxDeclNGen_4611_ = lean_ctor_get(v___x_4607_, 3);
v_traceState_4612_ = lean_ctor_get(v___x_4607_, 4);
v_messages_4613_ = lean_ctor_get(v___x_4607_, 6);
v_infoState_4614_ = lean_ctor_get(v___x_4607_, 7);
v_snapshotTasks_4615_ = lean_ctor_get(v___x_4607_, 8);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4640_ == 0)
{
lean_object* v_unused_4641_; 
v_unused_4641_ = lean_ctor_get(v___x_4607_, 5);
lean_dec(v_unused_4641_);
v___x_4617_ = v___x_4607_;
v_isShared_4618_ = v_isSharedCheck_4640_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_snapshotTasks_4615_);
lean_inc(v_infoState_4614_);
lean_inc(v_messages_4613_);
lean_inc(v_traceState_4612_);
lean_inc(v_auxDeclNGen_4611_);
lean_inc(v_ngen_4610_);
lean_inc(v_nextMacroScope_4609_);
lean_inc(v_env_4608_);
lean_dec(v___x_4607_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4640_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; lean_object* v___x_4621_; 
v___x_4619_ = l_Lean_Environment_setExporting(v_env_4608_, v_isExporting_4601_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 5, v___x_4602_);
lean_ctor_set(v___x_4617_, 0, v___x_4619_);
v___x_4621_ = v___x_4617_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4619_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_nextMacroScope_4609_);
lean_ctor_set(v_reuseFailAlloc_4639_, 2, v_ngen_4610_);
lean_ctor_set(v_reuseFailAlloc_4639_, 3, v_auxDeclNGen_4611_);
lean_ctor_set(v_reuseFailAlloc_4639_, 4, v_traceState_4612_);
lean_ctor_set(v_reuseFailAlloc_4639_, 5, v___x_4602_);
lean_ctor_set(v_reuseFailAlloc_4639_, 6, v_messages_4613_);
lean_ctor_set(v_reuseFailAlloc_4639_, 7, v_infoState_4614_);
lean_ctor_set(v_reuseFailAlloc_4639_, 8, v_snapshotTasks_4615_);
v___x_4621_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v_mctx_4624_; lean_object* v_zetaDeltaFVarIds_4625_; lean_object* v_postponed_4626_; lean_object* v_diag_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4637_; 
v___x_4622_ = lean_st_ref_set(v___y_4600_, v___x_4621_);
v___x_4623_ = lean_st_ref_take(v___y_4603_);
v_mctx_4624_ = lean_ctor_get(v___x_4623_, 0);
v_zetaDeltaFVarIds_4625_ = lean_ctor_get(v___x_4623_, 2);
v_postponed_4626_ = lean_ctor_get(v___x_4623_, 3);
v_diag_4627_ = lean_ctor_get(v___x_4623_, 4);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4637_ == 0)
{
lean_object* v_unused_4638_; 
v_unused_4638_ = lean_ctor_get(v___x_4623_, 1);
lean_dec(v_unused_4638_);
v___x_4629_ = v___x_4623_;
v_isShared_4630_ = v_isSharedCheck_4637_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_diag_4627_);
lean_inc(v_postponed_4626_);
lean_inc(v_zetaDeltaFVarIds_4625_);
lean_inc(v_mctx_4624_);
lean_dec(v___x_4623_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4637_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 1, v___x_4604_);
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_mctx_4624_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v___x_4604_);
lean_ctor_set(v_reuseFailAlloc_4636_, 2, v_zetaDeltaFVarIds_4625_);
lean_ctor_set(v_reuseFailAlloc_4636_, 3, v_postponed_4626_);
lean_ctor_set(v_reuseFailAlloc_4636_, 4, v_diag_4627_);
v___x_4632_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4633_ = lean_st_ref_set(v___y_4603_, v___x_4632_);
v___x_4634_ = lean_box(0);
v___x_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
return v___x_4635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v___y_4642_, lean_object* v_isExporting_4643_, lean_object* v___x_4644_, lean_object* v___y_4645_, lean_object* v___x_4646_, lean_object* v_a_x3f_4647_, lean_object* v___y_4648_){
_start:
{
uint8_t v_isExporting_boxed_4649_; lean_object* v_res_4650_; 
v_isExporting_boxed_4649_ = lean_unbox(v_isExporting_4643_);
v_res_4650_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4642_, v_isExporting_boxed_4649_, v___x_4644_, v___y_4645_, v___x_4646_, v_a_x3f_4647_);
lean_dec(v_a_x3f_4647_);
lean_dec(v___y_4645_);
lean_dec(v___y_4642_);
return v_res_4650_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4651_; 
v___x_4651_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4651_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4652_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__0);
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
return v___x_4653_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; 
v___x_4654_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1);
v___x_4655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4654_);
lean_ctor_set(v___x_4655_, 1, v___x_4654_);
return v___x_4655_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__1);
v___x_4657_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
lean_ctor_set(v___x_4657_, 1, v___x_4656_);
lean_ctor_set(v___x_4657_, 2, v___x_4656_);
lean_ctor_set(v___x_4657_, 3, v___x_4656_);
lean_ctor_set(v___x_4657_, 4, v___x_4656_);
lean_ctor_set(v___x_4657_, 5, v___x_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(lean_object* v_x_4658_, uint8_t v_isExporting_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v___x_4665_; lean_object* v_env_4666_; uint8_t v_isExporting_4667_; uint8_t v___y_4734_; lean_object* v___x_4736_; uint8_t v_isModule_4737_; uint8_t v___x_4738_; 
v___x_4665_ = lean_st_ref_get(v___y_4663_);
v_env_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc_ref(v_env_4666_);
lean_dec(v___x_4665_);
v_isExporting_4667_ = lean_ctor_get_uint8(v_env_4666_, sizeof(void*)*8);
v___x_4736_ = l_Lean_Environment_header(v_env_4666_);
lean_dec_ref(v_env_4666_);
v_isModule_4737_ = lean_ctor_get_uint8(v___x_4736_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4736_);
v___x_4738_ = lean_bool_not(v_isModule_4737_);
if (v___x_4738_ == 0)
{
if (v_isExporting_4667_ == 0)
{
if (v_isExporting_4659_ == 0)
{
lean_object* v___x_4739_; 
lean_inc(v___y_4663_);
lean_inc_ref(v___y_4662_);
lean_inc(v___y_4661_);
lean_inc_ref(v___y_4660_);
v___x_4739_ = lean_apply_5(v_x_4658_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, lean_box(0));
return v___x_4739_;
}
else
{
goto v___jp_4668_;
}
}
else
{
v___y_4734_ = v_isExporting_4659_;
goto v___jp_4733_;
}
}
else
{
v___y_4734_ = v___x_4738_;
goto v___jp_4733_;
}
v___jp_4668_:
{
lean_object* v___x_4669_; lean_object* v_env_4670_; lean_object* v_nextMacroScope_4671_; lean_object* v_ngen_4672_; lean_object* v_auxDeclNGen_4673_; lean_object* v_traceState_4674_; lean_object* v_messages_4675_; lean_object* v_infoState_4676_; lean_object* v_snapshotTasks_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4731_; 
v___x_4669_ = lean_st_ref_take(v___y_4663_);
v_env_4670_ = lean_ctor_get(v___x_4669_, 0);
v_nextMacroScope_4671_ = lean_ctor_get(v___x_4669_, 1);
v_ngen_4672_ = lean_ctor_get(v___x_4669_, 2);
v_auxDeclNGen_4673_ = lean_ctor_get(v___x_4669_, 3);
v_traceState_4674_ = lean_ctor_get(v___x_4669_, 4);
v_messages_4675_ = lean_ctor_get(v___x_4669_, 6);
v_infoState_4676_ = lean_ctor_get(v___x_4669_, 7);
v_snapshotTasks_4677_ = lean_ctor_get(v___x_4669_, 8);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4669_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; 
v_unused_4732_ = lean_ctor_get(v___x_4669_, 5);
lean_dec(v_unused_4732_);
v___x_4679_ = v___x_4669_;
v_isShared_4680_ = v_isSharedCheck_4731_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_snapshotTasks_4677_);
lean_inc(v_infoState_4676_);
lean_inc(v_messages_4675_);
lean_inc(v_traceState_4674_);
lean_inc(v_auxDeclNGen_4673_);
lean_inc(v_ngen_4672_);
lean_inc(v_nextMacroScope_4671_);
lean_inc(v_env_4670_);
lean_dec(v___x_4669_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4731_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4684_; 
v___x_4681_ = l_Lean_Environment_setExporting(v_env_4670_, v_isExporting_4659_);
v___x_4682_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 5, v___x_4682_);
lean_ctor_set(v___x_4679_, 0, v___x_4681_);
v___x_4684_ = v___x_4679_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4681_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_nextMacroScope_4671_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_ngen_4672_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_auxDeclNGen_4673_);
lean_ctor_set(v_reuseFailAlloc_4730_, 4, v_traceState_4674_);
lean_ctor_set(v_reuseFailAlloc_4730_, 5, v___x_4682_);
lean_ctor_set(v_reuseFailAlloc_4730_, 6, v_messages_4675_);
lean_ctor_set(v_reuseFailAlloc_4730_, 7, v_infoState_4676_);
lean_ctor_set(v_reuseFailAlloc_4730_, 8, v_snapshotTasks_4677_);
v___x_4684_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v_mctx_4687_; lean_object* v_zetaDeltaFVarIds_4688_; lean_object* v_postponed_4689_; lean_object* v_diag_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4728_; 
v___x_4685_ = lean_st_ref_set(v___y_4663_, v___x_4684_);
v___x_4686_ = lean_st_ref_take(v___y_4661_);
v_mctx_4687_ = lean_ctor_get(v___x_4686_, 0);
v_zetaDeltaFVarIds_4688_ = lean_ctor_get(v___x_4686_, 2);
v_postponed_4689_ = lean_ctor_get(v___x_4686_, 3);
v_diag_4690_ = lean_ctor_get(v___x_4686_, 4);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4728_ == 0)
{
lean_object* v_unused_4729_; 
v_unused_4729_ = lean_ctor_get(v___x_4686_, 1);
lean_dec(v_unused_4729_);
v___x_4692_ = v___x_4686_;
v_isShared_4693_ = v_isSharedCheck_4728_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_diag_4690_);
lean_inc(v_postponed_4689_);
lean_inc(v_zetaDeltaFVarIds_4688_);
lean_inc(v_mctx_4687_);
lean_dec(v___x_4686_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4728_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4694_; lean_object* v___x_4696_; 
v___x_4694_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__3);
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 1, v___x_4694_);
v___x_4696_ = v___x_4692_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_mctx_4687_);
lean_ctor_set(v_reuseFailAlloc_4727_, 1, v___x_4694_);
lean_ctor_set(v_reuseFailAlloc_4727_, 2, v_zetaDeltaFVarIds_4688_);
lean_ctor_set(v_reuseFailAlloc_4727_, 3, v_postponed_4689_);
lean_ctor_set(v_reuseFailAlloc_4727_, 4, v_diag_4690_);
v___x_4696_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
lean_object* v___x_4697_; lean_object* v_r_4698_; 
v___x_4697_ = lean_st_ref_set(v___y_4661_, v___x_4696_);
lean_inc(v___y_4663_);
lean_inc_ref(v___y_4662_);
lean_inc(v___y_4661_);
lean_inc_ref(v___y_4660_);
v_r_4698_ = lean_apply_5(v_x_4658_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, lean_box(0));
if (lean_obj_tag(v_r_4698_) == 0)
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4715_; 
v_a_4699_ = lean_ctor_get(v_r_4698_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_r_4698_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4701_ = v_r_4698_;
v_isShared_4702_ = v_isSharedCheck_4715_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v_r_4698_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4715_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4704_; 
lean_inc(v_a_4699_);
if (v_isShared_4702_ == 0)
{
lean_ctor_set_tag(v___x_4701_, 1);
v___x_4704_ = v___x_4701_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4699_);
v___x_4704_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
lean_object* v___x_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
v___x_4705_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4663_, v_isExporting_4667_, v___x_4682_, v___y_4661_, v___x_4694_, v___x_4704_);
lean_dec_ref(v___x_4704_);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4712_ == 0)
{
lean_object* v_unused_4713_; 
v_unused_4713_ = lean_ctor_get(v___x_4705_, 0);
lean_dec(v_unused_4713_);
v___x_4707_ = v___x_4705_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_dec(v___x_4705_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 0, v_a_4699_);
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4699_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
}
}
else
{
lean_object* v_a_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
v_a_4716_ = lean_ctor_get(v_r_4698_, 0);
lean_inc(v_a_4716_);
lean_dec_ref_known(v_r_4698_, 1);
v___x_4717_ = lean_box(0);
v___x_4718_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___lam__0(v___y_4663_, v_isExporting_4667_, v___x_4682_, v___y_4661_, v___x_4694_, v___x_4717_);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4725_ == 0)
{
lean_object* v_unused_4726_; 
v_unused_4726_ = lean_ctor_get(v___x_4718_, 0);
lean_dec(v_unused_4726_);
v___x_4720_ = v___x_4718_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_dec(v___x_4718_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
lean_ctor_set_tag(v___x_4720_, 1);
lean_ctor_set(v___x_4720_, 0, v_a_4716_);
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4716_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
}
}
}
}
v___jp_4733_:
{
if (v___y_4734_ == 0)
{
goto v___jp_4668_;
}
else
{
lean_object* v___x_4735_; 
lean_inc(v___y_4663_);
lean_inc_ref(v___y_4662_);
lean_inc(v___y_4661_);
lean_inc_ref(v___y_4660_);
v___x_4735_ = lean_apply_5(v_x_4658_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, lean_box(0));
return v___x_4735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___boxed(lean_object* v_x_4740_, lean_object* v_isExporting_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
uint8_t v_isExporting_boxed_4747_; lean_object* v_res_4748_; 
v_isExporting_boxed_4747_ = lean_unbox(v_isExporting_4741_);
v_res_4748_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4740_, v_isExporting_boxed_4747_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(lean_object* v_x_4749_, uint8_t v_when_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_){
_start:
{
if (v_when_4750_ == 0)
{
lean_object* v___x_4756_; 
lean_inc(v___y_4754_);
lean_inc_ref(v___y_4753_);
lean_inc(v___y_4752_);
lean_inc_ref(v___y_4751_);
v___x_4756_ = lean_apply_5(v_x_4749_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, lean_box(0));
return v___x_4756_;
}
else
{
uint8_t v___x_4757_; lean_object* v___x_4758_; 
v___x_4757_ = 0;
v___x_4758_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4749_, v___x_4757_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
return v___x_4758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg___boxed(lean_object* v_x_4759_, lean_object* v_when_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
uint8_t v_when_boxed_4766_; lean_object* v_res_4767_; 
v_when_boxed_4766_ = lean_unbox(v_when_4760_);
v_res_4767_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v_x_4759_, v_when_boxed_4766_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(lean_object* v_o_4768_, lean_object* v_k_4769_, uint8_t v_v_4770_){
_start:
{
lean_object* v_map_4771_; uint8_t v_hasTrace_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4786_; 
v_map_4771_ = lean_ctor_get(v_o_4768_, 0);
v_hasTrace_4772_ = lean_ctor_get_uint8(v_o_4768_, sizeof(void*)*1);
v_isSharedCheck_4786_ = !lean_is_exclusive(v_o_4768_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4774_ = v_o_4768_;
v_isShared_4775_ = v_isSharedCheck_4786_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_map_4771_);
lean_dec(v_o_4768_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4786_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4776_, 0, v_v_4770_);
lean_inc(v_k_4769_);
v___x_4777_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4769_, v___x_4776_, v_map_4771_);
if (v_hasTrace_4772_ == 0)
{
lean_object* v___x_4778_; uint8_t v___x_4779_; lean_object* v___x_4781_; 
v___x_4778_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4779_ = l_Lean_Name_isPrefixOf(v___x_4778_, v_k_4769_);
lean_dec(v_k_4769_);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 0, v___x_4777_);
v___x_4781_ = v___x_4774_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4777_);
v___x_4781_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_ctor_set_uint8(v___x_4781_, sizeof(void*)*1, v___x_4779_);
return v___x_4781_;
}
}
else
{
lean_object* v___x_4784_; 
lean_dec(v_k_4769_);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 0, v___x_4777_);
v___x_4784_ = v___x_4774_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4777_);
lean_ctor_set_uint8(v_reuseFailAlloc_4785_, sizeof(void*)*1, v_hasTrace_4772_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2___boxed(lean_object* v_o_4787_, lean_object* v_k_4788_, lean_object* v_v_4789_){
_start:
{
uint8_t v_v_boxed_4790_; lean_object* v_res_4791_; 
v_v_boxed_4790_ = lean_unbox(v_v_4789_);
v_res_4791_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(v_o_4787_, v_k_4788_, v_v_boxed_4790_);
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(lean_object* v_opts_4792_, lean_object* v_opt_4793_, uint8_t v_val_4794_){
_start:
{
lean_object* v_name_4795_; lean_object* v___x_4796_; 
v_name_4795_ = lean_ctor_get(v_opt_4793_, 0);
lean_inc(v_name_4795_);
lean_dec_ref(v_opt_4793_);
v___x_4796_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2_spec__2(v_opts_4792_, v_name_4795_, v_val_4794_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed(lean_object* v_opts_4797_, lean_object* v_opt_4798_, lean_object* v_val_4799_){
_start:
{
uint8_t v_val_boxed_4800_; lean_object* v_res_4801_; 
v_val_boxed_4800_ = lean_unbox(v_val_4799_);
v_res_4801_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_opts_4797_, v_opt_4798_, v_val_boxed_4800_);
return v_res_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t v___x_4802_, lean_object* v___x_4803_, uint8_t v___x_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
lean_object* v___x_4810_; lean_object* v_fileName_4811_; lean_object* v_fileMap_4812_; lean_object* v_options_4813_; lean_object* v_currRecDepth_4814_; lean_object* v_ref_4815_; lean_object* v_currNamespace_4816_; lean_object* v_openDecls_4817_; lean_object* v_initHeartbeats_4818_; lean_object* v_maxHeartbeats_4819_; lean_object* v_quotContext_4820_; lean_object* v_currMacroScope_4821_; lean_object* v_cancelTk_x3f_4822_; uint8_t v_suppressElabErrors_4823_; lean_object* v_inheritedTraceOptions_4824_; lean_object* v_env_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; uint8_t v___x_4829_; lean_object* v_fileName_4831_; lean_object* v_fileMap_4832_; lean_object* v_currRecDepth_4833_; lean_object* v_ref_4834_; lean_object* v_currNamespace_4835_; lean_object* v_openDecls_4836_; lean_object* v_initHeartbeats_4837_; lean_object* v_maxHeartbeats_4838_; lean_object* v_quotContext_4839_; lean_object* v_currMacroScope_4840_; lean_object* v_cancelTk_x3f_4841_; uint8_t v_suppressElabErrors_4842_; lean_object* v_inheritedTraceOptions_4843_; lean_object* v___y_4844_; uint8_t v___y_4850_; uint8_t v___x_4872_; 
v___x_4810_ = lean_st_ref_get(v___y_4808_);
v_fileName_4811_ = lean_ctor_get(v___y_4807_, 0);
v_fileMap_4812_ = lean_ctor_get(v___y_4807_, 1);
v_options_4813_ = lean_ctor_get(v___y_4807_, 2);
v_currRecDepth_4814_ = lean_ctor_get(v___y_4807_, 3);
v_ref_4815_ = lean_ctor_get(v___y_4807_, 5);
v_currNamespace_4816_ = lean_ctor_get(v___y_4807_, 6);
v_openDecls_4817_ = lean_ctor_get(v___y_4807_, 7);
v_initHeartbeats_4818_ = lean_ctor_get(v___y_4807_, 8);
v_maxHeartbeats_4819_ = lean_ctor_get(v___y_4807_, 9);
v_quotContext_4820_ = lean_ctor_get(v___y_4807_, 10);
v_currMacroScope_4821_ = lean_ctor_get(v___y_4807_, 11);
v_cancelTk_x3f_4822_ = lean_ctor_get(v___y_4807_, 12);
v_suppressElabErrors_4823_ = lean_ctor_get_uint8(v___y_4807_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4824_ = lean_ctor_get(v___y_4807_, 13);
v_env_4825_ = lean_ctor_get(v___x_4810_, 0);
lean_inc_ref(v_env_4825_);
lean_dec(v___x_4810_);
v___x_4826_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_4813_);
v___x_4827_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_options_4813_, v___x_4826_, v___x_4802_);
v___x_4828_ = l_Lean_diagnostics;
v___x_4829_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v___x_4827_, v___x_4828_);
v___x_4872_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4825_);
lean_dec_ref(v_env_4825_);
if (v___x_4872_ == 0)
{
if (v___x_4829_ == 0)
{
uint8_t v___x_4873_; 
v___x_4873_ = 1;
v___y_4850_ = v___x_4873_;
goto v___jp_4849_;
}
else
{
v___y_4850_ = v___x_4872_;
goto v___jp_4849_;
}
}
else
{
v___y_4850_ = v___x_4829_;
goto v___jp_4849_;
}
v___jp_4830_:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4845_ = l_Lean_maxRecDepth;
v___x_4846_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v___x_4827_, v___x_4845_);
lean_inc_ref(v_inheritedTraceOptions_4843_);
lean_inc(v_cancelTk_x3f_4841_);
lean_inc(v_currMacroScope_4840_);
lean_inc(v_quotContext_4839_);
lean_inc(v_maxHeartbeats_4838_);
lean_inc(v_initHeartbeats_4837_);
lean_inc(v_openDecls_4836_);
lean_inc(v_currNamespace_4835_);
lean_inc(v_ref_4834_);
lean_inc(v_currRecDepth_4833_);
lean_inc_ref(v_fileMap_4832_);
lean_inc_ref(v_fileName_4831_);
v___x_4847_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4847_, 0, v_fileName_4831_);
lean_ctor_set(v___x_4847_, 1, v_fileMap_4832_);
lean_ctor_set(v___x_4847_, 2, v___x_4827_);
lean_ctor_set(v___x_4847_, 3, v_currRecDepth_4833_);
lean_ctor_set(v___x_4847_, 4, v___x_4846_);
lean_ctor_set(v___x_4847_, 5, v_ref_4834_);
lean_ctor_set(v___x_4847_, 6, v_currNamespace_4835_);
lean_ctor_set(v___x_4847_, 7, v_openDecls_4836_);
lean_ctor_set(v___x_4847_, 8, v_initHeartbeats_4837_);
lean_ctor_set(v___x_4847_, 9, v_maxHeartbeats_4838_);
lean_ctor_set(v___x_4847_, 10, v_quotContext_4839_);
lean_ctor_set(v___x_4847_, 11, v_currMacroScope_4840_);
lean_ctor_set(v___x_4847_, 12, v_cancelTk_x3f_4841_);
lean_ctor_set(v___x_4847_, 13, v_inheritedTraceOptions_4843_);
lean_ctor_set_uint8(v___x_4847_, sizeof(void*)*14, v___x_4829_);
lean_ctor_set_uint8(v___x_4847_, sizeof(void*)*14 + 1, v_suppressElabErrors_4842_);
v___x_4848_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v___x_4803_, v___x_4804_, v___y_4805_, v___y_4806_, v___x_4847_, v___y_4844_);
lean_dec_ref_known(v___x_4847_, 14);
return v___x_4848_;
}
v___jp_4849_:
{
uint8_t v___x_4851_; 
v___x_4851_ = lean_bool_not(v___y_4850_);
if (v___x_4851_ == 0)
{
v_fileName_4831_ = v_fileName_4811_;
v_fileMap_4832_ = v_fileMap_4812_;
v_currRecDepth_4833_ = v_currRecDepth_4814_;
v_ref_4834_ = v_ref_4815_;
v_currNamespace_4835_ = v_currNamespace_4816_;
v_openDecls_4836_ = v_openDecls_4817_;
v_initHeartbeats_4837_ = v_initHeartbeats_4818_;
v_maxHeartbeats_4838_ = v_maxHeartbeats_4819_;
v_quotContext_4839_ = v_quotContext_4820_;
v_currMacroScope_4840_ = v_currMacroScope_4821_;
v_cancelTk_x3f_4841_ = v_cancelTk_x3f_4822_;
v_suppressElabErrors_4842_ = v_suppressElabErrors_4823_;
v_inheritedTraceOptions_4843_ = v_inheritedTraceOptions_4824_;
v___y_4844_ = v___y_4808_;
goto v___jp_4830_;
}
else
{
lean_object* v___x_4852_; lean_object* v_env_4853_; lean_object* v_nextMacroScope_4854_; lean_object* v_ngen_4855_; lean_object* v_auxDeclNGen_4856_; lean_object* v_traceState_4857_; lean_object* v_messages_4858_; lean_object* v_infoState_4859_; lean_object* v_snapshotTasks_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4870_; 
v___x_4852_ = lean_st_ref_take(v___y_4808_);
v_env_4853_ = lean_ctor_get(v___x_4852_, 0);
v_nextMacroScope_4854_ = lean_ctor_get(v___x_4852_, 1);
v_ngen_4855_ = lean_ctor_get(v___x_4852_, 2);
v_auxDeclNGen_4856_ = lean_ctor_get(v___x_4852_, 3);
v_traceState_4857_ = lean_ctor_get(v___x_4852_, 4);
v_messages_4858_ = lean_ctor_get(v___x_4852_, 6);
v_infoState_4859_ = lean_ctor_get(v___x_4852_, 7);
v_snapshotTasks_4860_ = lean_ctor_get(v___x_4852_, 8);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4870_ == 0)
{
lean_object* v_unused_4871_; 
v_unused_4871_ = lean_ctor_get(v___x_4852_, 5);
lean_dec(v_unused_4871_);
v___x_4862_ = v___x_4852_;
v_isShared_4863_ = v_isSharedCheck_4870_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_snapshotTasks_4860_);
lean_inc(v_infoState_4859_);
lean_inc(v_messages_4858_);
lean_inc(v_traceState_4857_);
lean_inc(v_auxDeclNGen_4856_);
lean_inc(v_ngen_4855_);
lean_inc(v_nextMacroScope_4854_);
lean_inc(v_env_4853_);
lean_dec(v___x_4852_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4870_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4867_; 
v___x_4864_ = l_Lean_Kernel_enableDiag(v_env_4853_, v___x_4829_);
v___x_4865_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_4863_ == 0)
{
lean_ctor_set(v___x_4862_, 5, v___x_4865_);
lean_ctor_set(v___x_4862_, 0, v___x_4864_);
v___x_4867_ = v___x_4862_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4864_);
lean_ctor_set(v_reuseFailAlloc_4869_, 1, v_nextMacroScope_4854_);
lean_ctor_set(v_reuseFailAlloc_4869_, 2, v_ngen_4855_);
lean_ctor_set(v_reuseFailAlloc_4869_, 3, v_auxDeclNGen_4856_);
lean_ctor_set(v_reuseFailAlloc_4869_, 4, v_traceState_4857_);
lean_ctor_set(v_reuseFailAlloc_4869_, 5, v___x_4865_);
lean_ctor_set(v_reuseFailAlloc_4869_, 6, v_messages_4858_);
lean_ctor_set(v_reuseFailAlloc_4869_, 7, v_infoState_4859_);
lean_ctor_set(v_reuseFailAlloc_4869_, 8, v_snapshotTasks_4860_);
v___x_4867_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
lean_object* v___x_4868_; 
v___x_4868_ = lean_st_ref_set(v___y_4808_, v___x_4867_);
v_fileName_4831_ = v_fileName_4811_;
v_fileMap_4832_ = v_fileMap_4812_;
v_currRecDepth_4833_ = v_currRecDepth_4814_;
v_ref_4834_ = v_ref_4815_;
v_currNamespace_4835_ = v_currNamespace_4816_;
v_openDecls_4836_ = v_openDecls_4817_;
v_initHeartbeats_4837_ = v_initHeartbeats_4818_;
v_maxHeartbeats_4838_ = v_maxHeartbeats_4819_;
v_quotContext_4839_ = v_quotContext_4820_;
v_currMacroScope_4840_ = v_currMacroScope_4821_;
v_cancelTk_x3f_4841_ = v_cancelTk_x3f_4822_;
v_suppressElabErrors_4842_ = v_suppressElabErrors_4823_;
v_inheritedTraceOptions_4843_ = v_inheritedTraceOptions_4824_;
v___y_4844_ = v___y_4808_;
goto v___jp_4830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object* v___x_4874_, lean_object* v___x_4875_, lean_object* v___x_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
uint8_t v___x_9922__boxed_4882_; uint8_t v___x_9924__boxed_4883_; lean_object* v_res_4884_; 
v___x_9922__boxed_4882_ = lean_unbox(v___x_4874_);
v___x_9924__boxed_4883_ = lean_unbox(v___x_4876_);
v_res_4884_ = l_Lean_Elab_WF_mkUnfoldEq___lam__2(v___x_9922__boxed_4882_, v___x_4875_, v___x_9924__boxed_4883_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
return v_res_4884_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4886_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___closed__0));
v___x_4887_ = l_Lean_stringToMessageData(v___x_4886_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object* v_preDef_4888_, lean_object* v_unaryPreDefName_4889_, lean_object* v_wfPreprocessProof_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v___x_4896_; lean_object* v_env_4897_; lean_object* v_levelParams_4898_; lean_object* v_declName_4899_; lean_object* v_value_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___f_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___f_4907_; uint8_t v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; uint8_t v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___f_4914_; lean_object* v___x_4915_; 
v___x_4896_ = lean_st_ref_get(v_a_4894_);
v_env_4897_ = lean_ctor_get(v___x_4896_, 0);
lean_inc_ref(v_env_4897_);
lean_dec(v___x_4896_);
v_levelParams_4898_ = lean_ctor_get(v_preDef_4888_, 1);
lean_inc(v_levelParams_4898_);
v_declName_4899_ = lean_ctor_get(v_preDef_4888_, 3);
lean_inc_n(v_declName_4899_, 2);
v_value_4900_ = lean_ctor_get(v_preDef_4888_, 7);
lean_inc_ref(v_value_4900_);
lean_dec_ref(v_preDef_4888_);
v___x_4901_ = l_Lean_Meta_unfoldThmSuffix;
v___x_4902_ = l_Lean_Meta_mkEqLikeNameFor(v_env_4897_, v_declName_4899_, v___x_4901_);
lean_inc(v___x_4902_);
v___f_4903_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4903_, 0, v_levelParams_4898_);
lean_closure_set(v___f_4903_, 1, v_declName_4899_);
lean_closure_set(v___f_4903_, 2, v_wfPreprocessProof_4890_);
lean_closure_set(v___f_4903_, 3, v___x_4902_);
lean_closure_set(v___f_4903_, 4, v_unaryPreDefName_4889_);
v___x_4904_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___closed__1, &l_Lean_Elab_WF_mkUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1);
v___x_4905_ = l_Lean_MessageData_ofName(v___x_4902_);
v___x_4906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4904_);
lean_ctor_set(v___x_4906_, 1, v___x_4905_);
v___f_4907_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4907_, 0, v___x_4906_);
v___x_4908_ = 0;
v___x_4909_ = lean_box(v___x_4908_);
v___x_4910_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed), 9, 4);
lean_closure_set(v___x_4910_, 0, lean_box(0));
lean_closure_set(v___x_4910_, 1, v_value_4900_);
lean_closure_set(v___x_4910_, 2, v___f_4903_);
lean_closure_set(v___x_4910_, 3, v___x_4909_);
v___x_4911_ = 1;
v___x_4912_ = lean_box(v___x_4908_);
v___x_4913_ = lean_box(v___x_4911_);
v___f_4914_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_4914_, 0, v___x_4912_);
lean_closure_set(v___f_4914_, 1, v___x_4910_);
lean_closure_set(v___f_4914_, 2, v___x_4913_);
v___x_4915_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4914_, v___f_4907_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___x_4915_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4915_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
else
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4931_; 
v_a_4924_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4926_ = v___x_4915_;
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4915_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4929_; 
if (v_isShared_4927_ == 0)
{
v___x_4929_ = v___x_4926_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4924_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___boxed(lean_object* v_preDef_4932_, lean_object* v_unaryPreDefName_4933_, lean_object* v_wfPreprocessProof_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l_Lean_Elab_WF_mkUnfoldEq(v_preDef_4932_, v_unaryPreDefName_4933_, v_wfPreprocessProof_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
lean_dec(v_a_4938_);
lean_dec_ref(v_a_4937_);
lean_dec(v_a_4936_);
lean_dec_ref(v_a_4935_);
return v_res_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6(lean_object* v_00_u03b1_4941_, lean_object* v_x_4942_, uint8_t v_isExporting_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg(v_x_4942_, v_isExporting_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4950_, lean_object* v_x_4951_, lean_object* v_isExporting_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_){
_start:
{
uint8_t v_isExporting_boxed_4958_; lean_object* v_res_4959_; 
v_isExporting_boxed_4958_ = lean_unbox(v_isExporting_4952_);
v_res_4959_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6(v_00_u03b1_4950_, v_x_4951_, v_isExporting_boxed_4958_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_);
lean_dec(v___y_4956_);
lean_dec_ref(v___y_4955_);
lean_dec(v___y_4954_);
lean_dec_ref(v___y_4953_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(lean_object* v_00_u03b1_4960_, lean_object* v_x_4961_, uint8_t v_when_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v___x_4968_; 
v___x_4968_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___redArg(v_x_4961_, v_when_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5___boxed(lean_object* v_00_u03b1_4969_, lean_object* v_x_4970_, lean_object* v_when_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_){
_start:
{
uint8_t v_when_boxed_4977_; lean_object* v_res_4978_; 
v_when_boxed_4977_ = lean_unbox(v_when_4971_);
v_res_4978_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5(v_00_u03b1_4969_, v_x_4970_, v_when_boxed_4977_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
return v_res_4978_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4980_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0));
v___x_4981_ = l_Lean_stringToMessageData(v___x_4980_);
return v___x_4981_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4987_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3));
v___x_4988_ = l_Lean_stringToMessageData(v___x_4987_);
return v___x_4988_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4990_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5));
v___x_4991_ = l_Lean_stringToMessageData(v___x_4990_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object* v_levelParams_4992_, lean_object* v_declName_4993_, lean_object* v___x_4994_, lean_object* v___x_4995_, lean_object* v___x_4996_, lean_object* v_xs_4997_, lean_object* v_body_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5007_ = lean_box(0);
lean_inc(v_levelParams_4992_);
v___x_5008_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4992_, v___x_5007_);
v___x_5009_ = l_Lean_mkConst(v_declName_4993_, v___x_5008_);
v___x_5010_ = l_Lean_mkAppN(v___x_5009_, v_xs_4997_);
v___x_5011_ = l_Lean_Meta_mkEq(v___x_5010_, v_body_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc_n(v_a_5012_, 2);
lean_dec_ref_known(v___x_5011_, 1);
v___x_5013_ = lean_box(0);
v___x_5014_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_5012_, v___x_5013_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5014_) == 0)
{
lean_object* v_a_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v_a_5015_ = lean_ctor_get(v___x_5014_, 0);
lean_inc(v_a_5015_);
lean_dec_ref_known(v___x_5014_, 1);
v___x_5016_ = l_Lean_Expr_mvarId_x21(v_a_5015_);
v___x_5017_ = l_Lean_Elab_Eqns_deltaLHS(v___x_5016_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; uint8_t v___x_5019_; uint8_t v___x_5020_; lean_object* v___y_5022_; lean_object* v___y_5023_; lean_object* v___y_5024_; lean_object* v___y_5025_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
lean_inc_n(v_a_5018_, 2);
lean_dec_ref_known(v___x_5017_, 1);
v___x_5019_ = 1;
v___x_5020_ = 0;
v___x_5081_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2));
v___x_5082_ = l_Lean_MVarId_applyConst(v_a_5018_, v___x_4994_, v___x_5081_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v_a_5083_; uint8_t v___x_5084_; 
v_a_5083_ = lean_ctor_get(v___x_5082_, 0);
lean_inc(v_a_5083_);
lean_dec_ref_known(v___x_5082_, 1);
v___x_5084_ = l_List_isEmpty___redArg(v_a_5083_);
lean_dec(v_a_5083_);
if (v___x_5084_ == 0)
{
lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
lean_dec(v_a_5015_);
lean_dec(v_a_5012_);
lean_dec(v___x_4995_);
lean_dec(v_levelParams_4992_);
v___x_5085_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4);
v___x_5086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5086_, 0, v___x_5085_);
lean_ctor_set(v___x_5086_, 1, v___x_4996_);
v___x_5087_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6);
v___x_5088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5088_, 0, v___x_5086_);
lean_ctor_set(v___x_5088_, 1, v___x_5087_);
v___x_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5089_, 0, v_a_5018_);
v___x_5090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5090_, 0, v___x_5088_);
lean_ctor_set(v___x_5090_, 1, v___x_5089_);
v___x_5091_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5092_, 0, v___x_5090_);
lean_ctor_set(v___x_5092_, 1, v___x_5091_);
v___x_5093_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_5092_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
return v___x_5093_;
}
else
{
lean_dec(v_a_5018_);
lean_dec_ref(v___x_4996_);
v___y_5022_ = v___y_4999_;
v___y_5023_ = v___y_5000_;
v___y_5024_ = v___y_5001_;
v___y_5025_ = v___y_5002_;
goto v___jp_5021_;
}
}
else
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
lean_dec(v_a_5018_);
lean_dec(v_a_5015_);
lean_dec(v_a_5012_);
lean_dec_ref(v___x_4996_);
lean_dec(v___x_4995_);
lean_dec(v_levelParams_4992_);
v_a_5094_ = lean_ctor_get(v___x_5082_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5082_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5082_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5082_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
v___jp_5021_:
{
lean_object* v___x_5026_; lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5080_; 
v___x_5026_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_5015_, v___y_5023_);
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5029_ = v___x_5026_;
v_isShared_5030_ = v_isSharedCheck_5080_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_dec(v___x_5026_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5080_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
uint8_t v___x_5031_; lean_object* v___x_5032_; 
v___x_5031_ = 1;
v___x_5032_ = l_Lean_Meta_mkForallFVars(v_xs_4997_, v_a_5012_, v___x_5020_, v___x_5019_, v___x_5019_, v___x_5031_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
if (lean_obj_tag(v___x_5032_) == 0)
{
lean_object* v_a_5033_; lean_object* v___x_5034_; 
v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_a_5033_);
lean_dec_ref_known(v___x_5032_, 1);
v___x_5034_ = l_Lean_Meta_letToHave(v_a_5033_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_object* v_a_5035_; lean_object* v___x_5036_; 
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_a_5035_);
lean_dec_ref_known(v___x_5034_, 1);
v___x_5036_ = l_Lean_Meta_mkLambdaFVars(v_xs_4997_, v_a_5027_, v___x_5020_, v___x_5019_, v___x_5020_, v___x_5019_, v___x_5031_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5042_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_a_5037_);
lean_dec_ref_known(v___x_5036_, 1);
lean_inc_n(v___x_4995_, 2);
v___x_5038_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5038_, 0, v___x_4995_);
lean_ctor_set(v___x_5038_, 1, v_levelParams_4992_);
lean_ctor_set(v___x_5038_, 2, v_a_5035_);
v___x_5039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5039_, 0, v___x_4995_);
lean_ctor_set(v___x_5039_, 1, v___x_5007_);
v___x_5040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5038_);
lean_ctor_set(v___x_5040_, 1, v_a_5037_);
lean_ctor_set(v___x_5040_, 2, v___x_5039_);
if (v_isShared_5030_ == 0)
{
lean_ctor_set_tag(v___x_5029_, 2);
lean_ctor_set(v___x_5029_, 0, v___x_5040_);
v___x_5042_ = v___x_5029_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v___x_5040_);
v___x_5042_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
lean_object* v___x_5043_; 
v___x_5043_ = l_Lean_addDecl(v___x_5042_, v___x_5020_, v___y_5024_, v___y_5025_);
if (lean_obj_tag(v___x_5043_) == 0)
{
lean_object* v___x_5044_; 
lean_dec_ref_known(v___x_5043_, 1);
lean_inc(v___x_4995_);
v___x_5044_ = l_Lean_inferDefEqAttr(v___x_4995_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_options_5045_; uint8_t v_hasTrace_5046_; 
lean_dec_ref_known(v___x_5044_, 1);
v_options_5045_ = lean_ctor_get(v___y_5024_, 2);
v_hasTrace_5046_ = lean_ctor_get_uint8(v_options_5045_, sizeof(void*)*1);
if (v_hasTrace_5046_ == 0)
{
lean_dec(v___x_4995_);
goto v___jp_5004_;
}
else
{
lean_object* v_inheritedTraceOptions_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; uint8_t v___x_5050_; 
v_inheritedTraceOptions_5047_ = lean_ctor_get(v___y_5024_, 13);
v___x_5048_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_5049_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_5050_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5047_, v_options_5045_, v___x_5049_);
if (v___x_5050_ == 0)
{
lean_dec(v___x_4995_);
goto v___jp_5004_;
}
else
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5051_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1);
v___x_5052_ = l_Lean_MessageData_ofConstName(v___x_4995_, v___x_5020_);
v___x_5053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5051_);
lean_ctor_set(v___x_5053_, 1, v___x_5052_);
v___x_5054_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_5048_, v___x_5053_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
return v___x_5054_;
}
}
}
else
{
lean_dec(v___x_4995_);
return v___x_5044_;
}
}
else
{
lean_dec(v___x_4995_);
return v___x_5043_;
}
}
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5063_; 
lean_dec(v_a_5035_);
lean_del_object(v___x_5029_);
lean_dec(v___x_4995_);
lean_dec(v_levelParams_4992_);
v_a_5056_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5058_ = v___x_5036_;
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_5036_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5061_; 
if (v_isShared_5059_ == 0)
{
v___x_5061_ = v___x_5058_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_a_5056_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
}
else
{
lean_object* v_a_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5071_; 
lean_del_object(v___x_5029_);
lean_dec(v_a_5027_);
lean_dec(v___x_4995_);
lean_dec(v_levelParams_4992_);
v_a_5064_ = lean_ctor_get(v___x_5034_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5066_ = v___x_5034_;
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_a_5064_);
lean_dec(v___x_5034_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5069_; 
if (v_isShared_5067_ == 0)
{
v___x_5069_ = v___x_5066_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_a_5064_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
}
else
{
lean_object* v_a_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5079_; 
lean_del_object(v___x_5029_);
lean_dec(v_a_5027_);
lean_dec(v___x_4995_);
lean_dec(v_levelParams_4992_);
v_a_5072_ = lean_ctor_get(v___x_5032_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5074_ = v___x_5032_;
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_5032_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5077_; 
if (v_isShared_5075_ == 0)
{
v___x_5077_ = v___x_5074_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
}
}
}
}
}
}
else
{
lean_object* v_a_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5109_; 
lean_dec(v_a_5015_);
lean_dec(v_a_5012_);
lean_dec_ref(v___x_4996_);
lean_dec(v___x_4995_);
lean_dec(v___x_4994_);
lean_dec(v_levelParams_4992_);
v_a_5102_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_5104_ = v___x_5017_;
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_a_5102_);
lean_dec(v___x_5017_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5107_; 
if (v_isShared_5105_ == 0)
{
v___x_5107_ = v___x_5104_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v_a_5102_);
v___x_5107_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
return v___x_5107_;
}
}
}
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5117_; 
lean_dec(v_a_5012_);
lean_dec_ref(v___x_4996_);
lean_dec(v___x_4995_);
lean_dec(v___x_4994_);
lean_dec(v_levelParams_4992_);
v_a_5110_ = lean_ctor_get(v___x_5014_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5014_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5112_ = v___x_5014_;
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5014_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5115_; 
if (v_isShared_5113_ == 0)
{
v___x_5115_ = v___x_5112_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_a_5110_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
}
else
{
lean_object* v_a_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5125_; 
lean_dec_ref(v___x_4996_);
lean_dec(v___x_4995_);
lean_dec(v___x_4994_);
lean_dec(v_levelParams_4992_);
v_a_5118_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5120_ = v___x_5011_;
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5011_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5123_; 
if (v_isShared_5121_ == 0)
{
v___x_5123_ = v___x_5120_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
return v___x_5123_;
}
}
}
v___jp_5004_:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5005_ = lean_box(0);
v___x_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5005_);
return v___x_5006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed(lean_object* v_levelParams_5126_, lean_object* v_declName_5127_, lean_object* v___x_5128_, lean_object* v___x_5129_, lean_object* v___x_5130_, lean_object* v_xs_5131_, lean_object* v_body_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_){
_start:
{
lean_object* v_res_5138_; 
v_res_5138_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(v_levelParams_5126_, v_declName_5127_, v___x_5128_, v___x_5129_, v___x_5130_, v_xs_5131_, v_body_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
lean_dec(v___y_5136_);
lean_dec_ref(v___y_5135_);
lean_dec(v___y_5134_);
lean_dec_ref(v___y_5133_);
lean_dec_ref(v_xs_5131_);
return v_res_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(uint8_t v___x_5139_, lean_object* v_value_5140_, lean_object* v___f_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_){
_start:
{
lean_object* v___x_5147_; lean_object* v_fileName_5148_; lean_object* v_fileMap_5149_; lean_object* v_options_5150_; lean_object* v_currRecDepth_5151_; lean_object* v_ref_5152_; lean_object* v_currNamespace_5153_; lean_object* v_openDecls_5154_; lean_object* v_initHeartbeats_5155_; lean_object* v_maxHeartbeats_5156_; lean_object* v_quotContext_5157_; lean_object* v_currMacroScope_5158_; lean_object* v_cancelTk_x3f_5159_; uint8_t v_suppressElabErrors_5160_; lean_object* v_inheritedTraceOptions_5161_; lean_object* v_env_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; uint8_t v___x_5166_; lean_object* v_fileName_5168_; lean_object* v_fileMap_5169_; lean_object* v_currRecDepth_5170_; lean_object* v_ref_5171_; lean_object* v_currNamespace_5172_; lean_object* v_openDecls_5173_; lean_object* v_initHeartbeats_5174_; lean_object* v_maxHeartbeats_5175_; lean_object* v_quotContext_5176_; lean_object* v_currMacroScope_5177_; lean_object* v_cancelTk_x3f_5178_; uint8_t v_suppressElabErrors_5179_; lean_object* v_inheritedTraceOptions_5180_; lean_object* v___y_5181_; uint8_t v___y_5187_; uint8_t v___x_5209_; 
v___x_5147_ = lean_st_ref_get(v___y_5145_);
v_fileName_5148_ = lean_ctor_get(v___y_5144_, 0);
v_fileMap_5149_ = lean_ctor_get(v___y_5144_, 1);
v_options_5150_ = lean_ctor_get(v___y_5144_, 2);
v_currRecDepth_5151_ = lean_ctor_get(v___y_5144_, 3);
v_ref_5152_ = lean_ctor_get(v___y_5144_, 5);
v_currNamespace_5153_ = lean_ctor_get(v___y_5144_, 6);
v_openDecls_5154_ = lean_ctor_get(v___y_5144_, 7);
v_initHeartbeats_5155_ = lean_ctor_get(v___y_5144_, 8);
v_maxHeartbeats_5156_ = lean_ctor_get(v___y_5144_, 9);
v_quotContext_5157_ = lean_ctor_get(v___y_5144_, 10);
v_currMacroScope_5158_ = lean_ctor_get(v___y_5144_, 11);
v_cancelTk_x3f_5159_ = lean_ctor_get(v___y_5144_, 12);
v_suppressElabErrors_5160_ = lean_ctor_get_uint8(v___y_5144_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5161_ = lean_ctor_get(v___y_5144_, 13);
v_env_5162_ = lean_ctor_get(v___x_5147_, 0);
lean_inc_ref(v_env_5162_);
lean_dec(v___x_5147_);
v___x_5163_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_5150_);
v___x_5164_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_options_5150_, v___x_5163_, v___x_5139_);
v___x_5165_ = l_Lean_diagnostics;
v___x_5166_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v___x_5164_, v___x_5165_);
v___x_5209_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5162_);
lean_dec_ref(v_env_5162_);
if (v___x_5209_ == 0)
{
if (v___x_5166_ == 0)
{
uint8_t v___x_5210_; 
v___x_5210_ = 1;
v___y_5187_ = v___x_5210_;
goto v___jp_5186_;
}
else
{
v___y_5187_ = v___x_5209_;
goto v___jp_5186_;
}
}
else
{
v___y_5187_ = v___x_5166_;
goto v___jp_5186_;
}
v___jp_5167_:
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; 
v___x_5182_ = l_Lean_maxRecDepth;
v___x_5183_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v___x_5164_, v___x_5182_);
lean_inc_ref(v_inheritedTraceOptions_5180_);
lean_inc(v_cancelTk_x3f_5178_);
lean_inc(v_currMacroScope_5177_);
lean_inc(v_quotContext_5176_);
lean_inc(v_maxHeartbeats_5175_);
lean_inc(v_initHeartbeats_5174_);
lean_inc(v_openDecls_5173_);
lean_inc(v_currNamespace_5172_);
lean_inc(v_ref_5171_);
lean_inc(v_currRecDepth_5170_);
lean_inc_ref(v_fileMap_5169_);
lean_inc_ref(v_fileName_5168_);
v___x_5184_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5184_, 0, v_fileName_5168_);
lean_ctor_set(v___x_5184_, 1, v_fileMap_5169_);
lean_ctor_set(v___x_5184_, 2, v___x_5164_);
lean_ctor_set(v___x_5184_, 3, v_currRecDepth_5170_);
lean_ctor_set(v___x_5184_, 4, v___x_5183_);
lean_ctor_set(v___x_5184_, 5, v_ref_5171_);
lean_ctor_set(v___x_5184_, 6, v_currNamespace_5172_);
lean_ctor_set(v___x_5184_, 7, v_openDecls_5173_);
lean_ctor_set(v___x_5184_, 8, v_initHeartbeats_5174_);
lean_ctor_set(v___x_5184_, 9, v_maxHeartbeats_5175_);
lean_ctor_set(v___x_5184_, 10, v_quotContext_5176_);
lean_ctor_set(v___x_5184_, 11, v_currMacroScope_5177_);
lean_ctor_set(v___x_5184_, 12, v_cancelTk_x3f_5178_);
lean_ctor_set(v___x_5184_, 13, v_inheritedTraceOptions_5180_);
lean_ctor_set_uint8(v___x_5184_, sizeof(void*)*14, v___x_5166_);
lean_ctor_set_uint8(v___x_5184_, sizeof(void*)*14 + 1, v_suppressElabErrors_5179_);
v___x_5185_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_value_5140_, v___f_5141_, v___x_5139_, v___y_5142_, v___y_5143_, v___x_5184_, v___y_5181_);
lean_dec_ref_known(v___x_5184_, 14);
return v___x_5185_;
}
v___jp_5186_:
{
uint8_t v___x_5188_; 
v___x_5188_ = lean_bool_not(v___y_5187_);
if (v___x_5188_ == 0)
{
v_fileName_5168_ = v_fileName_5148_;
v_fileMap_5169_ = v_fileMap_5149_;
v_currRecDepth_5170_ = v_currRecDepth_5151_;
v_ref_5171_ = v_ref_5152_;
v_currNamespace_5172_ = v_currNamespace_5153_;
v_openDecls_5173_ = v_openDecls_5154_;
v_initHeartbeats_5174_ = v_initHeartbeats_5155_;
v_maxHeartbeats_5175_ = v_maxHeartbeats_5156_;
v_quotContext_5176_ = v_quotContext_5157_;
v_currMacroScope_5177_ = v_currMacroScope_5158_;
v_cancelTk_x3f_5178_ = v_cancelTk_x3f_5159_;
v_suppressElabErrors_5179_ = v_suppressElabErrors_5160_;
v_inheritedTraceOptions_5180_ = v_inheritedTraceOptions_5161_;
v___y_5181_ = v___y_5145_;
goto v___jp_5167_;
}
else
{
lean_object* v___x_5189_; lean_object* v_env_5190_; lean_object* v_nextMacroScope_5191_; lean_object* v_ngen_5192_; lean_object* v_auxDeclNGen_5193_; lean_object* v_traceState_5194_; lean_object* v_messages_5195_; lean_object* v_infoState_5196_; lean_object* v_snapshotTasks_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5207_; 
v___x_5189_ = lean_st_ref_take(v___y_5145_);
v_env_5190_ = lean_ctor_get(v___x_5189_, 0);
v_nextMacroScope_5191_ = lean_ctor_get(v___x_5189_, 1);
v_ngen_5192_ = lean_ctor_get(v___x_5189_, 2);
v_auxDeclNGen_5193_ = lean_ctor_get(v___x_5189_, 3);
v_traceState_5194_ = lean_ctor_get(v___x_5189_, 4);
v_messages_5195_ = lean_ctor_get(v___x_5189_, 6);
v_infoState_5196_ = lean_ctor_get(v___x_5189_, 7);
v_snapshotTasks_5197_ = lean_ctor_get(v___x_5189_, 8);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_5189_);
if (v_isSharedCheck_5207_ == 0)
{
lean_object* v_unused_5208_; 
v_unused_5208_ = lean_ctor_get(v___x_5189_, 5);
lean_dec(v_unused_5208_);
v___x_5199_ = v___x_5189_;
v_isShared_5200_ = v_isSharedCheck_5207_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_snapshotTasks_5197_);
lean_inc(v_infoState_5196_);
lean_inc(v_messages_5195_);
lean_inc(v_traceState_5194_);
lean_inc(v_auxDeclNGen_5193_);
lean_inc(v_ngen_5192_);
lean_inc(v_nextMacroScope_5191_);
lean_inc(v_env_5190_);
lean_dec(v___x_5189_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5207_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5204_; 
v___x_5201_ = l_Lean_Kernel_enableDiag(v_env_5190_, v___x_5166_);
v___x_5202_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__5_spec__6___redArg___closed__2);
if (v_isShared_5200_ == 0)
{
lean_ctor_set(v___x_5199_, 5, v___x_5202_);
lean_ctor_set(v___x_5199_, 0, v___x_5201_);
v___x_5204_ = v___x_5199_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v___x_5201_);
lean_ctor_set(v_reuseFailAlloc_5206_, 1, v_nextMacroScope_5191_);
lean_ctor_set(v_reuseFailAlloc_5206_, 2, v_ngen_5192_);
lean_ctor_set(v_reuseFailAlloc_5206_, 3, v_auxDeclNGen_5193_);
lean_ctor_set(v_reuseFailAlloc_5206_, 4, v_traceState_5194_);
lean_ctor_set(v_reuseFailAlloc_5206_, 5, v___x_5202_);
lean_ctor_set(v_reuseFailAlloc_5206_, 6, v_messages_5195_);
lean_ctor_set(v_reuseFailAlloc_5206_, 7, v_infoState_5196_);
lean_ctor_set(v_reuseFailAlloc_5206_, 8, v_snapshotTasks_5197_);
v___x_5204_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
lean_object* v___x_5205_; 
v___x_5205_ = lean_st_ref_set(v___y_5145_, v___x_5204_);
v_fileName_5168_ = v_fileName_5148_;
v_fileMap_5169_ = v_fileMap_5149_;
v_currRecDepth_5170_ = v_currRecDepth_5151_;
v_ref_5171_ = v_ref_5152_;
v_currNamespace_5172_ = v_currNamespace_5153_;
v_openDecls_5173_ = v_openDecls_5154_;
v_initHeartbeats_5174_ = v_initHeartbeats_5155_;
v_maxHeartbeats_5175_ = v_maxHeartbeats_5156_;
v_quotContext_5176_ = v_quotContext_5157_;
v_currMacroScope_5177_ = v_currMacroScope_5158_;
v_cancelTk_x3f_5178_ = v_cancelTk_x3f_5159_;
v_suppressElabErrors_5179_ = v_suppressElabErrors_5160_;
v_inheritedTraceOptions_5180_ = v_inheritedTraceOptions_5161_;
v___y_5181_ = v___y_5145_;
goto v___jp_5167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed(lean_object* v___x_5211_, lean_object* v_value_5212_, lean_object* v___f_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_){
_start:
{
uint8_t v___x_5516__boxed_5219_; lean_object* v_res_5220_; 
v___x_5516__boxed_5219_ = lean_unbox(v___x_5211_);
v_res_5220_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(v___x_5516__boxed_5219_, v_value_5212_, v___f_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
return v_res_5220_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_5222_; lean_object* v___x_5223_; 
v___x_5222_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0));
v___x_5223_ = l_Lean_stringToMessageData(v___x_5222_);
return v___x_5223_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3(void){
_start:
{
lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5225_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__2));
v___x_5226_ = l_Lean_stringToMessageData(v___x_5225_);
return v___x_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object* v_preDef_5227_, lean_object* v_unaryPreDefName_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v_env_5236_; lean_object* v_levelParams_5237_; lean_object* v_declName_5238_; lean_object* v_value_5239_; lean_object* v_env_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___f_5250_; lean_object* v___x_5251_; lean_object* v___f_5252_; uint8_t v___x_5253_; lean_object* v___x_5254_; lean_object* v___f_5255_; lean_object* v___x_5256_; 
v___x_5234_ = lean_st_ref_get(v_a_5232_);
v___x_5235_ = lean_st_ref_get(v_a_5232_);
v_env_5236_ = lean_ctor_get(v___x_5234_, 0);
lean_inc_ref(v_env_5236_);
lean_dec(v___x_5234_);
v_levelParams_5237_ = lean_ctor_get(v_preDef_5227_, 1);
lean_inc(v_levelParams_5237_);
v_declName_5238_ = lean_ctor_get(v_preDef_5227_, 3);
lean_inc_n(v_declName_5238_, 2);
v_value_5239_ = lean_ctor_get(v_preDef_5227_, 7);
lean_inc_ref(v_value_5239_);
lean_dec_ref(v_preDef_5227_);
v_env_5240_ = lean_ctor_get(v___x_5235_, 0);
lean_inc_ref(v_env_5240_);
lean_dec(v___x_5235_);
v___x_5241_ = l_Lean_Meta_unfoldThmSuffix;
v___x_5242_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5236_, v_declName_5238_, v___x_5241_);
v___x_5243_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5240_, v_unaryPreDefName_5228_, v___x_5241_);
v___x_5244_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1);
lean_inc(v___x_5242_);
v___x_5245_ = l_Lean_MessageData_ofName(v___x_5242_);
v___x_5246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5246_, 0, v___x_5244_);
lean_ctor_set(v___x_5246_, 1, v___x_5245_);
v___x_5247_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3);
v___x_5248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5246_);
lean_ctor_set(v___x_5248_, 1, v___x_5247_);
lean_inc(v___x_5243_);
v___x_5249_ = l_Lean_MessageData_ofName(v___x_5243_);
lean_inc_ref(v___x_5249_);
v___f_5250_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5250_, 0, v_levelParams_5237_);
lean_closure_set(v___f_5250_, 1, v_declName_5238_);
lean_closure_set(v___f_5250_, 2, v___x_5243_);
lean_closure_set(v___f_5250_, 3, v___x_5242_);
lean_closure_set(v___f_5250_, 4, v___x_5249_);
v___x_5251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5251_, 0, v___x_5248_);
lean_ctor_set(v___x_5251_, 1, v___x_5249_);
v___f_5252_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_5252_, 0, v___x_5251_);
v___x_5253_ = 0;
v___x_5254_ = lean_box(v___x_5253_);
v___f_5255_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_5255_, 0, v___x_5254_);
lean_closure_set(v___f_5255_, 1, v_value_5239_);
lean_closure_set(v___f_5255_, 2, v___f_5250_);
v___x_5256_ = l_Lean_Meta_mapErrorImp___redArg(v___f_5255_, v___f_5252_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
if (lean_obj_tag(v___x_5256_) == 0)
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5264_; 
v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5259_ = v___x_5256_;
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5256_);
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
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5272_; 
v_a_5265_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5272_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5272_ == 0)
{
v___x_5267_ = v___x_5256_;
v_isShared_5268_ = v_isSharedCheck_5272_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_a_5265_);
lean_dec(v___x_5256_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5272_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5270_; 
if (v_isShared_5268_ == 0)
{
v___x_5270_ = v___x_5267_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_a_5265_);
v___x_5270_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
return v___x_5270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___boxed(lean_object* v_preDef_5273_, lean_object* v_unaryPreDefName_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_){
_start:
{
lean_object* v_res_5280_; 
v_res_5280_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_preDef_5273_, v_unaryPreDefName_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_);
lean_dec(v_a_5278_);
lean_dec_ref(v_a_5277_);
lean_dec(v_a_5276_);
lean_dec_ref(v_a_5275_);
return v_res_5280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5325_; uint8_t v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
v___x_5325_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5326_ = 0;
v___x_5327_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5328_ = l_Lean_registerTraceClass(v___x_5325_, v___x_5326_, v___x_5327_);
return v___x_5328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2____boxed(lean_object* v_a_5329_){
_start:
{
lean_object* v_res_5330_; 
v_res_5330_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_();
return v_res_5330_;
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
