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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* l_Lean_Meta_Simp_instInhabitedSimpM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instInhabitedSimpM___redArg___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "failed to finish proof for equational theorem for `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mkUnfoldEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Cannot derive unfold equation "};
static const lean_object* l_Lean_Elab_WF_mkUnfoldEq___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mkUnfoldEq___closed__0_value;
static lean_once_cell_t l_Lean_Elab_WF_mkUnfoldEq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_5979__boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v___x_5979__boxed_157_ = lean_unbox(v___x_155_);
v_res_158_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(v___x_5979__boxed_157_, v_x_156_);
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
uint8_t v___x_5987__boxed_188_; uint8_t v___x_5988__boxed_189_; lean_object* v_res_190_; 
v___x_5987__boxed_188_ = lean_unbox(v___x_179_);
v___x_5988__boxed_189_ = lean_unbox(v___x_180_);
v_res_190_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(v___x_177_, v___x_178_, v___x_5987__boxed_188_, v___x_5988__boxed_189_, v_ys_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4___boxed(lean_object* v_msgData_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msgData_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(lean_object* v_msg_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_ref_222_; lean_object* v___x_223_; lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_232_; 
v_ref_222_ = lean_ctor_get(v___y_219_, 2);
v___x_223_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg___boxed(lean_object* v_msg_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_ks_244_; lean_object* v_vs_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_269_; 
v_ks_244_ = lean_ctor_get(v_x_240_, 0);
v_vs_245_ = lean_ctor_get(v_x_240_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_240_);
if (v_isSharedCheck_269_ == 0)
{
v___x_247_ = v_x_240_;
v_isShared_248_ = v_isSharedCheck_269_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_vs_245_);
lean_inc(v_ks_244_);
lean_dec(v_x_240_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_269_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_array_get_size(v_ks_244_);
v___x_250_ = lean_nat_dec_lt(v_x_241_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
lean_dec(v_x_241_);
v___x_251_ = lean_array_push(v_ks_244_, v_x_242_);
v___x_252_ = lean_array_push(v_vs_245_, v_x_243_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v___x_252_);
lean_ctor_set(v___x_247_, 0, v___x_251_);
v___x_254_ = v___x_247_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
else
{
lean_object* v_k_x27_256_; uint8_t v___x_257_; 
v_k_x27_256_ = lean_array_fget_borrowed(v_ks_244_, v_x_241_);
v___x_257_ = l_Lean_instBEqMVarId_beq(v_x_242_, v_k_x27_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_259_; 
if (v_isShared_248_ == 0)
{
v___x_259_ = v___x_247_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_ks_244_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_vs_245_);
v___x_259_ = v_reuseFailAlloc_263_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_add(v_x_241_, v___x_260_);
lean_dec(v_x_241_);
v_x_240_ = v___x_259_;
v_x_241_ = v___x_261_;
goto _start;
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_264_ = lean_array_fset(v_ks_244_, v_x_241_, v_x_242_);
v___x_265_ = lean_array_fset(v_vs_245_, v_x_241_, v_x_243_);
lean_dec(v_x_241_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v___x_265_);
lean_ctor_set(v___x_247_, 0, v___x_264_);
v___x_267_ = v___x_247_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_n_270_, lean_object* v_k_271_, lean_object* v_v_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_270_, v___x_273_, v_k_271_, v_v_272_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(lean_object* v_x_276_, size_t v_x_277_, size_t v_x_278_, lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_object* v_es_281_; size_t v___x_282_; size_t v___x_283_; lean_object* v_j_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_es_281_ = lean_ctor_get(v_x_276_, 0);
v___x_282_ = ((size_t)31ULL);
v___x_283_ = lean_usize_land(v_x_277_, v___x_282_);
v_j_284_ = lean_usize_to_nat(v___x_283_);
v___x_285_ = lean_array_get_size(v_es_281_);
v___x_286_ = lean_nat_dec_lt(v_j_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_dec(v_j_284_);
lean_dec(v_x_280_);
lean_dec(v_x_279_);
return v_x_276_;
}
else
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_325_; 
lean_inc_ref(v_es_281_);
v_isSharedCheck_325_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; 
v_unused_326_ = lean_ctor_get(v_x_276_, 0);
lean_dec(v_unused_326_);
v___x_288_ = v_x_276_;
v_isShared_289_ = v_isSharedCheck_325_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_x_276_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_325_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_v_290_; lean_object* v___x_291_; lean_object* v_xs_x27_292_; lean_object* v___y_294_; 
v_v_290_ = lean_array_fget(v_es_281_, v_j_284_);
v___x_291_ = lean_box(0);
v_xs_x27_292_ = lean_array_fset(v_es_281_, v_j_284_, v___x_291_);
switch(lean_obj_tag(v_v_290_))
{
case 0:
{
lean_object* v_key_299_; lean_object* v_val_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_310_; 
v_key_299_ = lean_ctor_get(v_v_290_, 0);
v_val_300_ = lean_ctor_get(v_v_290_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_v_290_);
if (v_isSharedCheck_310_ == 0)
{
v___x_302_ = v_v_290_;
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_val_300_);
lean_inc(v_key_299_);
lean_dec(v_v_290_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
uint8_t v___x_304_; 
v___x_304_ = l_Lean_instBEqMVarId_beq(v_x_279_, v_key_299_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_del_object(v___x_302_);
v___x_305_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_299_, v_val_300_, v_x_279_, v_x_280_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___y_294_ = v___x_306_;
goto v___jp_293_;
}
else
{
lean_object* v___x_308_; 
lean_dec(v_val_300_);
lean_dec(v_key_299_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v_x_280_);
lean_ctor_set(v___x_302_, 0, v_x_279_);
v___x_308_ = v___x_302_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_x_279_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_x_280_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
v___y_294_ = v___x_308_;
goto v___jp_293_;
}
}
}
}
case 1:
{
lean_object* v_node_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_323_; 
v_node_311_ = lean_ctor_get(v_v_290_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v_v_290_);
if (v_isSharedCheck_323_ == 0)
{
v___x_313_ = v_v_290_;
v_isShared_314_ = v_isSharedCheck_323_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_node_311_);
lean_dec(v_v_290_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_323_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
size_t v___x_315_; size_t v___x_316_; size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_315_ = ((size_t)5ULL);
v___x_316_ = lean_usize_shift_right(v_x_277_, v___x_315_);
v___x_317_ = ((size_t)1ULL);
v___x_318_ = lean_usize_add(v_x_278_, v___x_317_);
v___x_319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_node_311_, v___x_316_, v___x_318_, v_x_279_, v_x_280_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_319_);
v___x_321_ = v___x_313_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
v___y_294_ = v___x_321_;
goto v___jp_293_;
}
}
}
default: 
{
lean_object* v___x_324_; 
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v_x_279_);
lean_ctor_set(v___x_324_, 1, v_x_280_);
v___y_294_ = v___x_324_;
goto v___jp_293_;
}
}
v___jp_293_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_array_fset(v_xs_x27_292_, v_j_284_, v___y_294_);
lean_dec(v_j_284_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_295_);
v___x_297_ = v___x_288_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
else
{
lean_object* v_ks_327_; lean_object* v_vs_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_346_; 
v_ks_327_ = lean_ctor_get(v_x_276_, 0);
v_vs_328_ = lean_ctor_get(v_x_276_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_346_ == 0)
{
v___x_330_ = v_x_276_;
v_isShared_331_ = v_isSharedCheck_346_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_vs_328_);
lean_inc(v_ks_327_);
lean_dec(v_x_276_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_346_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_ks_327_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_vs_328_);
v___x_333_ = v_reuseFailAlloc_345_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v_newNode_334_; size_t v___x_335_; uint8_t v___x_336_; 
v_newNode_334_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v___x_333_, v_x_279_, v_x_280_);
v___x_335_ = ((size_t)7ULL);
v___x_336_ = lean_usize_dec_le(v___x_335_, v_x_278_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_334_);
v___x_338_ = lean_unsigned_to_nat(4u);
v___x_339_ = lean_nat_dec_lt(v___x_337_, v___x_338_);
lean_dec(v___x_337_);
if (v___x_339_ == 0)
{
lean_object* v_ks_340_; lean_object* v_vs_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_ks_340_ = lean_ctor_get(v_newNode_334_, 0);
lean_inc_ref(v_ks_340_);
v_vs_341_ = lean_ctor_get(v_newNode_334_, 1);
lean_inc_ref(v_vs_341_);
lean_dec_ref(v_newNode_334_);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_344_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_x_278_, v_ks_340_, v_vs_341_, v___x_342_, v___x_343_);
lean_dec_ref(v_vs_341_);
lean_dec_ref(v_ks_340_);
return v___x_344_;
}
else
{
return v_newNode_334_;
}
}
else
{
return v_newNode_334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_347_, lean_object* v_keys_348_, lean_object* v_vals_349_, lean_object* v_i_350_, lean_object* v_entries_351_){
_start:
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_array_get_size(v_keys_348_);
v___x_353_ = lean_nat_dec_lt(v_i_350_, v___x_352_);
if (v___x_353_ == 0)
{
lean_dec(v_i_350_);
return v_entries_351_;
}
else
{
lean_object* v_k_354_; lean_object* v_v_355_; uint64_t v___x_356_; size_t v_h_357_; size_t v___x_358_; lean_object* v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v_h_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_k_354_ = lean_array_fget_borrowed(v_keys_348_, v_i_350_);
v_v_355_ = lean_array_fget_borrowed(v_vals_349_, v_i_350_);
v___x_356_ = l_Lean_instHashableMVarId_hash(v_k_354_);
v_h_357_ = lean_uint64_to_usize(v___x_356_);
v___x_358_ = ((size_t)5ULL);
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_sub(v_depth_347_, v___x_360_);
v___x_362_ = lean_usize_mul(v___x_358_, v___x_361_);
v_h_363_ = lean_usize_shift_right(v_h_357_, v___x_362_);
v___x_364_ = lean_nat_add(v_i_350_, v___x_359_);
lean_dec(v_i_350_);
lean_inc(v_v_355_);
lean_inc(v_k_354_);
v___x_365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_entries_351_, v_h_363_, v_depth_347_, v_k_354_, v_v_355_);
v_i_350_ = v___x_364_;
v_entries_351_ = v___x_365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_367_, lean_object* v_keys_368_, lean_object* v_vals_369_, lean_object* v_i_370_, lean_object* v_entries_371_){
_start:
{
size_t v_depth_boxed_372_; lean_object* v_res_373_; 
v_depth_boxed_372_ = lean_unbox_usize(v_depth_367_);
lean_dec(v_depth_367_);
v_res_373_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_372_, v_keys_368_, v_vals_369_, v_i_370_, v_entries_371_);
lean_dec_ref(v_vals_369_);
lean_dec_ref(v_keys_368_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
size_t v_x_6167__boxed_379_; size_t v_x_6168__boxed_380_; lean_object* v_res_381_; 
v_x_6167__boxed_379_ = lean_unbox_usize(v_x_375_);
lean_dec(v_x_375_);
v_x_6168__boxed_380_ = lean_unbox_usize(v_x_376_);
lean_dec(v_x_376_);
v_res_381_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_374_, v_x_6167__boxed_379_, v_x_6168__boxed_380_, v_x_377_, v_x_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
uint64_t v___x_385_; size_t v___x_386_; size_t v___x_387_; lean_object* v___x_388_; 
v___x_385_ = l_Lean_instHashableMVarId_hash(v_x_383_);
v___x_386_ = lean_uint64_to_usize(v___x_385_);
v___x_387_ = ((size_t)1ULL);
v___x_388_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_382_, v___x_386_, v___x_387_, v_x_383_, v_x_384_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(lean_object* v_mvarId_389_, lean_object* v_val_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; lean_object* v_mctx_394_; lean_object* v_cache_395_; lean_object* v_zetaDeltaFVarIds_396_; lean_object* v_postponed_397_; lean_object* v_diag_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_428_; 
v___x_393_ = lean_st_ref_take(v___y_391_);
v_mctx_394_ = lean_ctor_get(v___x_393_, 0);
v_cache_395_ = lean_ctor_get(v___x_393_, 1);
v_zetaDeltaFVarIds_396_ = lean_ctor_get(v___x_393_, 2);
v_postponed_397_ = lean_ctor_get(v___x_393_, 3);
v_diag_398_ = lean_ctor_get(v___x_393_, 4);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_428_ == 0)
{
v___x_400_ = v___x_393_;
v_isShared_401_ = v_isSharedCheck_428_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_diag_398_);
lean_inc(v_postponed_397_);
lean_inc(v_zetaDeltaFVarIds_396_);
lean_inc(v_cache_395_);
lean_inc(v_mctx_394_);
lean_dec(v___x_393_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_428_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_depth_402_; lean_object* v_levelAssignDepth_403_; lean_object* v_lmvarCounter_404_; lean_object* v_mvarCounter_405_; lean_object* v_lDecls_406_; lean_object* v_decls_407_; lean_object* v_userNames_408_; lean_object* v_lAssignment_409_; lean_object* v_eAssignment_410_; lean_object* v_dAssignment_411_; lean_object* v_instanceTypedMVars_412_; lean_object* v_synthNormMemo_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_427_; 
v_depth_402_ = lean_ctor_get(v_mctx_394_, 0);
v_levelAssignDepth_403_ = lean_ctor_get(v_mctx_394_, 1);
v_lmvarCounter_404_ = lean_ctor_get(v_mctx_394_, 2);
v_mvarCounter_405_ = lean_ctor_get(v_mctx_394_, 3);
v_lDecls_406_ = lean_ctor_get(v_mctx_394_, 4);
v_decls_407_ = lean_ctor_get(v_mctx_394_, 5);
v_userNames_408_ = lean_ctor_get(v_mctx_394_, 6);
v_lAssignment_409_ = lean_ctor_get(v_mctx_394_, 7);
v_eAssignment_410_ = lean_ctor_get(v_mctx_394_, 8);
v_dAssignment_411_ = lean_ctor_get(v_mctx_394_, 9);
v_instanceTypedMVars_412_ = lean_ctor_get(v_mctx_394_, 10);
v_synthNormMemo_413_ = lean_ctor_get(v_mctx_394_, 11);
v_isSharedCheck_427_ = !lean_is_exclusive(v_mctx_394_);
if (v_isSharedCheck_427_ == 0)
{
v___x_415_ = v_mctx_394_;
v_isShared_416_ = v_isSharedCheck_427_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_synthNormMemo_413_);
lean_inc(v_instanceTypedMVars_412_);
lean_inc(v_dAssignment_411_);
lean_inc(v_eAssignment_410_);
lean_inc(v_lAssignment_409_);
lean_inc(v_userNames_408_);
lean_inc(v_decls_407_);
lean_inc(v_lDecls_406_);
lean_inc(v_mvarCounter_405_);
lean_inc(v_lmvarCounter_404_);
lean_inc(v_levelAssignDepth_403_);
lean_inc(v_depth_402_);
lean_dec(v_mctx_394_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_427_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_417_ = lean_box(0);
v___x_418_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_eAssignment_410_, v_mvarId_389_, v_val_390_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 8, v___x_418_);
v___x_420_ = v___x_415_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_depth_402_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_levelAssignDepth_403_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_lmvarCounter_404_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_mvarCounter_405_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v_lDecls_406_);
lean_ctor_set(v_reuseFailAlloc_426_, 5, v_decls_407_);
lean_ctor_set(v_reuseFailAlloc_426_, 6, v_userNames_408_);
lean_ctor_set(v_reuseFailAlloc_426_, 7, v_lAssignment_409_);
lean_ctor_set(v_reuseFailAlloc_426_, 8, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_426_, 9, v_dAssignment_411_);
lean_ctor_set(v_reuseFailAlloc_426_, 10, v_instanceTypedMVars_412_);
lean_ctor_set(v_reuseFailAlloc_426_, 11, v_synthNormMemo_413_);
v___x_420_ = v_reuseFailAlloc_426_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_422_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_420_);
v___x_422_ = v___x_400_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_cache_395_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_zetaDeltaFVarIds_396_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v_postponed_397_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v_diag_398_);
v___x_422_ = v_reuseFailAlloc_425_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_st_ref_put(v___y_391_, v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_417_);
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
lean_inc(v_mvarId_477_);
v___x_484_ = l_Lean_MVarId_getType_x27(v_mvarId_477_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
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
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___f_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___f_499_; lean_object* v___x_500_; 
v___x_491_ = lean_box(v___x_488_);
v___f_492_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_492_, 0, v___x_491_);
v___x_493_ = l_Lean_Expr_appFn_x21(v_a_485_);
v___x_494_ = l_Lean_Expr_appArg_x21(v___x_493_);
lean_dec_ref(v___x_493_);
v___x_495_ = l_Lean_Expr_appArg_x21(v_a_485_);
lean_dec(v_a_485_);
v___x_496_ = 0;
v___x_497_ = lean_box(v___x_496_);
v___x_498_ = lean_box(v___x_488_);
lean_inc_ref_n(v___x_494_, 2);
v___f_499_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed), 11, 4);
lean_closure_set(v___f_499_, 0, v___x_494_);
lean_closure_set(v___f_499_, 1, v___x_478_);
lean_closure_set(v___f_499_, 2, v___x_497_);
lean_closure_set(v___f_499_, 3, v___x_498_);
v___x_500_ = l_Lean_Meta_delta_x3f(v___x_494_, v___f_492_, v___x_496_, v___y_481_, v___y_482_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
if (lean_obj_tag(v_a_501_) == 1)
{
lean_object* v_val_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref(v___x_494_);
v_val_502_ = lean_ctor_get(v_a_501_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_a_501_);
if (v_isSharedCheck_651_ == 0)
{
v___x_504_ = v_a_501_;
v_isShared_505_ = v_isSharedCheck_651_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_val_502_);
lean_dec(v_a_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_651_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_h_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___x_602_; 
lean_inc(v_val_502_);
v___x_602_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_val_502_, v___y_480_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = l_Lean_Expr_cleanupAnnotations(v_a_603_);
lean_dec(v_a_603_);
v___x_605_ = l_Lean_Expr_isApp(v___x_604_);
if (v___x_605_ == 0)
{
lean_dec_ref(v___x_604_);
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
v___y_584_ = v___y_482_;
goto v___jp_580_;
}
else
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = l_Lean_Expr_appFnCleanup___redArg(v___x_604_);
lean_dec_ref(v___x_604_);
v___x_607_ = l_Lean_Expr_isApp(v___x_606_);
if (v___x_607_ == 0)
{
lean_dec_ref(v___x_606_);
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
v___y_584_ = v___y_482_;
goto v___jp_580_;
}
else
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = l_Lean_Expr_appFnCleanup___redArg(v___x_606_);
lean_dec_ref(v___x_606_);
v___x_609_ = l_Lean_Expr_isApp(v___x_608_);
if (v___x_609_ == 0)
{
lean_dec_ref(v___x_608_);
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
v___y_584_ = v___y_482_;
goto v___jp_580_;
}
else
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = l_Lean_Expr_appFnCleanup___redArg(v___x_608_);
lean_dec_ref(v___x_608_);
v___x_611_ = l_Lean_Expr_isApp(v___x_610_);
if (v___x_611_ == 0)
{
lean_dec_ref(v___x_610_);
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
v___y_584_ = v___y_482_;
goto v___jp_580_;
}
else
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_610_);
lean_dec_ref(v___x_610_);
v___x_613_ = l_Lean_Expr_isApp(v___x_612_);
if (v___x_613_ == 0)
{
lean_dec_ref(v___x_612_);
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
v___y_584_ = v___y_482_;
goto v___jp_580_;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_614_ = l_Lean_Expr_appFnCleanup___redArg(v___x_612_);
lean_dec_ref(v___x_612_);
v___x_615_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14));
v___x_616_ = l_Lean_Expr_isConstOf(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
uint8_t v___x_617_; 
v___x_617_ = l_Lean_Expr_isApp(v___x_614_);
if (v___x_617_ == 0)
{
lean_dec_ref(v___x_614_);
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
v___y_584_ = v___y_482_;
goto v___jp_580_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_618_ = l_Lean_Expr_appFnCleanup___redArg(v___x_614_);
lean_dec_ref(v___x_614_);
v___x_619_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15));
v___x_620_ = l_Lean_Expr_isConstOf(v___x_618_, v___x_619_);
lean_dec_ref(v___x_618_);
if (v___x_620_ == 0)
{
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
v___y_584_ = v___y_482_;
goto v___jp_580_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_dummy_625_; lean_object* v_nargs_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_del_object(v___x_504_);
v___x_621_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17));
v___x_622_ = l_Lean_Expr_getAppFn(v_val_502_);
v___x_623_ = l_Lean_Expr_constLevels_x21(v___x_622_);
lean_dec_ref(v___x_622_);
v___x_624_ = l_Lean_mkConst(v___x_621_, v___x_623_);
v_dummy_625_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_626_ = l_Lean_Expr_getAppNumArgs(v_val_502_);
lean_inc(v_nargs_626_);
v___x_627_ = lean_mk_array(v_nargs_626_, v_dummy_625_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_sub(v_nargs_626_, v___x_628_);
lean_dec(v_nargs_626_);
lean_inc(v_val_502_);
v___x_630_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_502_, v___x_627_, v___x_629_);
v___x_631_ = l_Lean_mkAppN(v___x_624_, v___x_630_);
lean_dec_ref(v___x_630_);
v_h_507_ = v___x_631_;
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
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_dummy_636_; lean_object* v_nargs_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec_ref(v___x_614_);
lean_del_object(v___x_504_);
v___x_632_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19));
v___x_633_ = l_Lean_Expr_getAppFn(v_val_502_);
v___x_634_ = l_Lean_Expr_constLevels_x21(v___x_633_);
lean_dec_ref(v___x_633_);
v___x_635_ = l_Lean_mkConst(v___x_632_, v___x_634_);
v_dummy_636_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_637_ = l_Lean_Expr_getAppNumArgs(v_val_502_);
lean_inc(v_nargs_637_);
v___x_638_ = lean_mk_array(v_nargs_637_, v_dummy_636_);
v___x_639_ = lean_unsigned_to_nat(1u);
v___x_640_ = lean_nat_sub(v_nargs_637_, v___x_639_);
lean_dec(v_nargs_637_);
lean_inc(v_val_502_);
v___x_641_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_502_, v___x_638_, v___x_640_);
v___x_642_ = l_Lean_mkAppN(v___x_635_, v___x_641_);
lean_dec_ref(v___x_641_);
v_h_507_ = v___x_642_;
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
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_del_object(v___x_504_);
lean_dec(v_val_502_);
lean_dec_ref(v___f_499_);
lean_dec_ref(v___x_495_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v_mvarId_477_);
v_a_643_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_602_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_602_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
v___jp_506_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_512_ = l_Lean_Expr_appFn_x21(v_val_502_);
v___x_513_ = l_Lean_Expr_appArg_x21(v___x_512_);
lean_dec_ref(v___x_512_);
v___x_514_ = l_Lean_Expr_appArg_x21(v_val_502_);
lean_dec(v_val_502_);
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
v___x_520_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_518_, v___x_519_, v___f_499_, v___x_496_, v___x_496_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
v___x_522_ = l_Lean_mkAppB(v___x_513_, v___x_514_, v_a_521_);
v___x_523_ = l_Lean_Meta_mkEq(v___x_522_, v___x_495_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
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
v___x_530_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_477_, v_a_529_, v___y_509_);
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
lean_dec(v_mvarId_477_);
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
lean_dec(v_mvarId_477_);
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
lean_dec(v_mvarId_477_);
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
lean_dec_ref(v___x_495_);
lean_dec(v_mvarId_477_);
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
lean_dec_ref(v___f_499_);
lean_dec_ref(v___x_495_);
lean_dec(v_mvarId_477_);
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
lean_inc(v_val_502_);
v___x_587_ = l_Lean_MessageData_ofExpr(v_val_502_);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_588_);
v___x_590_ = v___x_504_;
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
lean_inc(v_mvarId_477_);
v___x_591_ = l_Lean_Meta_throwTacticEx___redArg(v___x_585_, v_mvarId_477_, v___x_590_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
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
lean_dec(v_val_502_);
lean_dec_ref(v___f_499_);
lean_dec_ref(v___x_495_);
lean_dec(v_mvarId_477_);
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
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec(v_a_501_);
lean_dec_ref(v___f_499_);
lean_dec_ref(v___x_495_);
lean_dec(v_mvarId_477_);
v___x_652_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21);
v___x_653_ = l_Lean_MessageData_ofExpr(v___x_494_);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_654_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v___x_655_;
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec_ref(v___f_499_);
lean_dec_ref(v___x_495_);
lean_dec_ref(v___x_494_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v_mvarId_477_);
v_a_656_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_500_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_500_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v___x_478_);
lean_dec(v_mvarId_477_);
v_a_664_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_484_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_484_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed(lean_object* v_mvarId_672_, lean_object* v___x_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(v_mvarId_672_, v___x_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(lean_object* v_mvarId_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___x_686_; lean_object* v___f_687_; lean_object* v___x_688_; 
v___x_686_ = l_Lean_instInhabitedExpr;
lean_inc(v_mvarId_680_);
v___f_687_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed), 7, 2);
lean_closure_set(v___f_687_, 0, v_mvarId_680_);
lean_closure_set(v___f_687_, 1, v___x_686_);
v___x_688_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(v_mvarId_680_, v___f_687_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___boxed(lean_object* v_mvarId_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(lean_object* v_mvarId_696_, lean_object* v_val_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_696_, v_val_697_, v___y_699_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___boxed(lean_object* v_mvarId_704_, lean_object* v_val_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(v_mvarId_704_, v_val_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(lean_object* v_00_u03b1_712_, lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___boxed(lean_object* v_00_u03b1_720_, lean_object* v_msg_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(v_00_u03b1_720_, v_msg_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2(lean_object* v_00_u03b2_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_x_729_, v_x_730_, v_x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_733_, lean_object* v_x_734_, size_t v_x_735_, size_t v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_734_, v_x_735_, v_x_736_, v_x_737_, v_x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
size_t v_x_6942__boxed_746_; size_t v_x_6943__boxed_747_; lean_object* v_res_748_; 
v_x_6942__boxed_746_ = lean_unbox_usize(v_x_742_);
lean_dec(v_x_742_);
v_x_6943__boxed_747_ = lean_unbox_usize(v_x_743_);
lean_dec(v_x_743_);
v_res_748_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(v_00_u03b2_740_, v_x_741_, v_x_6942__boxed_746_, v_x_6943__boxed_747_, v_x_744_, v_x_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_749_, lean_object* v_n_750_, lean_object* v_k_751_, lean_object* v_v_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v_n_750_, v_k_751_, v_v_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_754_, size_t v_depth_755_, lean_object* v_keys_756_, lean_object* v_vals_757_, lean_object* v_heq_758_, lean_object* v_i_759_, lean_object* v_entries_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_755_, v_keys_756_, v_vals_757_, v_i_759_, v_entries_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_762_, lean_object* v_depth_763_, lean_object* v_keys_764_, lean_object* v_vals_765_, lean_object* v_heq_766_, lean_object* v_i_767_, lean_object* v_entries_768_){
_start:
{
size_t v_depth_boxed_769_; lean_object* v_res_770_; 
v_depth_boxed_769_ = lean_unbox_usize(v_depth_763_);
lean_dec(v_depth_763_);
v_res_770_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_762_, v_depth_boxed_769_, v_keys_764_, v_vals_765_, v_heq_766_, v_i_767_, v_entries_768_);
lean_dec_ref(v_vals_765_);
lean_dec_ref(v_keys_764_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_772_, v_x_773_, v_x_774_, v_x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(lean_object* v_e_777_, lean_object* v_maxFVars_778_, lean_object* v_k_779_, uint8_t v_cleanupAnnotations_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___f_786_; uint8_t v___x_787_; uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___f_786_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_786_, 0, v_k_779_);
v___x_787_ = 1;
v___x_788_ = 0;
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v_maxFVars_778_);
v___x_790_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_777_, v___x_787_, v___x_788_, v___x_787_, v___x_788_, v___x_789_, v___f_786_, v_cleanupAnnotations_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec_ref_known(v___x_789_, 1);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_a_799_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_790_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_790_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg___boxed(lean_object* v_e_807_, lean_object* v_maxFVars_808_, lean_object* v_k_809_, lean_object* v_cleanupAnnotations_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_816_; lean_object* v_res_817_; 
v_cleanupAnnotations_boxed_816_ = lean_unbox(v_cleanupAnnotations_810_);
v_res_817_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_807_, v_maxFVars_808_, v_k_809_, v_cleanupAnnotations_boxed_816_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(lean_object* v_00_u03b1_818_, lean_object* v_e_819_, lean_object* v_maxFVars_820_, lean_object* v_k_821_, uint8_t v_cleanupAnnotations_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_819_, v_maxFVars_820_, v_k_821_, v_cleanupAnnotations_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___boxed(lean_object* v_00_u03b1_829_, lean_object* v_e_830_, lean_object* v_maxFVars_831_, lean_object* v_k_832_, lean_object* v_cleanupAnnotations_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_839_; lean_object* v_res_840_; 
v_cleanupAnnotations_boxed_839_ = lean_unbox(v_cleanupAnnotations_833_);
v_res_840_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(v_00_u03b1_829_, v_e_830_, v_maxFVars_831_, v_k_832_, v_cleanupAnnotations_boxed_839_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(lean_object* v___x_841_, lean_object* v_xs_842_, lean_object* v_t_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_852_ = lean_array_get_size(v_xs_842_);
v___x_853_ = lean_nat_dec_eq(v___x_852_, v___x_841_);
if (v___x_853_ == 0)
{
goto v___jp_849_;
}
else
{
uint8_t v___x_854_; 
v___x_854_ = l_Lean_Expr_isForall(v_t_843_);
if (v___x_854_ == 0)
{
goto v___jp_849_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_855_ = l_Lean_Expr_bindingBody_x21(v_t_843_);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_expr_has_loose_bvar(v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
uint8_t v___x_858_; lean_object* v___x_859_; 
v___x_858_ = 1;
v___x_859_ = l_Lean_Meta_mkLambdaFVars(v_xs_842_, v___x_855_, v___x_857_, v___x_854_, v___x_857_, v___x_854_, v___x_858_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_868_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_868_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v_a_860_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_864_);
v___x_866_ = v___x_862_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_859_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_859_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_dec_ref(v___x_855_);
goto v___jp_849_;
}
}
}
v___jp_849_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_box(0);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
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
lean_object* v___f_937_; lean_object* v___x_617__overap_938_; lean_object* v___x_939_; 
v___f_937_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_617__overap_938_ = lean_panic_fn_borrowed(v___f_937_, v_msg_931_);
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
lean_inc(v___y_933_);
lean_inc_ref(v___y_932_);
v___x_939_ = lean_apply_5(v___x_617__overap_938_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, lean_box(0));
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
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_a_986_; uint8_t v___x_987_; 
v___x_984_ = l_Lean_instInhabitedExpr;
v___x_985_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_977_, v_a_982_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_985_);
v___x_987_ = lean_unbox(v_a_986_);
if (v___x_987_ == 0)
{
lean_object* v_numParams_988_; lean_object* v_numDiscrs_989_; lean_object* v_nargs_990_; lean_object* v_dummy_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_numParams_988_ = lean_ctor_get(v_matcherInfo_978_, 0);
v_numDiscrs_989_ = lean_ctor_get(v_matcherInfo_978_, 1);
v_nargs_990_ = l_Lean_Expr_getAppNumArgs(v_e_977_);
v_dummy_991_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_990_);
v___x_992_ = lean_mk_array(v_nargs_990_, v_dummy_991_);
v___x_993_ = lean_unsigned_to_nat(1u);
v___x_994_ = lean_nat_sub(v_nargs_990_, v___x_993_);
lean_dec(v_nargs_990_);
v___x_995_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_977_, v___x_992_, v___x_994_);
v___x_996_ = lean_nat_add(v_numParams_988_, v_numDiscrs_989_);
v___x_997_ = lean_array_get(v___x_984_, v___x_995_, v___x_996_);
lean_dec(v___x_996_);
lean_dec_ref(v___x_995_);
v___x_998_ = l_Lean_Expr_isFVar(v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec(v___x_997_);
lean_dec(v_a_986_);
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
v___x_1004_ = lean_unbox(v_a_986_);
lean_dec(v_a_986_);
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
lean_dec(v_a_986_);
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
lean_object* v___f_1042_; lean_object* v___x_11828__overap_1043_; lean_object* v___x_1044_; 
v___f_1042_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_11828__overap_1043_ = lean_panic_fn_borrowed(v___f_1042_, v_msg_1036_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
v___x_1044_ = lean_apply_5(v___x_11828__overap_1043_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, lean_box(0));
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
uint8_t v___x_15935__boxed_1199_; lean_object* v_res_1200_; 
v___x_15935__boxed_1199_ = lean_unbox(v___x_1191_);
v_res_1200_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(v___x_1188_, v___x_1189_, v_alpha_1190_, v___x_15935__boxed_1199_, v_xs_1192_, v_x_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
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
uint8_t v___x_15989__boxed_1251_; uint8_t v___x_15990__boxed_1252_; lean_object* v_res_1253_; 
v___x_15989__boxed_1251_ = lean_unbox(v___x_1241_);
v___x_15990__boxed_1252_ = lean_unbox(v___x_1243_);
v_res_1253_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(v___x_1236_, v___x_1237_, v_rel_1238_, v___x_1239_, v_beta_1240_, v___x_15989__boxed_1251_, v_alpha_1242_, v___x_15990__boxed_1252_, v_xs_1244_, v_x_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v_x_1245_);
return v_res_1253_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1));
v___x_1257_ = lean_unsigned_to_nat(10u);
v___x_1258_ = lean_unsigned_to_nat(146u);
v___x_1259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0));
v___x_1260_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_1261_ = l_mkPanicMessageWithDecl(v___x_1260_, v___x_1259_, v___x_1258_, v___x_1257_, v___x_1256_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(lean_object* v___f_1262_, uint8_t v___x_1263_, lean_object* v_a_1264_, uint8_t v___x_1265_, lean_object* v_ys_1266_, lean_object* v_altBodyType_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v___x_1273_; 
v___x_1273_ = l_Lean_Expr_isForall(v_altBodyType_1267_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_dec_ref(v_ys_1266_);
lean_dec_ref(v_a_1264_);
lean_dec_ref(v___f_1262_);
v___x_1274_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2);
v___x_1275_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v___x_1274_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = l_Lean_Expr_bindingDomain_x21(v_altBodyType_1267_);
v___x_1277_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_1278_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_1276_, v___x_1277_, v___f_1262_, v___x_1263_, v___x_1263_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
lean_inc_ref(v_ys_1266_);
v___x_1280_ = lean_array_push(v_ys_1266_, v_a_1279_);
v___x_1281_ = l_Lean_mkAppN(v_a_1264_, v___x_1280_);
lean_dec_ref(v___x_1280_);
v___x_1282_ = 1;
v___x_1283_ = l_Lean_Meta_mkLambdaFVars(v_ys_1266_, v___x_1281_, v___x_1263_, v___x_1265_, v___x_1263_, v___x_1265_, v___x_1282_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec_ref(v_ys_1266_);
return v___x_1283_;
}
else
{
lean_dec_ref(v_ys_1266_);
lean_dec_ref(v_a_1264_);
return v___x_1278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed(lean_object* v___f_1284_, lean_object* v___x_1285_, lean_object* v_a_1286_, lean_object* v___x_1287_, lean_object* v_ys_1288_, lean_object* v_altBodyType_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
uint8_t v___x_16074__boxed_1295_; uint8_t v___x_16075__boxed_1296_; lean_object* v_res_1297_; 
v___x_16074__boxed_1295_ = lean_unbox(v___x_1285_);
v___x_16075__boxed_1296_ = lean_unbox(v___x_1287_);
v_res_1297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(v___f_1284_, v___x_16074__boxed_1295_, v_a_1286_, v___x_16075__boxed_1296_, v_ys_1288_, v_altBodyType_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec_ref(v_altBodyType_1289_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(lean_object* v___x_1298_, lean_object* v___x_1299_, lean_object* v_f_1300_, uint8_t v___x_1301_, uint8_t v___x_1302_, lean_object* v_ys_1303_, lean_object* v_x_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = lean_array_get_borrowed(v___x_1298_, v_ys_1303_, v___x_1299_);
lean_inc(v___x_1310_);
v___x_1311_ = l_Lean_Expr_app___override(v_f_1300_, v___x_1310_);
v___x_1312_ = 1;
v___x_1313_ = l_Lean_Meta_mkLambdaFVars(v_ys_1303_, v___x_1311_, v___x_1301_, v___x_1302_, v___x_1301_, v___x_1302_, v___x_1312_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed(lean_object* v___x_1314_, lean_object* v___x_1315_, lean_object* v_f_1316_, lean_object* v___x_1317_, lean_object* v___x_1318_, lean_object* v_ys_1319_, lean_object* v_x_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
uint8_t v___x_16130__boxed_1326_; uint8_t v___x_16131__boxed_1327_; lean_object* v_res_1328_; 
v___x_16130__boxed_1326_ = lean_unbox(v___x_1317_);
v___x_16131__boxed_1327_ = lean_unbox(v___x_1318_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(v___x_1314_, v___x_1315_, v_f_1316_, v___x_16130__boxed_1326_, v___x_16131__boxed_1327_, v_ys_1319_, v_x_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec_ref(v_x_1320_);
lean_dec_ref(v_ys_1319_);
lean_dec(v___x_1315_);
lean_dec_ref(v___x_1314_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(lean_object* v_f_1329_, lean_object* v_as_1330_, size_t v_sz_1331_, size_t v_i_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v___x_1339_; 
v___x_1339_ = lean_usize_dec_lt(v_i_1332_, v_sz_1331_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
lean_dec_ref(v_f_1329_);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v_b_1333_);
return v___x_1340_;
}
else
{
lean_object* v_snd_1341_; lean_object* v_fst_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1405_; 
v_snd_1341_ = lean_ctor_get(v_b_1333_, 1);
v_fst_1342_ = lean_ctor_get(v_b_1333_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_b_1333_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1344_ = v_b_1333_;
v_isShared_1345_ = v_isSharedCheck_1405_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_snd_1341_);
lean_inc(v_fst_1342_);
lean_dec(v_b_1333_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1405_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v_array_1346_; lean_object* v_start_1347_; lean_object* v_stop_1348_; uint8_t v___x_1349_; 
v_array_1346_ = lean_ctor_get(v_snd_1341_, 0);
v_start_1347_ = lean_ctor_get(v_snd_1341_, 1);
v_stop_1348_ = lean_ctor_get(v_snd_1341_, 2);
v___x_1349_ = lean_nat_dec_lt(v_start_1347_, v_stop_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1351_; 
lean_dec_ref(v_f_1329_);
if (v_isShared_1345_ == 0)
{
v___x_1351_ = v___x_1344_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_fst_1342_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_snd_1341_);
v___x_1351_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
}
else
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1401_; 
lean_inc(v_stop_1348_);
lean_inc(v_start_1347_);
lean_inc_ref(v_array_1346_);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_snd_1341_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; lean_object* v_unused_1403_; lean_object* v_unused_1404_; 
v_unused_1402_ = lean_ctor_get(v_snd_1341_, 2);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_snd_1341_, 1);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_snd_1341_, 0);
lean_dec(v_unused_1404_);
v___x_1355_ = v_snd_1341_;
v_isShared_1356_ = v_isSharedCheck_1401_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v_snd_1341_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1401_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; lean_object* v_a_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___f_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1357_ = l_Lean_instInhabitedExpr;
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = 0;
v_a_1360_ = lean_array_uget_borrowed(v_as_1330_, v_i_1332_);
v___x_1361_ = lean_box(v___x_1359_);
v___x_1362_ = lean_box(v___x_1349_);
lean_inc_ref(v_f_1329_);
v___f_1363_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1363_, 0, v___x_1357_);
lean_closure_set(v___f_1363_, 1, v___x_1358_);
lean_closure_set(v___f_1363_, 2, v_f_1329_);
lean_closure_set(v___f_1363_, 3, v___x_1361_);
lean_closure_set(v___f_1363_, 4, v___x_1362_);
v___x_1364_ = lean_box(v___x_1359_);
v___x_1365_ = lean_box(v___x_1349_);
lean_inc(v_a_1360_);
v___f_1366_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1366_, 0, v___f_1363_);
lean_closure_set(v___f_1366_, 1, v___x_1364_);
lean_closure_set(v___f_1366_, 2, v_a_1360_);
lean_closure_set(v___f_1366_, 3, v___x_1365_);
v___x_1367_ = lean_array_fget(v_array_1346_, v_start_1347_);
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_add(v_start_1347_, v___x_1368_);
lean_dec(v_start_1347_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1369_);
v___x_1371_ = v___x_1355_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_array_1346_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_stop_1348_);
v___x_1371_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; 
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc(v_a_1360_);
v___x_1372_ = lean_infer_type(v_a_1360_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1367_);
v___x_1375_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1373_, v___x_1374_, v___f_1366_, v___x_1359_, v___x_1359_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = l_Lean_Expr_app___override(v_fst_1342_, v_a_1376_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v___x_1371_);
lean_ctor_set(v___x_1344_, 0, v___x_1377_);
v___x_1379_ = v___x_1344_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1371_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
size_t v___x_1380_; size_t v___x_1381_; 
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1332_, v___x_1380_);
v_i_1332_ = v___x_1381_;
v_b_1333_ = v___x_1379_;
goto _start;
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v___x_1371_);
lean_del_object(v___x_1344_);
lean_dec(v_fst_1342_);
lean_dec_ref(v_f_1329_);
v_a_1384_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1375_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1375_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v___x_1371_);
lean_dec(v___x_1367_);
lean_dec_ref(v___f_1366_);
lean_del_object(v___x_1344_);
lean_dec(v_fst_1342_);
lean_dec_ref(v_f_1329_);
v_a_1392_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1372_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1372_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
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
lean_object* v_head_1427_; lean_object* v_tail_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; lean_object* v___x_1431_; 
v_head_1427_ = lean_ctor_get(v_as_x27_1419_, 0);
v_tail_1428_ = lean_ctor_get(v_as_x27_1419_, 1);
v___x_1429_ = lean_box(0);
v___x_1430_ = 1;
lean_inc(v_head_1427_);
v___x_1431_ = l_Lean_MVarId_refl(v_head_1427_, v___x_1430_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_dec_ref_known(v___x_1431_, 1);
v_as_x27_1419_ = v_tail_1428_;
v_b_1420_ = v___x_1429_;
goto _start;
}
else
{
return v___x_1431_;
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
uint8_t v___x_16345__boxed_1604_; uint8_t v___x_16348__boxed_1605_; lean_object* v_res_1606_; 
v___x_16345__boxed_1604_ = lean_unbox(v___x_1588_);
v___x_16348__boxed_1605_ = lean_unbox(v___x_1593_);
v_res_1606_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(v___x_1579_, v_matcherInfo_1580_, v___x_1581_, v___x_1582_, v_f_1583_, v_discrs_1584_, v___x_1585_, v_rel_1586_, v___x_1587_, v___x_16345__boxed_1604_, v_alpha_1589_, v___x_1590_, v_beta_1591_, v___x_1592_, v___x_16348__boxed_1605_, v___x_1594_, v___x_1595_, v___x_1596_, v_alts_1597_, v_x_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
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
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___f_1635_; lean_object* v___x_1636_; 
v___x_1631_ = l_Lean_mkAppN(v___x_1607_, v_discrs_1624_);
v___x_1632_ = l_Lean_mkAppN(v___x_1608_, v_discrs_1624_);
v___x_1633_ = lean_box(v___x_1615_);
v___x_1634_ = lean_box(v___x_1620_);
lean_inc_ref(v_matcherInfo_1609_);
lean_inc_ref(v___x_1631_);
v___f_1635_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1635_, 0, v___x_1631_);
lean_closure_set(v___f_1635_, 1, v_matcherInfo_1609_);
lean_closure_set(v___f_1635_, 2, v___x_1610_);
lean_closure_set(v___f_1635_, 3, v___x_1632_);
lean_closure_set(v___f_1635_, 4, v_f_1611_);
lean_closure_set(v___f_1635_, 5, v_discrs_1624_);
lean_closure_set(v___f_1635_, 6, v___x_1612_);
lean_closure_set(v___f_1635_, 7, v_rel_1613_);
lean_closure_set(v___f_1635_, 8, v___x_1614_);
lean_closure_set(v___f_1635_, 9, v___x_1633_);
lean_closure_set(v___f_1635_, 10, v_alpha_1616_);
lean_closure_set(v___f_1635_, 11, v___x_1617_);
lean_closure_set(v___f_1635_, 12, v_beta_1618_);
lean_closure_set(v___f_1635_, 13, v___x_1619_);
lean_closure_set(v___f_1635_, 14, v___x_1634_);
lean_closure_set(v___f_1635_, 15, v___x_1621_);
lean_closure_set(v___f_1635_, 16, v___x_1622_);
lean_closure_set(v___f_1635_, 17, v___x_1623_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc(v___y_1627_);
lean_inc_ref(v___y_1626_);
v___x_1636_ = lean_infer_type(v___x_1631_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_matcherInfo_1609_);
lean_dec_ref(v_matcherInfo_1609_);
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
v___x_1640_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1637_, v___x_1639_, v___f_1635_, v___x_1620_, v___x_1620_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1640_;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v___f_1635_);
lean_dec_ref(v_matcherInfo_1609_);
v_a_1641_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1636_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1636_);
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
uint8_t v___x_16626__boxed_1673_; uint8_t v___x_16629__boxed_1674_; lean_object* v_res_1675_; 
v___x_16626__boxed_1673_ = lean_unbox(v___x_1657_);
v___x_16629__boxed_1674_ = lean_unbox(v___x_1662_);
v_res_1675_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(v___x_1649_, v___x_1650_, v_matcherInfo_1651_, v___x_1652_, v_f_1653_, v___x_1654_, v_rel_1655_, v___x_1656_, v___x_16626__boxed_1673_, v_alpha_1658_, v___x_1659_, v_beta_1660_, v___x_1661_, v___x_16629__boxed_1674_, v___x_1663_, v___x_1664_, v___x_1665_, v_discrs_1666_, v_x_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
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
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; 
v___x_1721_ = lean_box(v___x_1700_);
v___x_1722_ = lean_box(v___x_1702_);
lean_inc_ref(v_alpha_1701_);
lean_inc_ref(v_beta_1699_);
lean_inc(v___x_1698_);
lean_inc_ref(v_rel_1715_);
lean_inc_ref(v___x_1697_);
lean_inc_ref_n(v___x_1696_, 2);
v___f_1723_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed), 15, 8);
lean_closure_set(v___f_1723_, 0, v___x_1696_);
lean_closure_set(v___f_1723_, 1, v___x_1697_);
lean_closure_set(v___f_1723_, 2, v_rel_1715_);
lean_closure_set(v___f_1723_, 3, v___x_1698_);
lean_closure_set(v___f_1723_, 4, v_beta_1699_);
lean_closure_set(v___f_1723_, 5, v___x_1721_);
lean_closure_set(v___f_1723_, 6, v_alpha_1701_);
lean_closure_set(v___f_1723_, 7, v___x_1722_);
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1718_);
lean_inc(v___y_1717_);
lean_inc_ref(v___y_1716_);
v___x_1724_ = lean_infer_type(v___x_1696_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1725_, v___f_1723_, v___x_1702_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
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
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___f_1750_; lean_object* v___x_1751_; 
lean_inc(v_matcherName_1708_);
v___x_1741_ = l_Lean_Expr_const___override(v_matcherName_1708_, v_matcherLevels_1736_);
v___x_1742_ = l_Lean_Expr_const___override(v_matcherName_1708_, v___x_1734_);
v___x_1743_ = l_Subarray_copy___redArg(v___x_1709_);
v___x_1744_ = l_Lean_mkAppN(v___x_1741_, v___x_1743_);
v___x_1745_ = l_Lean_mkAppN(v___x_1742_, v___x_1743_);
v___x_1746_ = l_Lean_Expr_app___override(v___x_1744_, v_a_1727_);
lean_inc_ref(v___x_1696_);
v___x_1747_ = l_Lean_Expr_app___override(v___x_1745_, v___x_1696_);
v___x_1748_ = lean_box(v___x_1700_);
v___x_1749_ = lean_box(v___x_1702_);
lean_inc_ref(v___x_1746_);
v___f_1750_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed), 24, 17);
lean_closure_set(v___f_1750_, 0, v___x_1746_);
lean_closure_set(v___f_1750_, 1, v___x_1747_);
lean_closure_set(v___f_1750_, 2, v_matcherInfo_1710_);
lean_closure_set(v___f_1750_, 3, v___x_1711_);
lean_closure_set(v___f_1750_, 4, v_f_1712_);
lean_closure_set(v___f_1750_, 5, v___x_1697_);
lean_closure_set(v___f_1750_, 6, v_rel_1715_);
lean_closure_set(v___f_1750_, 7, v___x_1698_);
lean_closure_set(v___f_1750_, 8, v___x_1748_);
lean_closure_set(v___f_1750_, 9, v_alpha_1701_);
lean_closure_set(v___f_1750_, 10, v___x_1696_);
lean_closure_set(v___f_1750_, 11, v_beta_1699_);
lean_closure_set(v___f_1750_, 12, v___x_1743_);
lean_closure_set(v___f_1750_, 13, v___x_1749_);
lean_closure_set(v___f_1750_, 14, v___x_1713_);
lean_closure_set(v___f_1750_, 15, v___x_1733_);
lean_closure_set(v___f_1750_, 16, v___x_1730_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
v___x_1751_ = lean_infer_type(v___x_1746_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_numDiscrs_1703_);
v___x_1754_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1752_, v___x_1753_, v___f_1750_, v___x_1702_, v___x_1702_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
return v___x_1754_;
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v___f_1750_);
lean_dec(v_numDiscrs_1703_);
v_a_1755_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1751_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1751_);
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
lean_dec_ref(v___f_1723_);
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
v_a_1790_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1724_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1724_);
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
uint8_t v___x_16754__boxed_1823_; uint8_t v___x_16755__boxed_1824_; lean_object* v_res_1825_; 
v___x_16754__boxed_1823_ = lean_unbox(v___x_1802_);
v___x_16755__boxed_1824_ = lean_unbox(v___x_1804_);
v_res_1825_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(v___x_1798_, v___x_1799_, v___x_1800_, v_beta_1801_, v___x_16754__boxed_1823_, v_alpha_1803_, v___x_16755__boxed_1824_, v_numDiscrs_1805_, v___f_1806_, v_a_1807_, v_a_1808_, v_levelParams_1809_, v_matcherName_1810_, v___x_1811_, v_matcherInfo_1812_, v___x_1813_, v_f_1814_, v___x_1815_, v_uElimPos_x3f_1816_, v_rel_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(lean_object* v___x_1906_, lean_object* v___x_1907_, lean_object* v___x_1908_, lean_object* v_beta_1909_, uint8_t v___x_1910_, lean_object* v_alpha_1911_, lean_object* v_numDiscrs_1912_, lean_object* v___f_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_levelParams_1916_, lean_object* v_matcherName_1917_, lean_object* v___x_1918_, lean_object* v_matcherInfo_1919_, lean_object* v___x_1920_, lean_object* v___x_1921_, lean_object* v_uElimPos_x3f_1922_, lean_object* v___f_1923_, lean_object* v_f_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
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
lean_object* v_a_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___f_1935_; lean_object* v___x_1936_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1932_ = 0;
v___x_1933_ = lean_box(v___x_1910_);
v___x_1934_ = lean_box(v___x_1932_);
v___f_1935_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed), 25, 19);
lean_closure_set(v___f_1935_, 0, v___x_1906_);
lean_closure_set(v___f_1935_, 1, v___x_1907_);
lean_closure_set(v___f_1935_, 2, v___x_1908_);
lean_closure_set(v___f_1935_, 3, v_beta_1909_);
lean_closure_set(v___f_1935_, 4, v___x_1933_);
lean_closure_set(v___f_1935_, 5, v_alpha_1911_);
lean_closure_set(v___f_1935_, 6, v___x_1934_);
lean_closure_set(v___f_1935_, 7, v_numDiscrs_1912_);
lean_closure_set(v___f_1935_, 8, v___f_1913_);
lean_closure_set(v___f_1935_, 9, v_a_1914_);
lean_closure_set(v___f_1935_, 10, v_a_1915_);
lean_closure_set(v___f_1935_, 11, v_levelParams_1916_);
lean_closure_set(v___f_1935_, 12, v_matcherName_1917_);
lean_closure_set(v___f_1935_, 13, v___x_1918_);
lean_closure_set(v___f_1935_, 14, v_matcherInfo_1919_);
lean_closure_set(v___f_1935_, 15, v___x_1920_);
lean_closure_set(v___f_1935_, 16, v_f_1924_);
lean_closure_set(v___f_1935_, 17, v___x_1921_);
lean_closure_set(v___f_1935_, 18, v_uElimPos_x3f_1922_);
v___x_1936_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1931_, v___f_1923_, v___x_1932_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__1));
v___x_1939_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_1938_, v_a_1937_, v___f_1935_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
return v___x_1939_;
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec_ref(v___f_1935_);
v_a_1940_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1936_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1936_);
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
lean_dec_ref(v___f_1923_);
lean_dec(v_uElimPos_x3f_1922_);
lean_dec(v___x_1921_);
lean_dec(v___x_1920_);
lean_dec_ref(v_matcherInfo_1919_);
lean_dec_ref(v___x_1918_);
lean_dec(v_matcherName_1917_);
lean_dec(v_levelParams_1916_);
lean_dec(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec_ref(v___f_1913_);
lean_dec(v_numDiscrs_1912_);
lean_dec_ref(v_alpha_1911_);
lean_dec_ref(v_beta_1909_);
lean_dec(v___x_1908_);
lean_dec_ref(v___x_1907_);
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
lean_object* v___x_1957_ = _args[1];
lean_object* v___x_1958_ = _args[2];
lean_object* v_beta_1959_ = _args[3];
lean_object* v___x_1960_ = _args[4];
lean_object* v_alpha_1961_ = _args[5];
lean_object* v_numDiscrs_1962_ = _args[6];
lean_object* v___f_1963_ = _args[7];
lean_object* v_a_1964_ = _args[8];
lean_object* v_a_1965_ = _args[9];
lean_object* v_levelParams_1966_ = _args[10];
lean_object* v_matcherName_1967_ = _args[11];
lean_object* v___x_1968_ = _args[12];
lean_object* v_matcherInfo_1969_ = _args[13];
lean_object* v___x_1970_ = _args[14];
lean_object* v___x_1971_ = _args[15];
lean_object* v_uElimPos_x3f_1972_ = _args[16];
lean_object* v___f_1973_ = _args[17];
lean_object* v_f_1974_ = _args[18];
lean_object* v___y_1975_ = _args[19];
lean_object* v___y_1976_ = _args[20];
lean_object* v___y_1977_ = _args[21];
lean_object* v___y_1978_ = _args[22];
lean_object* v___y_1979_ = _args[23];
_start:
{
uint8_t v___x_17057__boxed_1980_; lean_object* v_res_1981_; 
v___x_17057__boxed_1980_ = lean_unbox(v___x_1960_);
v_res_1981_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(v___x_1956_, v___x_1957_, v___x_1958_, v_beta_1959_, v___x_17057__boxed_1980_, v_alpha_1961_, v_numDiscrs_1962_, v___f_1963_, v_a_1964_, v_a_1965_, v_levelParams_1966_, v_matcherName_1967_, v___x_1968_, v_matcherInfo_1969_, v___x_1970_, v___x_1971_, v_uElimPos_x3f_1972_, v___f_1973_, v_f_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
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
lean_closure_set(v___f_2016_, 1, v___x_2010_);
lean_closure_set(v___f_2016_, 2, v___x_1991_);
lean_closure_set(v___f_2016_, 3, v_beta_2002_);
lean_closure_set(v___f_2016_, 4, v___x_2015_);
lean_closure_set(v___f_2016_, 5, v_alpha_1989_);
lean_closure_set(v___f_2016_, 6, v_numDiscrs_1992_);
lean_closure_set(v___f_2016_, 7, v___f_1993_);
lean_closure_set(v___f_2016_, 8, v_a_1994_);
lean_closure_set(v___f_2016_, 9, v_a_1995_);
lean_closure_set(v___f_2016_, 10, v_levelParams_1996_);
lean_closure_set(v___f_2016_, 11, v_matcherName_1997_);
lean_closure_set(v___f_2016_, 12, v___x_1998_);
lean_closure_set(v___f_2016_, 13, v_matcherInfo_1999_);
lean_closure_set(v___f_2016_, 14, v___x_1988_);
lean_closure_set(v___f_2016_, 15, v___x_2000_);
lean_closure_set(v___f_2016_, 16, v_uElimPos_x3f_2001_);
lean_closure_set(v___f_2016_, 17, v___f_2014_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(lean_object* v___x_2043_, lean_object* v___x_2044_, lean_object* v___x_2045_, lean_object* v_numDiscrs_2046_, lean_object* v___f_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_levelParams_2050_, lean_object* v_matcherName_2051_, lean_object* v___x_2052_, lean_object* v_matcherInfo_2053_, lean_object* v___x_2054_, lean_object* v_uElimPos_x3f_2055_, lean_object* v_alpha_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___f_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_inc(v_a_2048_);
lean_inc_ref(v_alpha_2056_);
v___f_2062_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed), 20, 14);
lean_closure_set(v___f_2062_, 0, v___x_2043_);
lean_closure_set(v___f_2062_, 1, v_alpha_2056_);
lean_closure_set(v___f_2062_, 2, v___x_2044_);
lean_closure_set(v___f_2062_, 3, v___x_2045_);
lean_closure_set(v___f_2062_, 4, v_numDiscrs_2046_);
lean_closure_set(v___f_2062_, 5, v___f_2047_);
lean_closure_set(v___f_2062_, 6, v_a_2048_);
lean_closure_set(v___f_2062_, 7, v_a_2049_);
lean_closure_set(v___f_2062_, 8, v_levelParams_2050_);
lean_closure_set(v___f_2062_, 9, v_matcherName_2051_);
lean_closure_set(v___f_2062_, 10, v___x_2052_);
lean_closure_set(v___f_2062_, 11, v_matcherInfo_2053_);
lean_closure_set(v___f_2062_, 12, v___x_2054_);
lean_closure_set(v___f_2062_, 13, v_uElimPos_x3f_2055_);
v___x_2063_ = l_Lean_Level_param___override(v_a_2048_);
v___x_2064_ = l_Lean_Expr_sort___override(v___x_2063_);
v___x_2065_ = l_Lean_mkArrow(v_alpha_2056_, v___x_2064_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__1));
v___x_2068_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2067_, v_a_2066_, v___f_2062_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
return v___x_2068_;
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec_ref(v___f_2062_);
v_a_2069_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2065_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2065_);
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
lean_object* v___x_2077_ = _args[0];
lean_object* v___x_2078_ = _args[1];
lean_object* v___x_2079_ = _args[2];
lean_object* v_numDiscrs_2080_ = _args[3];
lean_object* v___f_2081_ = _args[4];
lean_object* v_a_2082_ = _args[5];
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
v_res_2096_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(v___x_2077_, v___x_2078_, v___x_2079_, v_numDiscrs_2080_, v___f_2081_, v_a_2082_, v_a_2083_, v_levelParams_2084_, v_matcherName_2085_, v___x_2086_, v_matcherInfo_2087_, v___x_2088_, v_uElimPos_x3f_2089_, v_alpha_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
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
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2123_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2106_);
lean_inc_ref(v_xs_2116_);
v___x_2124_ = l_Array_toSubarray___redArg(v_xs_2116_, v___x_2123_, v_numParams_2106_);
v___x_2125_ = lean_array_get(v___x_2107_, v_xs_2116_, v_numParams_2106_);
lean_dec(v_numParams_2106_);
lean_dec_ref(v_xs_2116_);
v___x_2126_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__1));
v___x_2127_ = l_Lean_Core_mkFreshUserName(v___x_2126_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___x_2129_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__3));
v___x_2130_ = l_Lean_Core_mkFreshUserName(v___x_2129_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___f_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
lean_inc(v_a_2128_);
v___f_2132_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed), 19, 13);
lean_closure_set(v___f_2132_, 0, v___x_2123_);
lean_closure_set(v___f_2132_, 1, v___x_2125_);
lean_closure_set(v___f_2132_, 2, v___x_2108_);
lean_closure_set(v___f_2132_, 3, v_numDiscrs_2109_);
lean_closure_set(v___f_2132_, 4, v___f_2110_);
lean_closure_set(v___f_2132_, 5, v_a_2131_);
lean_closure_set(v___f_2132_, 6, v_a_2128_);
lean_closure_set(v___f_2132_, 7, v_levelParams_2111_);
lean_closure_set(v___f_2132_, 8, v_matcherName_2112_);
lean_closure_set(v___f_2132_, 9, v___x_2124_);
lean_closure_set(v___f_2132_, 10, v_matcherInfo_2113_);
lean_closure_set(v___f_2132_, 11, v___x_2114_);
lean_closure_set(v___f_2132_, 12, v_uElimPos_x3f_2115_);
v___x_2133_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__5));
v___x_2134_ = l_Lean_Level_param___override(v_a_2128_);
v___x_2135_ = l_Lean_Expr_sort___override(v___x_2134_);
v___x_2136_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2133_, v___x_2135_, v___f_2132_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
return v___x_2136_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_a_2128_);
lean_dec(v___x_2125_);
lean_dec_ref(v___x_2124_);
lean_dec(v_uElimPos_x3f_2115_);
lean_dec(v___x_2114_);
lean_dec_ref(v_matcherInfo_2113_);
lean_dec(v_matcherName_2112_);
lean_dec(v_levelParams_2111_);
lean_dec_ref(v___f_2110_);
lean_dec(v_numDiscrs_2109_);
lean_dec(v___x_2108_);
v_a_2137_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2130_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2130_);
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
lean_dec(v___x_2125_);
lean_dec_ref(v___x_2124_);
lean_dec(v_uElimPos_x3f_2115_);
lean_dec(v___x_2114_);
lean_dec_ref(v_matcherInfo_2113_);
lean_dec(v_matcherName_2112_);
lean_dec(v_levelParams_2111_);
lean_dec_ref(v___f_2110_);
lean_dec(v_numDiscrs_2109_);
lean_dec(v___x_2108_);
v_a_2145_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2127_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2127_);
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
lean_object* v_toCold_2178_; lean_object* v_currRecDepth_2179_; lean_object* v_ref_2180_; uint16_t v_optionFlags_2181_; uint8_t v_suppressElabErrors_2182_; uint8_t v_checkDeprecated_2183_; uint8_t v_isRecordingDeps_2184_; lean_object* v_ref_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_toCold_2178_ = lean_ctor_get(v___y_2175_, 0);
v_currRecDepth_2179_ = lean_ctor_get(v___y_2175_, 1);
v_ref_2180_ = lean_ctor_get(v___y_2175_, 2);
v_optionFlags_2181_ = lean_ctor_get_uint16(v___y_2175_, sizeof(void*)*3);
v_suppressElabErrors_2182_ = lean_ctor_get_uint8(v___y_2175_, sizeof(void*)*3 + 2);
v_checkDeprecated_2183_ = lean_ctor_get_uint8(v___y_2175_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2184_ = lean_ctor_get_uint8(v___y_2175_, sizeof(void*)*3 + 4);
v_ref_2185_ = l_Lean_replaceRef(v_ref_2171_, v_ref_2180_);
lean_inc(v_currRecDepth_2179_);
lean_inc_ref(v_toCold_2178_);
v___x_2186_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2186_, 0, v_toCold_2178_);
lean_ctor_set(v___x_2186_, 1, v_currRecDepth_2179_);
lean_ctor_set(v___x_2186_, 2, v_ref_2185_);
lean_ctor_set_uint16(v___x_2186_, sizeof(void*)*3, v_optionFlags_2181_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*3 + 2, v_suppressElabErrors_2182_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*3 + 3, v_checkDeprecated_2183_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*3 + 4, v_isRecordingDeps_2184_);
v___x_2187_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_2172_, v___y_2173_, v___y_2174_, v___x_2186_, v___y_2176_);
lean_dec_ref_known(v___x_2186_, 3);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2188_, lean_object* v_msg_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2188_, v_msg_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v_ref_2188_);
return v_res_2195_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2199_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2200_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
lean_ctor_set(v___x_2202_, 2, v___x_2201_);
lean_ctor_set(v___x_2202_, 3, v___x_2201_);
lean_ctor_set(v___x_2202_, 4, v___x_2200_);
lean_ctor_set(v___x_2202_, 5, v___x_2200_);
lean_ctor_set(v___x_2202_, 6, v___x_2200_);
lean_ctor_set(v___x_2202_, 7, v___x_2200_);
lean_ctor_set(v___x_2202_, 8, v___x_2200_);
lean_ctor_set(v___x_2202_, 9, v___x_2200_);
lean_ctor_set(v___x_2202_, 10, v___x_2200_);
lean_ctor_set(v___x_2202_, 11, v___x_2199_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_unsigned_to_nat(32u);
v___x_2204_ = lean_mk_empty_array_with_capacity(v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2206_ = ((size_t)5ULL);
v___x_2207_ = lean_unsigned_to_nat(0u);
v___x_2208_ = lean_unsigned_to_nat(32u);
v___x_2209_ = lean_mk_empty_array_with_capacity(v___x_2208_);
v___x_2210_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3);
v___x_2211_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v___x_2209_);
lean_ctor_set(v___x_2211_, 2, v___x_2207_);
lean_ctor_set(v___x_2211_, 3, v___x_2207_);
lean_ctor_set_usize(v___x_2211_, 4, v___x_2206_);
return v___x_2211_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2212_ = lean_box(1);
v___x_2213_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4);
v___x_2214_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___x_2213_);
lean_ctor_set(v___x_2215_, 2, v___x_2212_);
return v___x_2215_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__6));
v___x_2218_ = l_Lean_stringToMessageData(v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__8));
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__10));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__12));
v___x_2227_ = l_Lean_stringToMessageData(v___x_2226_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__14));
v___x_2230_ = l_Lean_stringToMessageData(v___x_2229_);
return v___x_2230_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16));
v___x_2233_ = l_Lean_stringToMessageData(v___x_2232_);
return v___x_2233_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18));
v___x_2236_ = l_Lean_stringToMessageData(v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2237_, lean_object* v_declHint_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v_env_2243_; uint8_t v___x_2244_; 
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_st_ref_get(v___y_2239_);
v_env_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc_ref(v_env_2243_);
lean_dec(v___x_2242_);
v___x_2244_ = l_Lean_Name_isAnonymous(v_declHint_2238_);
if (v___x_2244_ == 0)
{
uint8_t v_isExporting_2245_; 
v_isExporting_2245_ = lean_ctor_get_uint8(v_env_2243_, sizeof(void*)*13);
if (v_isExporting_2245_ == 0)
{
lean_object* v___x_2246_; 
lean_dec_ref(v_env_2243_);
lean_dec(v_declHint_2238_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v_msg_2237_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; uint8_t v___x_2248_; 
lean_inc_ref(v_env_2243_);
v___x_2247_ = l_Lean_Environment_setExporting(v_env_2243_, v___x_2244_);
lean_inc(v_declHint_2238_);
lean_inc_ref(v___x_2247_);
v___x_2248_ = l_Lean_Environment_contains(v___x_2247_, v_declHint_2238_, v_isExporting_2245_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; 
lean_dec_ref(v___x_2247_);
lean_dec_ref(v_env_2243_);
lean_dec(v_declHint_2238_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_msg_2237_);
return v___x_2249_;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_c_2255_; lean_object* v___x_2256_; 
v___x_2250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2251_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2252_ = l_Lean_Options_empty;
lean_inc_ref(v___x_2247_);
v___x_2253_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2247_);
lean_ctor_set(v___x_2253_, 1, v___x_2250_);
lean_ctor_set(v___x_2253_, 2, v___x_2251_);
lean_ctor_set(v___x_2253_, 3, v___x_2252_);
lean_inc(v_declHint_2238_);
v___x_2254_ = l_Lean_MessageData_ofConstName(v_declHint_2238_, v___x_2244_);
v_c_2255_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2255_, 0, v___x_2253_);
lean_ctor_set(v_c_2255_, 1, v___x_2254_);
v___x_2256_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_2247_, v_declHint_2238_);
lean_dec_ref(v___x_2247_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec_ref(v_env_2243_);
lean_dec(v_declHint_2238_);
v___x_2257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v_c_2255_);
v___x_2259_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = l_Lean_MessageData_note(v___x_2260_);
v___x_2262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2262_, 0, v_msg_2237_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
return v___x_2263_;
}
else
{
lean_object* v_val_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2298_; 
v_val_2264_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2266_ = v___x_2256_;
v_isShared_2267_ = v_isSharedCheck_2298_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_val_2264_);
lean_dec(v___x_2256_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2298_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v_moduleNames_2269_; lean_object* v_mod_2270_; uint8_t v___x_2271_; 
v___x_2268_ = l_Lean_Environment_header(v_env_2243_);
lean_dec_ref(v_env_2243_);
v_moduleNames_2269_ = lean_ctor_get(v___x_2268_, 4);
lean_inc_ref(v_moduleNames_2269_);
lean_dec_ref(v___x_2268_);
v_mod_2270_ = lean_array_get(v___x_2241_, v_moduleNames_2269_, v_val_2264_);
lean_dec(v_val_2264_);
lean_dec_ref(v_moduleNames_2269_);
v___x_2271_ = l_Lean_isPrivateName(v_declHint_2238_);
lean_dec(v_declHint_2238_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2272_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v_c_2255_);
v___x_2274_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2273_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = l_Lean_MessageData_ofName(v_mod_2270_);
v___x_2277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = l_Lean_MessageData_note(v___x_2279_);
v___x_2281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2281_, 0, v_msg_2237_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2281_);
v___x_2283_ = v___x_2266_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2285_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v_c_2255_);
v___x_2287_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = l_Lean_MessageData_ofName(v_mod_2270_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = l_Lean_MessageData_note(v___x_2292_);
v___x_2294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2294_, 0, v_msg_2237_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2294_);
v___x_2296_ = v___x_2266_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2299_; 
lean_dec_ref(v_env_2243_);
lean_dec(v_declHint_2238_);
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v_msg_2237_);
return v___x_2299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2300_, lean_object* v_declHint_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2300_, v_declHint_2301_, v___y_2302_);
lean_dec(v___y_2302_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(lean_object* v_msg_2305_, lean_object* v_declHint_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2322_; 
v___x_2312_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2305_, v_declHint_2306_, v___y_2310_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2317_ = l_Lean_unknownIdentifierMessageTag;
v___x_2318_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v_a_2313_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2318_);
v___x_2320_ = v___x_2315_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11___boxed(lean_object* v_msg_2323_, lean_object* v_declHint_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2323_, v_declHint_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_ref_2331_, lean_object* v_msg_2332_, lean_object* v_declHint_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; lean_object* v_a_2340_; lean_object* v___x_2341_; 
v___x_2339_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2332_, v_declHint_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2331_, v_a_2340_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_ref_2342_, lean_object* v_msg_2343_, lean_object* v_declHint_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2342_, v_msg_2343_, v_declHint_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v_ref_2342_);
return v_res_2350_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_2353_ = l_Lean_stringToMessageData(v___x_2352_);
return v___x_2353_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_2356_ = l_Lean_stringToMessageData(v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_2357_, lean_object* v_constName_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2364_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_2365_ = 0;
lean_inc(v_constName_2358_);
v___x_2366_ = l_Lean_MessageData_ofConstName(v_constName_2358_, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2364_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2357_, v___x_2369_, v_constName_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_2371_, lean_object* v_constName_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2371_, v_constName_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v_ref_2371_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(lean_object* v_constName_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_ref_2385_; lean_object* v___x_2386_; 
v_ref_2385_ = lean_ctor_get(v___y_2382_, 2);
v___x_2386_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2385_, v_constName_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(lean_object* v_constName_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2400_; lean_object* v_env_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; 
v___x_2400_ = lean_st_ref_get(v___y_2398_);
v_env_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc_ref(v_env_2401_);
lean_dec(v___x_2400_);
v___x_2402_ = 0;
lean_inc(v_constName_2394_);
v___x_2403_ = l_Lean_Environment_findConstVal_x3f(v_env_2401_, v_constName_2394_, v___x_2402_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
return v___x_2404_;
}
else
{
lean_object* v_val_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec(v_constName_2394_);
v_val_2405_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2403_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_val_2405_);
lean_dec(v___x_2403_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
lean_ctor_set_tag(v___x_2407_, 0);
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_val_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0___boxed(lean_object* v_constName_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_constName_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(lean_object* v_matcherName_2420_, lean_object* v_matcherInfo_2421_, lean_object* v___x_2422_, lean_object* v___f_2423_, lean_object* v___x_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; 
lean_inc(v_matcherName_2420_);
v___x_2430_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_matcherName_2420_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v_levelParams_2432_; lean_object* v_type_2433_; lean_object* v_numParams_2434_; lean_object* v_numDiscrs_2435_; lean_object* v_uElimPos_x3f_2436_; lean_object* v___x_2437_; lean_object* v___f_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v_levelParams_2432_ = lean_ctor_get(v_a_2431_, 1);
lean_inc(v_levelParams_2432_);
v_type_2433_ = lean_ctor_get(v_a_2431_, 2);
lean_inc_ref(v_type_2433_);
lean_dec(v_a_2431_);
v_numParams_2434_ = lean_ctor_get(v_matcherInfo_2421_, 0);
lean_inc_n(v_numParams_2434_, 2);
v_numDiscrs_2435_ = lean_ctor_get(v_matcherInfo_2421_, 1);
lean_inc(v_numDiscrs_2435_);
v_uElimPos_x3f_2436_ = lean_ctor_get(v_matcherInfo_2421_, 3);
lean_inc(v_uElimPos_x3f_2436_);
v___x_2437_ = lean_unsigned_to_nat(1u);
v___f_2438_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed), 17, 10);
lean_closure_set(v___f_2438_, 0, v_numParams_2434_);
lean_closure_set(v___f_2438_, 1, v___x_2422_);
lean_closure_set(v___f_2438_, 2, v___x_2437_);
lean_closure_set(v___f_2438_, 3, v_numDiscrs_2435_);
lean_closure_set(v___f_2438_, 4, v___f_2423_);
lean_closure_set(v___f_2438_, 5, v_levelParams_2432_);
lean_closure_set(v___f_2438_, 6, v_matcherName_2420_);
lean_closure_set(v___f_2438_, 7, v_matcherInfo_2421_);
lean_closure_set(v___f_2438_, 8, v___x_2424_);
lean_closure_set(v___f_2438_, 9, v_uElimPos_x3f_2436_);
v___x_2439_ = lean_nat_add(v_numParams_2434_, v___x_2437_);
lean_dec(v_numParams_2434_);
v___x_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
v___x_2441_ = 0;
v___x_2442_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_2433_, v___x_2440_, v___f_2438_, v___x_2441_, v___x_2441_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
return v___x_2442_;
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec(v___x_2424_);
lean_dec_ref(v___f_2423_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v_matcherInfo_2421_);
lean_dec(v_matcherName_2420_);
v_a_2443_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2430_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2430_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed(lean_object* v_matcherName_2451_, lean_object* v_matcherInfo_2452_, lean_object* v___x_2453_, lean_object* v___f_2454_, lean_object* v___x_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(v_matcherName_2451_, v_matcherInfo_2452_, v___x_2453_, v___f_2454_, v___x_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11(lean_object* v___x_2462_, lean_object* v_e_2463_){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = l_Lean_indentD(v_e_2463_);
v___x_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2462_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(lean_object* v___f_2466_, lean_object* v___f_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2466_, v___f_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2473_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2473_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
v_a_2482_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2473_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2473_);
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
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed(lean_object* v___f_2490_, lean_object* v___f_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(v___f_2490_, v___f_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
return v_res_2497_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__3));
v___x_2504_ = l_Lean_stringToMessageData(v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(lean_object* v_matcherName_2505_, lean_object* v_matcherInfo_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v___f_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v_env_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___f_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___f_2523_; lean_object* v___f_2524_; lean_object* v___x_2525_; 
v___f_2512_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__0));
v___x_2513_ = l_Lean_instInhabitedExpr;
v___x_2514_ = lean_st_ref_get(v_a_2510_);
v_env_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc_ref(v_env_2515_);
lean_dec(v___x_2514_);
lean_inc_n(v_matcherName_2505_, 3);
v___x_2516_ = l_Lean_mkPrivateName(v_env_2515_, v_matcherName_2505_);
lean_dec_ref(v_env_2515_);
v___x_2517_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__2));
v___x_2518_ = l_Lean_Name_append(v___x_2516_, v___x_2517_);
lean_inc_n(v___x_2518_, 2);
v___f_2519_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed), 10, 5);
lean_closure_set(v___f_2519_, 0, v_matcherName_2505_);
lean_closure_set(v___f_2519_, 1, v_matcherInfo_2506_);
lean_closure_set(v___f_2519_, 2, v___x_2513_);
lean_closure_set(v___f_2519_, 3, v___f_2512_);
lean_closure_set(v___f_2519_, 4, v___x_2518_);
v___x_2520_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4);
v___x_2521_ = l_Lean_MessageData_ofName(v_matcherName_2505_);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___f_2523_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_2523_, 0, v___x_2522_);
v___f_2524_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed), 7, 2);
lean_closure_set(v___f_2524_, 0, v___f_2519_);
lean_closure_set(v___f_2524_, 1, v___f_2523_);
v___x_2525_ = l_Lean_Meta_realizeConst(v_matcherName_2505_, v___x_2518_, v___f_2524_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v___x_2525_, 0);
lean_dec(v_unused_2533_);
v___x_2527_ = v___x_2525_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_dec(v___x_2525_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2518_);
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2518_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v___x_2518_);
v_a_2534_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2525_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2525_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___boxed(lean_object* v_matcherName_2542_, lean_object* v_matcherInfo_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_2542_, v_matcherInfo_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(lean_object* v_as_2550_, lean_object* v_as_x27_2551_, lean_object* v_b_2552_, lean_object* v_a_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_2551_, v_b_2552_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___boxed(lean_object* v_as_2560_, lean_object* v_as_x27_2561_, lean_object* v_b_2562_, lean_object* v_a_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(v_as_2560_, v_as_x27_2561_, v_b_2562_, v_a_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v_as_x27_2561_);
lean_dec(v_as_2560_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(lean_object* v_00_u03b1_2570_, lean_object* v_name_2571_, uint8_t v_bi_2572_, lean_object* v_type_2573_, lean_object* v_k_2574_, uint8_t v_kind_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_2571_, v_bi_2572_, v_type_2573_, v_k_2574_, v_kind_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2582_, lean_object* v_name_2583_, lean_object* v_bi_2584_, lean_object* v_type_2585_, lean_object* v_k_2586_, lean_object* v_kind_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
uint8_t v_bi_boxed_2593_; uint8_t v_kind_boxed_2594_; lean_object* v_res_2595_; 
v_bi_boxed_2593_ = lean_unbox(v_bi_2584_);
v_kind_boxed_2594_ = lean_unbox(v_kind_2587_);
v_res_2595_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(v_00_u03b1_2582_, v_name_2583_, v_bi_boxed_2593_, v_type_2585_, v_k_2586_, v_kind_boxed_2594_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(lean_object* v_00_u03b1_2596_, lean_object* v_name_2597_, lean_object* v_type_2598_, lean_object* v_k_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_2597_, v_type_2598_, v_k_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___boxed(lean_object* v_00_u03b1_2606_, lean_object* v_name_2607_, lean_object* v_type_2608_, lean_object* v_k_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(v_00_u03b1_2606_, v_name_2607_, v_type_2608_, v_k_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(lean_object* v_00_u03b1_2616_, lean_object* v_constName_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2624_, lean_object* v_constName_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(v_00_u03b1_2624_, v_constName_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2632_, lean_object* v_ref_2633_, lean_object* v_constName_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2633_, v_constName_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2641_, lean_object* v_ref_2642_, lean_object* v_constName_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(v_00_u03b1_2641_, v_ref_2642_, v_constName_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v_ref_2642_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b1_2650_, lean_object* v_ref_2651_, lean_object* v_msg_2652_, lean_object* v_declHint_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2651_, v_msg_2652_, v_declHint_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b1_2660_, lean_object* v_ref_2661_, lean_object* v_msg_2662_, lean_object* v_declHint_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(v_00_u03b1_2660_, v_ref_2661_, v_msg_2662_, v_declHint_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v_ref_2661_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(lean_object* v_msg_2670_, lean_object* v_declHint_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2670_, v_declHint_2671_, v___y_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_2678_, lean_object* v_declHint_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(v_msg_2678_, v_declHint_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_2686_, lean_object* v_ref_2687_, lean_object* v_msg_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2687_, v_msg_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_2695_, lean_object* v_ref_2696_, lean_object* v_msg_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(v_00_u03b1_2695_, v_ref_2696_, v_msg_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v_ref_2696_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(lean_object* v_msg_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___f_2714_; lean_object* v___x_34404__overap_2715_; lean_object* v___x_2716_; 
v___f_2714_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0));
v___x_34404__overap_2715_ = lean_panic_fn_borrowed(v___f_2714_, v_msg_2705_);
lean_inc(v___y_2712_);
lean_inc_ref(v___y_2711_);
lean_inc(v___y_2710_);
lean_inc_ref(v___y_2709_);
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
lean_inc(v___y_2706_);
v___x_2716_ = lean_apply_8(v___x_34404__overap_2715_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, lean_box(0));
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___boxed(lean_object* v_msg_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v_msg_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(lean_object* v_k_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v_b_2731_, lean_object* v_c_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; 
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
lean_inc(v___y_2728_);
v___x_2738_ = lean_apply_10(v_k_2727_, v_b_2731_, v_c_2732_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed(lean_object* v_k_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v_b_2743_, lean_object* v_c_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(v_k_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v_b_2743_, v_c_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(lean_object* v_e_2751_, lean_object* v_k_2752_, uint8_t v_cleanupAnnotations_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___f_2762_; uint8_t v___x_2763_; uint8_t v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_inc(v___y_2756_);
lean_inc_ref(v___y_2755_);
lean_inc(v___y_2754_);
v___f_2762_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2762_, 0, v_k_2752_);
lean_closure_set(v___f_2762_, 1, v___y_2754_);
lean_closure_set(v___f_2762_, 2, v___y_2755_);
lean_closure_set(v___f_2762_, 3, v___y_2756_);
v___x_2763_ = 1;
v___x_2764_ = 0;
v___x_2765_ = lean_box(0);
v___x_2766_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2751_, v___x_2763_, v___x_2764_, v___x_2763_, v___x_2764_, v___x_2765_, v___f_2762_, v_cleanupAnnotations_2753_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2766_) == 0)
{
return v___x_2766_;
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2766_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___boxed(lean_object* v_e_2775_, lean_object* v_k_2776_, lean_object* v_cleanupAnnotations_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2786_; lean_object* v_res_2787_; 
v_cleanupAnnotations_boxed_2786_ = lean_unbox(v_cleanupAnnotations_2777_);
v_res_2787_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2775_, v_k_2776_, v_cleanupAnnotations_boxed_2786_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(lean_object* v_00_u03b1_2788_, lean_object* v_e_2789_, lean_object* v_k_2790_, uint8_t v_cleanupAnnotations_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2789_, v_k_2790_, v_cleanupAnnotations_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___boxed(lean_object* v_00_u03b1_2801_, lean_object* v_e_2802_, lean_object* v_k_2803_, lean_object* v_cleanupAnnotations_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2813_; lean_object* v_res_2814_; 
v_cleanupAnnotations_boxed_2813_ = lean_unbox(v_cleanupAnnotations_2804_);
v_res_2814_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(v_00_u03b1_2801_, v_e_2802_, v_k_2803_, v_cleanupAnnotations_boxed_2813_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(uint8_t v___x_2815_, uint8_t v___x_2816_, uint8_t v___x_2817_, lean_object* v_xs_2818_, lean_object* v_motiveBody_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; lean_object* v___x_2835_; 
v___x_2828_ = l_Lean_Expr_bindingDomain_x21(v_motiveBody_2819_);
v___x_2829_ = l_Lean_Expr_bindingName_x21(v___x_2828_);
v___x_2830_ = l_Lean_Expr_bindingDomain_x21(v___x_2828_);
v___x_2831_ = l_Lean_Expr_bindingBody_x21(v___x_2828_);
lean_dec_ref(v___x_2828_);
v___x_2832_ = l_Lean_Expr_bindingDomain_x21(v___x_2831_);
lean_dec_ref(v___x_2831_);
v___x_2833_ = l_Lean_Expr_lam___override(v___x_2829_, v___x_2830_, v___x_2832_, v___x_2815_);
v___x_2834_ = 1;
v___x_2835_ = l_Lean_Meta_mkLambdaFVars(v_xs_2818_, v___x_2833_, v___x_2816_, v___x_2817_, v___x_2816_, v___x_2817_, v___x_2834_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed(lean_object* v___x_2836_, lean_object* v___x_2837_, lean_object* v___x_2838_, lean_object* v_xs_2839_, lean_object* v_motiveBody_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v___x_41872__boxed_2849_; uint8_t v___x_41873__boxed_2850_; uint8_t v___x_41874__boxed_2851_; lean_object* v_res_2852_; 
v___x_41872__boxed_2849_ = lean_unbox(v___x_2836_);
v___x_41873__boxed_2850_ = lean_unbox(v___x_2837_);
v___x_41874__boxed_2851_ = lean_unbox(v___x_2838_);
v_res_2852_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(v___x_41872__boxed_2849_, v___x_41873__boxed_2850_, v___x_41874__boxed_2851_, v_xs_2839_, v_motiveBody_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v_motiveBody_2840_);
lean_dec_ref(v_xs_2839_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(size_t v_sz_2853_, size_t v_i_2854_, lean_object* v_bs_2855_){
_start:
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_usize_dec_lt(v_i_2854_, v_sz_2853_);
if (v___x_2856_ == 0)
{
return v_bs_2855_;
}
else
{
lean_object* v_v_2857_; lean_object* v___x_2858_; lean_object* v_bs_x27_2859_; lean_object* v___x_2860_; size_t v___x_2861_; size_t v___x_2862_; lean_object* v___x_2863_; 
v_v_2857_ = lean_array_uget(v_bs_2855_, v_i_2854_);
v___x_2858_ = lean_unsigned_to_nat(0u);
v_bs_x27_2859_ = lean_array_uset(v_bs_2855_, v_i_2854_, v___x_2858_);
v___x_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_v_2857_);
v___x_2861_ = ((size_t)1ULL);
v___x_2862_ = lean_usize_add(v_i_2854_, v___x_2861_);
v___x_2863_ = lean_array_uset(v_bs_x27_2859_, v_i_2854_, v___x_2860_);
v_i_2854_ = v___x_2862_;
v_bs_2855_ = v___x_2863_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4___boxed(lean_object* v_sz_2865_, lean_object* v_i_2866_, lean_object* v_bs_2867_){
_start:
{
size_t v_sz_boxed_2868_; size_t v_i_boxed_2869_; lean_object* v_res_2870_; 
v_sz_boxed_2868_ = lean_unbox_usize(v_sz_2865_);
lean_dec(v_sz_2865_);
v_i_boxed_2869_ = lean_unbox_usize(v_i_2866_);
lean_dec(v_i_2866_);
v_res_2870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_boxed_2868_, v_i_boxed_2869_, v_bs_2867_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(lean_object* v_msg_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_ref_2877_; lean_object* v___x_2878_; lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2887_; 
v_ref_2877_ = lean_ctor_get(v___y_2874_, 2);
v___x_2878_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
lean_inc(v_ref_2877_);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_ref_2877_);
lean_ctor_set(v___x_2883_, 1, v_a_2879_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set_tag(v___x_2881_, 1);
lean_ctor_set(v___x_2881_, 0, v___x_2883_);
v___x_2885_ = v___x_2881_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg___boxed(lean_object* v_msg_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(lean_object* v_declName_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v_env_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2898_ = lean_st_ref_get(v___y_2896_);
v_env_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc_ref(v_env_2899_);
lean_dec(v___x_2898_);
v___x_2900_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2899_, v_declName_2895_);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg___boxed(lean_object* v_declName_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_2902_, v___y_2903_);
lean_dec(v___y_2903_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(lean_object* v_ref_2906_, lean_object* v_msg_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_toCold_2916_; lean_object* v_currRecDepth_2917_; lean_object* v_ref_2918_; uint16_t v_optionFlags_2919_; uint8_t v_suppressElabErrors_2920_; uint8_t v_checkDeprecated_2921_; uint8_t v_isRecordingDeps_2922_; lean_object* v_ref_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v_toCold_2916_ = lean_ctor_get(v___y_2913_, 0);
v_currRecDepth_2917_ = lean_ctor_get(v___y_2913_, 1);
v_ref_2918_ = lean_ctor_get(v___y_2913_, 2);
v_optionFlags_2919_ = lean_ctor_get_uint16(v___y_2913_, sizeof(void*)*3);
v_suppressElabErrors_2920_ = lean_ctor_get_uint8(v___y_2913_, sizeof(void*)*3 + 2);
v_checkDeprecated_2921_ = lean_ctor_get_uint8(v___y_2913_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2922_ = lean_ctor_get_uint8(v___y_2913_, sizeof(void*)*3 + 4);
v_ref_2923_ = l_Lean_replaceRef(v_ref_2906_, v_ref_2918_);
lean_inc(v_currRecDepth_2917_);
lean_inc_ref(v_toCold_2916_);
v___x_2924_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2924_, 0, v_toCold_2916_);
lean_ctor_set(v___x_2924_, 1, v_currRecDepth_2917_);
lean_ctor_set(v___x_2924_, 2, v_ref_2923_);
lean_ctor_set_uint16(v___x_2924_, sizeof(void*)*3, v_optionFlags_2919_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*3 + 2, v_suppressElabErrors_2920_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*3 + 3, v_checkDeprecated_2921_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*3 + 4, v_isRecordingDeps_2922_);
v___x_2925_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2907_, v___y_2911_, v___y_2912_, v___x_2924_, v___y_2914_);
lean_dec_ref_known(v___x_2924_, 3);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2926_, lean_object* v_msg_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_2926_, v_msg_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec(v_ref_2926_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2937_, lean_object* v_declHint_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v_env_2943_; uint8_t v___x_2944_; 
v___x_2941_ = lean_box(0);
v___x_2942_ = lean_st_ref_get(v___y_2939_);
v_env_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc_ref(v_env_2943_);
lean_dec(v___x_2942_);
v___x_2944_ = l_Lean_Name_isAnonymous(v_declHint_2938_);
if (v___x_2944_ == 0)
{
uint8_t v_isExporting_2945_; 
v_isExporting_2945_ = lean_ctor_get_uint8(v_env_2943_, sizeof(void*)*13);
if (v_isExporting_2945_ == 0)
{
lean_object* v___x_2946_; 
lean_dec_ref(v_env_2943_);
lean_dec(v_declHint_2938_);
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v_msg_2937_);
return v___x_2946_;
}
else
{
lean_object* v___x_2947_; uint8_t v___x_2948_; 
lean_inc_ref(v_env_2943_);
v___x_2947_ = l_Lean_Environment_setExporting(v_env_2943_, v___x_2944_);
lean_inc(v_declHint_2938_);
lean_inc_ref(v___x_2947_);
v___x_2948_ = l_Lean_Environment_contains(v___x_2947_, v_declHint_2938_, v_isExporting_2945_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_env_2943_);
lean_dec(v_declHint_2938_);
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_msg_2937_);
return v___x_2949_;
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v_c_2957_; lean_object* v___x_2958_; 
v___x_2950_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2951_ = lean_unsigned_to_nat(32u);
v___x_2952_ = lean_mk_empty_array_with_capacity(v___x_2951_);
lean_dec_ref(v___x_2952_);
v___x_2953_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2954_ = l_Lean_Options_empty;
lean_inc_ref(v___x_2947_);
v___x_2955_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2947_);
lean_ctor_set(v___x_2955_, 1, v___x_2950_);
lean_ctor_set(v___x_2955_, 2, v___x_2953_);
lean_ctor_set(v___x_2955_, 3, v___x_2954_);
lean_inc(v_declHint_2938_);
v___x_2956_ = l_Lean_MessageData_ofConstName(v_declHint_2938_, v___x_2944_);
v_c_2957_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2957_, 0, v___x_2955_);
lean_ctor_set(v_c_2957_, 1, v___x_2956_);
v___x_2958_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_2947_, v_declHint_2938_);
lean_dec_ref(v___x_2947_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref(v_env_2943_);
lean_dec(v_declHint_2938_);
v___x_2959_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v_c_2957_);
v___x_2961_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2960_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = l_Lean_MessageData_note(v___x_2962_);
v___x_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_msg_2937_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
else
{
lean_object* v_val_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3000_; 
v_val_2966_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2968_ = v___x_2958_;
v_isShared_2969_ = v_isSharedCheck_3000_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_val_2966_);
lean_dec(v___x_2958_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_3000_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v_moduleNames_2971_; lean_object* v_mod_2972_; uint8_t v___x_2973_; 
v___x_2970_ = l_Lean_Environment_header(v_env_2943_);
lean_dec_ref(v_env_2943_);
v_moduleNames_2971_ = lean_ctor_get(v___x_2970_, 4);
lean_inc_ref(v_moduleNames_2971_);
lean_dec_ref(v___x_2970_);
v_mod_2972_ = lean_array_get(v___x_2941_, v_moduleNames_2971_, v_val_2966_);
lean_dec(v_val_2966_);
lean_dec_ref(v_moduleNames_2971_);
v___x_2973_ = l_Lean_isPrivateName(v_declHint_2938_);
lean_dec(v_declHint_2938_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2974_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
lean_ctor_set(v___x_2975_, 1, v_c_2957_);
v___x_2976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2975_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___x_2978_ = l_Lean_MessageData_ofName(v_mod_2972_);
v___x_2979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2977_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2979_);
lean_ctor_set(v___x_2981_, 1, v___x_2980_);
v___x_2982_ = l_Lean_MessageData_note(v___x_2981_);
v___x_2983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2983_, 0, v_msg_2937_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set_tag(v___x_2968_, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2983_);
v___x_2985_ = v___x_2968_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2983_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2987_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v_c_2957_);
v___x_2989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_2990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2988_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = l_Lean_MessageData_ofName(v_mod_2972_);
v___x_2992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2990_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_2994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2992_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = l_Lean_MessageData_note(v___x_2994_);
v___x_2996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2996_, 0, v_msg_2937_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set_tag(v___x_2968_, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2996_);
v___x_2998_ = v___x_2968_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3001_; 
lean_dec_ref(v_env_2943_);
lean_dec(v_declHint_2938_);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_msg_2937_);
return v___x_3001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_3002_, lean_object* v_declHint_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3002_, v_declHint_3003_, v___y_3004_);
lean_dec(v___y_3004_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(lean_object* v_msg_3007_, lean_object* v_declHint_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___x_3017_; lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3027_; 
v___x_3017_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3007_, v_declHint_3008_, v___y_3015_);
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3027_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3027_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3022_ = l_Lean_unknownIdentifierMessageTag;
v___x_3023_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
lean_ctor_set(v___x_3023_, 1, v_a_3018_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3023_);
v___x_3025_ = v___x_3020_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11___boxed(lean_object* v_msg_3028_, lean_object* v_declHint_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3028_, v_declHint_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object* v_ref_3039_, lean_object* v_msg_3040_, lean_object* v_declHint_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v_a_3051_; lean_object* v___x_3052_; 
v___x_3050_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3040_, v_declHint_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref(v___x_3050_);
v___x_3052_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3039_, v_a_3051_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_ref_3053_, lean_object* v_msg_3054_, lean_object* v_declHint_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3053_, v_msg_3054_, v_declHint_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec(v_ref_3053_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(lean_object* v_ref_3065_, lean_object* v_constName_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v___x_3075_; uint8_t v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3075_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3076_ = 0;
lean_inc(v_constName_3066_);
v___x_3077_ = l_Lean_MessageData_ofConstName(v_constName_3066_, v___x_3076_);
v___x_3078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3075_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3078_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3065_, v___x_3080_, v_constName_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_ref_3082_, lean_object* v_constName_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3082_, v_constName_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec(v_ref_3082_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v_ref_3102_; lean_object* v___x_3103_; 
v_ref_3102_ = lean_ctor_get(v___y_3099_, 2);
v___x_3103_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3102_, v_constName_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(lean_object* v_constName_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v___x_3123_; lean_object* v_env_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; 
v___x_3123_ = lean_st_ref_get(v___y_3121_);
v_env_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc_ref(v_env_3124_);
lean_dec(v___x_3123_);
v___x_3125_ = 0;
lean_inc(v_constName_3114_);
v___x_3126_ = l_Lean_Environment_find_x3f(v_env_3124_, v_constName_3114_, v___x_3125_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
return v___x_3127_;
}
else
{
lean_object* v_val_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec(v_constName_3114_);
v_val_3128_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3126_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_val_3128_);
lean_dec(v___x_3126_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set_tag(v___x_3130_, 0);
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_val_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0___boxed(lean_object* v_constName_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_constName_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3137_);
return v_res_3145_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_instMonadEIO___redArg();
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(lean_object* v_msg_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v_toApplicative_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3226_; 
v___x_3160_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0);
v___x_3161_ = l_StateRefT_x27_instMonad___redArg(v___x_3160_);
v_toApplicative_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v___x_3161_, 1);
lean_dec(v_unused_3227_);
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3226_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_toApplicative_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3226_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v_toFunctor_3166_; lean_object* v_toSeq_3167_; lean_object* v_toSeqLeft_3168_; lean_object* v_toSeqRight_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3224_; 
v_toFunctor_3166_ = lean_ctor_get(v_toApplicative_3162_, 0);
v_toSeq_3167_ = lean_ctor_get(v_toApplicative_3162_, 2);
v_toSeqLeft_3168_ = lean_ctor_get(v_toApplicative_3162_, 3);
v_toSeqRight_3169_ = lean_ctor_get(v_toApplicative_3162_, 4);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_toApplicative_3162_);
if (v_isSharedCheck_3224_ == 0)
{
lean_object* v_unused_3225_; 
v_unused_3225_ = lean_ctor_get(v_toApplicative_3162_, 1);
lean_dec(v_unused_3225_);
v___x_3171_ = v_toApplicative_3162_;
v_isShared_3172_ = v_isSharedCheck_3224_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_toSeqRight_3169_);
lean_inc(v_toSeqLeft_3168_);
lean_inc(v_toSeq_3167_);
lean_inc(v_toFunctor_3166_);
lean_dec(v_toApplicative_3162_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3224_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___f_3173_; lean_object* v___f_3174_; lean_object* v___f_3175_; lean_object* v___f_3176_; lean_object* v___x_3177_; lean_object* v___f_3178_; lean_object* v___f_3179_; lean_object* v___f_3180_; lean_object* v___x_3182_; 
v___f_3173_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__1));
v___f_3174_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3166_);
v___f_3175_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3175_, 0, v_toFunctor_3166_);
v___f_3176_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3176_, 0, v_toFunctor_3166_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___f_3175_);
lean_ctor_set(v___x_3177_, 1, v___f_3176_);
v___f_3178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3178_, 0, v_toSeqRight_3169_);
v___f_3179_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3179_, 0, v_toSeqLeft_3168_);
v___f_3180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3180_, 0, v_toSeq_3167_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 4, v___f_3178_);
lean_ctor_set(v___x_3171_, 3, v___f_3179_);
lean_ctor_set(v___x_3171_, 2, v___f_3180_);
lean_ctor_set(v___x_3171_, 1, v___f_3173_);
lean_ctor_set(v___x_3171_, 0, v___x_3177_);
v___x_3182_ = v___x_3171_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v___f_3173_);
lean_ctor_set(v_reuseFailAlloc_3223_, 2, v___f_3180_);
lean_ctor_set(v_reuseFailAlloc_3223_, 3, v___f_3179_);
lean_ctor_set(v_reuseFailAlloc_3223_, 4, v___f_3178_);
v___x_3182_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3184_; 
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 1, v___f_3174_);
lean_ctor_set(v___x_3164_, 0, v___x_3182_);
v___x_3184_ = v___x_3164_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3182_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v___f_3174_);
v___x_3184_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
lean_object* v___x_3185_; lean_object* v_toApplicative_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3220_; 
v___x_3185_ = l_StateRefT_x27_instMonad___redArg(v___x_3184_);
v_toApplicative_3186_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v___x_3185_, 1);
lean_dec(v_unused_3221_);
v___x_3188_ = v___x_3185_;
v_isShared_3189_ = v_isSharedCheck_3220_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_toApplicative_3186_);
lean_dec(v___x_3185_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3220_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v_toFunctor_3190_; lean_object* v_toSeq_3191_; lean_object* v_toSeqLeft_3192_; lean_object* v_toSeqRight_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3218_; 
v_toFunctor_3190_ = lean_ctor_get(v_toApplicative_3186_, 0);
v_toSeq_3191_ = lean_ctor_get(v_toApplicative_3186_, 2);
v_toSeqLeft_3192_ = lean_ctor_get(v_toApplicative_3186_, 3);
v_toSeqRight_3193_ = lean_ctor_get(v_toApplicative_3186_, 4);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_toApplicative_3186_);
if (v_isSharedCheck_3218_ == 0)
{
lean_object* v_unused_3219_; 
v_unused_3219_ = lean_ctor_get(v_toApplicative_3186_, 1);
lean_dec(v_unused_3219_);
v___x_3195_ = v_toApplicative_3186_;
v_isShared_3196_ = v_isSharedCheck_3218_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_toSeqRight_3193_);
lean_inc(v_toSeqLeft_3192_);
lean_inc(v_toSeq_3191_);
lean_inc(v_toFunctor_3190_);
lean_dec(v_toApplicative_3186_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3218_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___f_3197_; lean_object* v___f_3198_; lean_object* v___f_3199_; lean_object* v___f_3200_; lean_object* v___x_3201_; lean_object* v___f_3202_; lean_object* v___f_3203_; lean_object* v___f_3204_; lean_object* v___x_3206_; 
v___f_3197_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__3));
v___f_3198_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3190_);
v___f_3199_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3199_, 0, v_toFunctor_3190_);
v___f_3200_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3200_, 0, v_toFunctor_3190_);
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___f_3199_);
lean_ctor_set(v___x_3201_, 1, v___f_3200_);
v___f_3202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3202_, 0, v_toSeqRight_3193_);
v___f_3203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3203_, 0, v_toSeqLeft_3192_);
v___f_3204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3204_, 0, v_toSeq_3191_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 4, v___f_3202_);
lean_ctor_set(v___x_3195_, 3, v___f_3203_);
lean_ctor_set(v___x_3195_, 2, v___f_3204_);
lean_ctor_set(v___x_3195_, 1, v___f_3197_);
lean_ctor_set(v___x_3195_, 0, v___x_3201_);
v___x_3206_ = v___x_3195_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v___f_3197_);
lean_ctor_set(v_reuseFailAlloc_3217_, 2, v___f_3204_);
lean_ctor_set(v_reuseFailAlloc_3217_, 3, v___f_3203_);
lean_ctor_set(v_reuseFailAlloc_3217_, 4, v___f_3202_);
v___x_3206_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3208_; 
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 1, v___f_3198_);
lean_ctor_set(v___x_3188_, 0, v___x_3206_);
v___x_3208_ = v___x_3188_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___f_3198_);
v___x_3208_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_36481__overap_3214_; lean_object* v___x_3215_; 
v___x_3209_ = l_StateRefT_x27_instMonad___redArg(v___x_3208_);
v___x_3210_ = l_ReaderT_instMonad___redArg(v___x_3209_);
v___x_3211_ = l_ReaderT_instMonad___redArg(v___x_3210_);
v___x_3212_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3213_ = l_instInhabitedOfMonad___redArg(v___x_3211_, v___x_3212_);
v___x_36481__overap_3214_ = lean_panic_fn_borrowed(v___x_3213_, v_msg_3151_);
lean_dec(v___x_3213_);
lean_inc(v___y_3158_);
lean_inc_ref(v___y_3157_);
lean_inc(v___y_3156_);
lean_inc_ref(v___y_3155_);
lean_inc(v___y_3154_);
lean_inc_ref(v___y_3153_);
lean_inc(v___y_3152_);
v___x_3215_ = lean_apply_8(v___x_36481__overap_3214_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, lean_box(0));
return v___x_3215_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___boxed(lean_object* v_msg_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v_msg_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
return v_res_3237_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__2));
v___x_3242_ = lean_unsigned_to_nat(53u);
v___x_3243_ = lean_unsigned_to_nat(62u);
v___x_3244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__1));
v___x_3245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__0));
v___x_3246_ = l_mkPanicMessageWithDecl(v___x_3245_, v___x_3244_, v___x_3243_, v___x_3242_, v___x_3241_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(size_t v_sz_3247_, size_t v_i_3248_, lean_object* v_bs_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
uint8_t v___x_3258_; 
v___x_3258_ = lean_usize_dec_lt(v_i_3248_, v_sz_3247_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; 
v___x_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_bs_3249_);
return v___x_3259_;
}
else
{
lean_object* v_v_3260_; lean_object* v___x_3261_; lean_object* v_bs_x27_3262_; lean_object* v_a_3264_; lean_object* v___x_3269_; 
v_v_3260_ = lean_array_uget(v_bs_3249_, v_i_3248_);
v___x_3261_ = lean_unsigned_to_nat(0u);
v_bs_x27_3262_ = lean_array_uset(v_bs_3249_, v_i_3248_, v___x_3261_);
v___x_3269_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_v_3260_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3269_, 1);
if (lean_obj_tag(v_a_3270_) == 6)
{
lean_object* v_val_3271_; lean_object* v_numFields_3272_; uint8_t v___x_3273_; lean_object* v___x_3274_; 
v_val_3271_ = lean_ctor_get(v_a_3270_, 0);
lean_inc_ref(v_val_3271_);
lean_dec_ref_known(v_a_3270_, 1);
v_numFields_3272_ = lean_ctor_get(v_val_3271_, 4);
lean_inc(v_numFields_3272_);
lean_dec_ref(v_val_3271_);
v___x_3273_ = 0;
v___x_3274_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3274_, 0, v_numFields_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3261_);
lean_ctor_set_uint8(v___x_3274_, sizeof(void*)*2, v___x_3273_);
v_a_3264_ = v___x_3274_;
goto v___jp_3263_;
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
lean_dec(v_a_3270_);
v___x_3275_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3);
v___x_3276_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v___x_3275_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v_a_3264_ = v_a_3277_;
goto v___jp_3263_;
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec_ref(v_bs_x27_3262_);
v_a_3278_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3276_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3276_);
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
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec_ref(v_bs_x27_3262_);
v_a_3286_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3269_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3269_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
v___jp_3263_:
{
size_t v___x_3265_; size_t v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = ((size_t)1ULL);
v___x_3266_ = lean_usize_add(v_i_3248_, v___x_3265_);
v___x_3267_ = lean_array_uset(v_bs_x27_3262_, v_i_3248_, v_a_3264_);
v_i_3248_ = v___x_3266_;
v_bs_3249_ = v___x_3267_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___boxed(lean_object* v_sz_3294_, lean_object* v_i_3295_, lean_object* v_bs_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
size_t v_sz_boxed_3305_; size_t v_i_boxed_3306_; lean_object* v_res_3307_; 
v_sz_boxed_3305_ = lean_unbox_usize(v_sz_3294_);
lean_dec(v_sz_3294_);
v_i_boxed_3306_ = lean_unbox_usize(v_i_3295_);
lean_dec(v_i_3295_);
v_res_3307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_boxed_3305_, v_i_boxed_3306_, v_bs_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
return v_res_3307_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = lean_box(0);
v___x_3309_ = lean_unsigned_to_nat(16u);
v___x_3310_ = lean_mk_array(v___x_3309_, v___x_3308_);
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0);
v___x_3312_ = lean_unsigned_to_nat(0u);
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
lean_ctor_set(v___x_3313_, 1, v___x_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(lean_object* v_e_3316_, uint8_t v_alsoCasesOn_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
uint8_t v___x_3329_; 
v___x_3329_ = l_Lean_Expr_isApp(v_e_3316_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
lean_dec_ref(v_e_3316_);
v___x_3330_ = lean_box(0);
v___x_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
return v___x_3331_;
}
else
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_Expr_getAppFn(v_e_3316_);
if (lean_obj_tag(v___x_3332_) == 4)
{
lean_object* v_declName_3333_; lean_object* v_us_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3489_; 
v_declName_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc_n(v_declName_3333_, 2);
v_us_3334_ = lean_ctor_get(v___x_3332_, 1);
lean_inc(v_us_3334_);
lean_dec_ref_known(v___x_3332_, 2);
v___x_3335_ = l_Lean_instInhabitedExpr;
v___x_3336_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3333_, v___y_3324_);
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3489_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3489_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
if (lean_obj_tag(v_a_3337_) == 1)
{
lean_object* v_val_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3382_; 
v_val_3341_ = lean_ctor_get(v_a_3337_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v_a_3337_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3343_ = v_a_3337_;
v_isShared_3344_ = v_isSharedCheck_3382_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_val_3341_);
lean_dec(v_a_3337_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3382_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v_dummy_3345_; lean_object* v_nargs_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v_args_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; uint8_t v___x_3353_; 
v_dummy_3345_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_3346_ = l_Lean_Expr_getAppNumArgs(v_e_3316_);
lean_inc(v_nargs_3346_);
v___x_3347_ = lean_mk_array(v_nargs_3346_, v_dummy_3345_);
v___x_3348_ = lean_unsigned_to_nat(1u);
v___x_3349_ = lean_nat_sub(v_nargs_3346_, v___x_3348_);
lean_dec(v_nargs_3346_);
v_args_3350_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3316_, v___x_3347_, v___x_3349_);
v___x_3351_ = lean_array_get_size(v_args_3350_);
v___x_3352_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_3341_);
v___x_3353_ = lean_nat_dec_lt(v___x_3351_, v___x_3352_);
lean_dec(v___x_3352_);
if (v___x_3353_ == 0)
{
lean_object* v_numParams_3354_; lean_object* v_numDiscrs_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3373_; 
v_numParams_3354_ = lean_ctor_get(v_val_3341_, 0);
v_numDiscrs_3355_ = lean_ctor_get(v_val_3341_, 1);
v___x_3356_ = lean_array_mk(v_us_3334_);
v___x_3357_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3354_);
v___x_3358_ = l_Array_extract___redArg(v_args_3350_, v___x_3357_, v_numParams_3354_);
v___x_3359_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3341_);
v___x_3360_ = lean_array_get(v___x_3335_, v_args_3350_, v___x_3359_);
lean_dec(v___x_3359_);
v___x_3361_ = lean_nat_add(v_numParams_3354_, v___x_3348_);
v___x_3362_ = lean_nat_add(v___x_3361_, v_numDiscrs_3355_);
lean_inc(v___x_3362_);
lean_inc_ref_n(v_args_3350_, 2);
v___x_3363_ = l_Array_toSubarray___redArg(v_args_3350_, v___x_3361_, v___x_3362_);
v___x_3364_ = l_Subarray_copy___redArg(v___x_3363_);
v___x_3365_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3341_);
v___x_3366_ = lean_nat_add(v___x_3362_, v___x_3365_);
lean_dec(v___x_3365_);
lean_inc(v___x_3366_);
v___x_3367_ = l_Array_toSubarray___redArg(v_args_3350_, v___x_3362_, v___x_3366_);
v___x_3368_ = l_Subarray_copy___redArg(v___x_3367_);
v___x_3369_ = l_Array_toSubarray___redArg(v_args_3350_, v___x_3366_, v___x_3351_);
v___x_3370_ = l_Subarray_copy___redArg(v___x_3369_);
v___x_3371_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3371_, 0, v_val_3341_);
lean_ctor_set(v___x_3371_, 1, v_declName_3333_);
lean_ctor_set(v___x_3371_, 2, v___x_3356_);
lean_ctor_set(v___x_3371_, 3, v___x_3358_);
lean_ctor_set(v___x_3371_, 4, v___x_3360_);
lean_ctor_set(v___x_3371_, 5, v___x_3364_);
lean_ctor_set(v___x_3371_, 6, v___x_3368_);
lean_ctor_set(v___x_3371_, 7, v___x_3370_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 0, v___x_3371_);
v___x_3373_ = v___x_3343_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; 
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3373_);
v___x_3375_ = v___x_3339_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
else
{
lean_object* v___x_3378_; lean_object* v___x_3380_; 
lean_dec_ref(v_args_3350_);
lean_del_object(v___x_3343_);
lean_dec(v_val_3341_);
lean_dec(v_us_3334_);
lean_dec(v_declName_3333_);
v___x_3378_ = lean_box(0);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3378_);
v___x_3380_ = v___x_3339_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_object* v___x_3383_; 
lean_del_object(v___x_3339_);
lean_dec(v_a_3337_);
v___x_3383_ = lean_st_ref_get(v___y_3324_);
if (v_alsoCasesOn_3317_ == 0)
{
lean_dec(v___x_3383_);
lean_dec(v_us_3334_);
lean_dec(v_declName_3333_);
lean_dec_ref(v_e_3316_);
goto v___jp_3326_;
}
else
{
lean_object* v_env_3384_; uint8_t v___x_3385_; 
v_env_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc_ref(v_env_3384_);
lean_dec(v___x_3383_);
lean_inc(v_declName_3333_);
v___x_3385_ = l_Lean_isCasesOnRecursor(v_env_3384_, v_declName_3333_);
if (v___x_3385_ == 0)
{
lean_dec(v_us_3334_);
lean_dec(v_declName_3333_);
lean_dec_ref(v_e_3316_);
goto v___jp_3326_;
}
else
{
lean_object* v_indName_3386_; lean_object* v___x_3387_; 
v_indName_3386_ = l_Lean_Name_getPrefix(v_declName_3333_);
v___x_3387_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_indName_3386_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3480_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3390_ = v___x_3387_;
v_isShared_3391_ = v_isSharedCheck_3480_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3480_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
if (lean_obj_tag(v_a_3388_) == 5)
{
lean_object* v_val_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3475_; 
v_val_3392_ = lean_ctor_get(v_a_3388_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_a_3388_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3394_ = v_a_3388_;
v_isShared_3395_ = v_isSharedCheck_3475_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_val_3392_);
lean_dec(v_a_3388_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3475_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v_toConstantVal_3396_; lean_object* v_numParams_3397_; lean_object* v_numIndices_3398_; lean_object* v_ctors_3399_; lean_object* v_nargs_3400_; lean_object* v_dummy_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v_args_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v_toConstantVal_3396_ = lean_ctor_get(v_val_3392_, 0);
lean_inc_ref(v_toConstantVal_3396_);
v_numParams_3397_ = lean_ctor_get(v_val_3392_, 1);
lean_inc(v_numParams_3397_);
v_numIndices_3398_ = lean_ctor_get(v_val_3392_, 2);
lean_inc(v_numIndices_3398_);
v_ctors_3399_ = lean_ctor_get(v_val_3392_, 4);
lean_inc(v_ctors_3399_);
v_nargs_3400_ = l_Lean_Expr_getAppNumArgs(v_e_3316_);
v_dummy_3401_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_3400_);
v___x_3402_ = lean_mk_array(v_nargs_3400_, v_dummy_3401_);
v___x_3403_ = lean_unsigned_to_nat(1u);
v___x_3404_ = lean_nat_sub(v_nargs_3400_, v___x_3403_);
lean_dec(v_nargs_3400_);
v_args_3405_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3316_, v___x_3402_, v___x_3404_);
v___x_3406_ = lean_nat_add(v_numParams_3397_, v___x_3403_);
v___x_3407_ = lean_nat_add(v___x_3406_, v_numIndices_3398_);
v___x_3408_ = lean_nat_add(v___x_3407_, v___x_3403_);
lean_dec(v___x_3407_);
v___x_3409_ = l_Lean_InductiveVal_numCtors(v_val_3392_);
lean_dec_ref(v_val_3392_);
v___x_3410_ = lean_nat_add(v___x_3408_, v___x_3409_);
lean_dec(v___x_3409_);
v___x_3411_ = lean_array_get_size(v_args_3405_);
v___x_3412_ = lean_nat_dec_le(v___x_3410_, v___x_3411_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
lean_dec(v___x_3410_);
lean_dec(v___x_3408_);
lean_dec(v___x_3406_);
lean_dec_ref(v_args_3405_);
lean_dec(v_ctors_3399_);
lean_dec(v_numIndices_3398_);
lean_dec(v_numParams_3397_);
lean_dec_ref(v_toConstantVal_3396_);
lean_del_object(v___x_3394_);
lean_dec(v_us_3334_);
lean_dec(v_declName_3333_);
v___x_3413_ = lean_box(0);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3413_);
v___x_3415_ = v___x_3390_;
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
else
{
lean_object* v___x_3417_; lean_object* v_params_3418_; lean_object* v_motive_3419_; lean_object* v_discrs_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v_discrInfos_3423_; lean_object* v_alts_3424_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v_lower_3466_; lean_object* v_upper_3467_; uint8_t v___x_3474_; 
lean_del_object(v___x_3390_);
v___x_3417_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3397_);
lean_inc_ref_n(v_args_3405_, 3);
v_params_3418_ = l_Array_toSubarray___redArg(v_args_3405_, v___x_3417_, v_numParams_3397_);
v_motive_3419_ = lean_array_get(v___x_3335_, v_args_3405_, v_numParams_3397_);
lean_dec(v_numParams_3397_);
lean_inc(v___x_3408_);
v_discrs_3420_ = l_Array_toSubarray___redArg(v_args_3405_, v___x_3406_, v___x_3408_);
v___x_3421_ = lean_nat_add(v_numIndices_3398_, v___x_3403_);
lean_dec(v_numIndices_3398_);
v___x_3422_ = lean_box(0);
v_discrInfos_3423_ = lean_mk_array(v___x_3421_, v___x_3422_);
lean_inc(v___x_3410_);
v_alts_3424_ = l_Array_toSubarray___redArg(v_args_3405_, v___x_3408_, v___x_3410_);
v___x_3474_ = lean_nat_dec_le(v___x_3410_, v___x_3417_);
if (v___x_3474_ == 0)
{
v_lower_3466_ = v___x_3410_;
v_upper_3467_ = v___x_3411_;
goto v___jp_3465_;
}
else
{
lean_dec(v___x_3410_);
v_lower_3466_ = v___x_3417_;
v_upper_3467_ = v___x_3411_;
goto v___jp_3465_;
}
v___jp_3425_:
{
lean_object* v___x_3428_; size_t v_sz_3429_; size_t v___x_3430_; lean_object* v___x_3431_; 
v___x_3428_ = lean_array_mk(v_ctors_3399_);
v_sz_3429_ = lean_array_size(v___x_3428_);
v___x_3430_ = ((size_t)0ULL);
v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_3429_, v___x_3430_, v___x_3428_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3456_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3456_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3456_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v_start_3436_; lean_object* v_stop_3437_; lean_object* v_start_3438_; lean_object* v_stop_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3451_; 
v_start_3436_ = lean_ctor_get(v_params_3418_, 1);
v_stop_3437_ = lean_ctor_get(v_params_3418_, 2);
v_start_3438_ = lean_ctor_get(v_discrs_3420_, 1);
v_stop_3439_ = lean_ctor_get(v_discrs_3420_, 2);
v___x_3440_ = lean_nat_sub(v_stop_3437_, v_start_3436_);
v___x_3441_ = lean_nat_sub(v_stop_3439_, v_start_3438_);
v___x_3442_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1);
v___x_3443_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3440_);
lean_ctor_set(v___x_3443_, 1, v___x_3441_);
lean_ctor_set(v___x_3443_, 2, v_a_3432_);
lean_ctor_set(v___x_3443_, 3, v___y_3427_);
lean_ctor_set(v___x_3443_, 4, v_discrInfos_3423_);
lean_ctor_set(v___x_3443_, 5, v___x_3442_);
v___x_3444_ = lean_array_mk(v_us_3334_);
v___x_3445_ = l_Subarray_copy___redArg(v_params_3418_);
v___x_3446_ = l_Subarray_copy___redArg(v_discrs_3420_);
v___x_3447_ = l_Subarray_copy___redArg(v_alts_3424_);
v___x_3448_ = l_Subarray_copy___redArg(v___y_3426_);
v___x_3449_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3443_);
lean_ctor_set(v___x_3449_, 1, v_declName_3333_);
lean_ctor_set(v___x_3449_, 2, v___x_3444_);
lean_ctor_set(v___x_3449_, 3, v___x_3445_);
lean_ctor_set(v___x_3449_, 4, v_motive_3419_);
lean_ctor_set(v___x_3449_, 5, v___x_3446_);
lean_ctor_set(v___x_3449_, 6, v___x_3447_);
lean_ctor_set(v___x_3449_, 7, v___x_3448_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set_tag(v___x_3394_, 1);
lean_ctor_set(v___x_3394_, 0, v___x_3449_);
v___x_3451_ = v___x_3394_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3453_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v___x_3451_);
v___x_3453_ = v___x_3434_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec_ref(v_alts_3424_);
lean_dec_ref(v_discrInfos_3423_);
lean_dec_ref(v_discrs_3420_);
lean_dec(v_motive_3419_);
lean_dec_ref(v_params_3418_);
lean_del_object(v___x_3394_);
lean_dec(v_us_3334_);
lean_dec(v_declName_3333_);
v_a_3457_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3431_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3431_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
v___jp_3465_:
{
lean_object* v_levelParams_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; uint8_t v___x_3472_; 
v_levelParams_3468_ = lean_ctor_get(v_toConstantVal_3396_, 1);
lean_inc(v_levelParams_3468_);
lean_dec_ref(v_toConstantVal_3396_);
v___x_3469_ = l_Array_toSubarray___redArg(v_args_3405_, v_lower_3466_, v_upper_3467_);
v___x_3470_ = l_List_lengthTR___redArg(v_levelParams_3468_);
lean_dec(v_levelParams_3468_);
v___x_3471_ = l_List_lengthTR___redArg(v_us_3334_);
v___x_3472_ = lean_nat_dec_eq(v___x_3470_, v___x_3471_);
lean_dec(v___x_3471_);
lean_dec(v___x_3470_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; 
v___x_3473_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__2));
v___y_3426_ = v___x_3469_;
v___y_3427_ = v___x_3473_;
goto v___jp_3425_;
}
else
{
v___y_3426_ = v___x_3469_;
v___y_3427_ = v___x_3422_;
goto v___jp_3425_;
}
}
}
}
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
lean_dec(v_a_3388_);
lean_dec(v_us_3334_);
lean_dec(v_declName_3333_);
lean_dec_ref(v_e_3316_);
v___x_3476_ = lean_box(0);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3476_);
v___x_3478_ = v___x_3390_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
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
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec(v_us_3334_);
lean_dec(v_declName_3333_);
lean_dec_ref(v_e_3316_);
v_a_3481_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3387_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3387_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
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
lean_dec_ref(v___x_3332_);
lean_dec_ref(v_e_3316_);
goto v___jp_3326_;
}
}
v___jp_3326_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = lean_box(0);
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
return v___x_3328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___boxed(lean_object* v_e_3490_, lean_object* v_alsoCasesOn_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
uint8_t v_alsoCasesOn_boxed_3500_; lean_object* v_res_3501_; 
v_alsoCasesOn_boxed_3500_ = lean_unbox(v_alsoCasesOn_3491_);
v_res_3501_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3490_, v_alsoCasesOn_boxed_3500_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
return v_res_3501_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__1));
v___x_3506_ = l_Lean_stringToMessageData(v___x_3505_);
return v___x_3506_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = lean_unsigned_to_nat(1u);
v___x_3508_ = l_Lean_Expr_bvar___override(v___x_3507_);
return v___x_3508_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3511_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__5));
v___x_3512_ = lean_unsigned_to_nat(2u);
v___x_3513_ = lean_unsigned_to_nat(182u);
v___x_3514_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__4));
v___x_3515_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_3516_ = l_mkPanicMessageWithDecl(v___x_3515_, v___x_3514_, v___x_3513_, v___x_3512_, v___x_3511_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(lean_object* v_e_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v_e_3526_; uint8_t v___x_3527_; lean_object* v___x_3528_; 
v_e_3526_ = l_Lean_Expr_headBeta(v_e_3517_);
v___x_3527_ = 1;
v___x_3528_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3526_, v___x_3527_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3778_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3531_ = v___x_3528_;
v_isShared_3532_ = v_isSharedCheck_3778_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3778_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
if (lean_obj_tag(v_a_3529_) == 1)
{
lean_object* v_val_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3773_; 
v_val_3533_ = lean_ctor_get(v_a_3529_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_a_3529_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3535_ = v_a_3529_;
v_isShared_3536_ = v_isSharedCheck_3773_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_val_3533_);
lean_dec(v_a_3529_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3773_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v_toMatcherInfo_3537_; lean_object* v_matcherName_3538_; lean_object* v_params_3539_; lean_object* v_motive_3540_; lean_object* v_discrs_3541_; lean_object* v_alts_3542_; lean_object* v_remaining_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; uint8_t v___x_3546_; 
v_toMatcherInfo_3537_ = lean_ctor_get(v_val_3533_, 0);
lean_inc_ref(v_toMatcherInfo_3537_);
v_matcherName_3538_ = lean_ctor_get(v_val_3533_, 1);
lean_inc(v_matcherName_3538_);
v_params_3539_ = lean_ctor_get(v_val_3533_, 3);
lean_inc_ref(v_params_3539_);
v_motive_3540_ = lean_ctor_get(v_val_3533_, 4);
lean_inc_ref(v_motive_3540_);
v_discrs_3541_ = lean_ctor_get(v_val_3533_, 5);
lean_inc_ref(v_discrs_3541_);
v_alts_3542_ = lean_ctor_get(v_val_3533_, 6);
lean_inc_ref(v_alts_3542_);
v_remaining_3543_ = lean_ctor_get(v_val_3533_, 7);
lean_inc_ref(v_remaining_3543_);
v___x_3544_ = lean_unsigned_to_nat(0u);
v___x_3545_ = lean_array_get_size(v_remaining_3543_);
v___x_3546_ = lean_nat_dec_lt(v___x_3544_, v___x_3545_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; lean_object* v___x_3549_; 
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
v___x_3547_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3547_);
v___x_3549_ = v___x_3531_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
else
{
lean_object* v___x_3551_; uint8_t v___x_3552_; 
v___x_3551_ = lean_array_fget_borrowed(v_remaining_3543_, v___x_3544_);
v___x_3552_ = l_Lean_Expr_isLambda(v___x_3551_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3555_; 
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
v___x_3553_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3553_);
v___x_3555_ = v___x_3531_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
else
{
lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_3557_ = l_Lean_Expr_bindingBody_x21(v___x_3551_);
v___x_3558_ = l_Lean_Expr_isLambda(v___x_3557_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
lean_dec_ref(v___x_3557_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
v___x_3559_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3559_);
v___x_3561_ = v___x_3531_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
else
{
lean_object* v___x_3563_; uint8_t v___x_3564_; 
v___x_3563_ = l_Lean_Expr_bindingBody_x21(v___x_3557_);
lean_dec_ref(v___x_3557_);
v___x_3564_ = l_Lean_Expr_isApp(v___x_3563_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3565_; lean_object* v___x_3567_; 
lean_dec_ref(v___x_3563_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3565_);
v___x_3567_ = v___x_3531_;
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
uint8_t v___x_3569_; 
v___x_3569_ = lean_expr_has_loose_bvar(v___x_3563_, v___x_3544_);
if (v___x_3569_ == 0)
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___y_3573_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___x_3570_ = l_Lean_Expr_appArg_x21(v___x_3563_);
v___x_3571_ = lean_unsigned_to_nat(1u);
v___x_3636_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3);
v___x_3637_ = lean_expr_eqv(v___x_3570_, v___x_3636_);
lean_dec_ref(v___x_3570_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; lean_object* v___x_3640_; 
lean_dec_ref(v___x_3563_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
v___x_3638_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3638_);
v___x_3640_ = v___x_3531_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
else
{
lean_object* v___x_3642_; uint8_t v___x_3643_; 
v___x_3642_ = l_Lean_Expr_appFn_x21(v___x_3563_);
lean_dec_ref(v___x_3563_);
v___x_3643_ = lean_expr_has_loose_bvar(v___x_3642_, v___x_3571_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; 
lean_del_object(v___x_3531_);
lean_inc(v_a_3524_);
lean_inc_ref(v_a_3523_);
lean_inc(v_a_3522_);
lean_inc_ref(v_a_3521_);
lean_inc_ref(v___x_3642_);
v___x_3644_ = lean_infer_type(v___x_3642_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3646_; uint8_t v_transparency_3647_; uint8_t v___x_3648_; lean_object* v___y_3650_; uint8_t v___x_3741_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v___x_3646_ = l_Lean_Meta_Context_config(v_a_3521_);
v_transparency_3647_ = lean_ctor_get_uint8(v___x_3646_, 9);
v___x_3648_ = 0;
v___x_3741_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3647_, v___x_3648_);
if (v___x_3741_ == 0)
{
lean_object* v_keyedConfig_3742_; uint8_t v_trackZetaDelta_3743_; lean_object* v_zetaDeltaSet_3744_; lean_object* v_lctx_3745_; lean_object* v_localInstances_3746_; lean_object* v_defEqCtx_x3f_3747_; lean_object* v_synthPendingDepth_3748_; lean_object* v_customCanUnfoldPredicate_x3f_3749_; uint8_t v_univApprox_3750_; uint8_t v_inTypeClassResolution_3751_; uint8_t v_cacheInferType_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_keyedConfig_3742_ = lean_ctor_get(v_a_3521_, 0);
v_trackZetaDelta_3743_ = lean_ctor_get_uint8(v_a_3521_, sizeof(void*)*7);
v_zetaDeltaSet_3744_ = lean_ctor_get(v_a_3521_, 1);
v_lctx_3745_ = lean_ctor_get(v_a_3521_, 2);
v_localInstances_3746_ = lean_ctor_get(v_a_3521_, 3);
v_defEqCtx_x3f_3747_ = lean_ctor_get(v_a_3521_, 4);
v_synthPendingDepth_3748_ = lean_ctor_get(v_a_3521_, 5);
v_customCanUnfoldPredicate_x3f_3749_ = lean_ctor_get(v_a_3521_, 6);
v_univApprox_3750_ = lean_ctor_get_uint8(v_a_3521_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3751_ = lean_ctor_get_uint8(v_a_3521_, sizeof(void*)*7 + 2);
v_cacheInferType_3752_ = lean_ctor_get_uint8(v_a_3521_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3742_);
v___x_3753_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3648_, v_keyedConfig_3742_);
lean_inc(v_customCanUnfoldPredicate_x3f_3749_);
lean_inc(v_synthPendingDepth_3748_);
lean_inc(v_defEqCtx_x3f_3747_);
lean_inc_ref(v_localInstances_3746_);
lean_inc_ref(v_lctx_3745_);
lean_inc(v_zetaDeltaSet_3744_);
v___x_3754_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
lean_ctor_set(v___x_3754_, 1, v_zetaDeltaSet_3744_);
lean_ctor_set(v___x_3754_, 2, v_lctx_3745_);
lean_ctor_set(v___x_3754_, 3, v_localInstances_3746_);
lean_ctor_set(v___x_3754_, 4, v_defEqCtx_x3f_3747_);
lean_ctor_set(v___x_3754_, 5, v_synthPendingDepth_3748_);
lean_ctor_set(v___x_3754_, 6, v_customCanUnfoldPredicate_x3f_3749_);
lean_ctor_set_uint8(v___x_3754_, sizeof(void*)*7, v_trackZetaDelta_3743_);
lean_ctor_set_uint8(v___x_3754_, sizeof(void*)*7 + 1, v_univApprox_3750_);
lean_ctor_set_uint8(v___x_3754_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3751_);
lean_ctor_set_uint8(v___x_3754_, sizeof(void*)*7 + 3, v_cacheInferType_3752_);
v___x_3755_ = l_Lean_Meta_whnfForall(v_a_3645_, v___x_3754_, v_a_3522_, v_a_3523_, v_a_3524_);
lean_dec_ref_known(v___x_3754_, 7);
v___y_3650_ = v___x_3755_;
goto v___jp_3649_;
}
else
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Lean_Meta_whnfForall(v_a_3645_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
v___y_3650_ = v___x_3756_;
goto v___jp_3649_;
}
v___jp_3649_:
{
if (lean_obj_tag(v___y_3650_) == 0)
{
lean_object* v_a_3651_; uint8_t v___x_3652_; 
v_a_3651_ = lean_ctor_get(v___y_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v___y_3650_, 1);
v___x_3652_ = l_Lean_Expr_isForall(v_a_3651_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
lean_dec(v_a_3651_);
lean_dec_ref(v___x_3646_);
lean_dec_ref(v___x_3642_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
v___x_3653_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6);
v___x_3654_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v___x_3653_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
return v___x_3654_;
}
else
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; uint8_t v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___f_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3655_ = l_Lean_Expr_bindingDomain_x21(v_a_3651_);
v___x_3656_ = l_Lean_Expr_bindingName_x21(v_a_3651_);
v___x_3657_ = l_Lean_Expr_bindingBody_x21(v_a_3651_);
lean_dec(v_a_3651_);
v___x_3658_ = 0;
v___x_3659_ = lean_box(v___x_3658_);
v___x_3660_ = lean_box(v___x_3643_);
v___x_3661_ = lean_box(v___x_3527_);
v___f_3662_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3662_, 0, v___x_3659_);
lean_closure_set(v___f_3662_, 1, v___x_3660_);
lean_closure_set(v___f_3662_, 2, v___x_3661_);
lean_inc_ref(v___x_3655_);
v___x_3663_ = l_Lean_Expr_lam___override(v___x_3656_, v___x_3655_, v___x_3657_, v___x_3658_);
v___x_3664_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_val_3533_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3724_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3724_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3724_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
if (lean_obj_tag(v_a_3665_) == 1)
{
lean_object* v_val_3669_; lean_object* v___x_3670_; 
lean_del_object(v___x_3667_);
v_val_3669_ = lean_ctor_get(v_a_3665_, 0);
lean_inc(v_val_3669_);
lean_dec_ref_known(v_a_3665_, 1);
v___x_3670_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_motive_3540_, v___f_3662_, v___x_3643_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3672_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref_known(v___x_3670_, 1);
v___x_3672_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_3538_, v_toMatcherInfo_3537_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; uint8_t v_transparency_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; size_t v_sz_3685_; size_t v___x_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___x_3672_, 1);
v_transparency_3674_ = lean_ctor_get_uint8(v___x_3646_, 9);
lean_dec_ref(v___x_3646_);
v___x_3675_ = lean_unsigned_to_nat(5u);
v___x_3676_ = lean_mk_empty_array_with_capacity(v___x_3675_);
v___x_3677_ = lean_array_push(v___x_3676_, v_val_3669_);
v___x_3678_ = lean_array_push(v___x_3677_, v___x_3655_);
v___x_3679_ = lean_array_push(v___x_3678_, v___x_3663_);
v___x_3680_ = lean_array_push(v___x_3679_, v___x_3642_);
v___x_3681_ = lean_array_push(v___x_3680_, v_a_3671_);
v___x_3682_ = l_Array_append___redArg(v_params_3539_, v___x_3681_);
lean_dec_ref(v___x_3681_);
v___x_3683_ = l_Array_append___redArg(v___x_3682_, v_discrs_3541_);
lean_dec_ref(v_discrs_3541_);
v___x_3684_ = l_Array_append___redArg(v___x_3683_, v_alts_3542_);
lean_dec_ref(v_alts_3542_);
v_sz_3685_ = lean_array_size(v___x_3684_);
v___x_3686_ = ((size_t)0ULL);
v___x_3687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_3685_, v___x_3686_, v___x_3684_);
v___x_3688_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3674_, v___x_3648_);
if (v___x_3688_ == 0)
{
lean_object* v_keyedConfig_3689_; uint8_t v_trackZetaDelta_3690_; lean_object* v_zetaDeltaSet_3691_; lean_object* v_lctx_3692_; lean_object* v_localInstances_3693_; lean_object* v_defEqCtx_x3f_3694_; lean_object* v_synthPendingDepth_3695_; lean_object* v_customCanUnfoldPredicate_x3f_3696_; uint8_t v_univApprox_3697_; uint8_t v_inTypeClassResolution_3698_; uint8_t v_cacheInferType_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v_keyedConfig_3689_ = lean_ctor_get(v_a_3521_, 0);
v_trackZetaDelta_3690_ = lean_ctor_get_uint8(v_a_3521_, sizeof(void*)*7);
v_zetaDeltaSet_3691_ = lean_ctor_get(v_a_3521_, 1);
v_lctx_3692_ = lean_ctor_get(v_a_3521_, 2);
v_localInstances_3693_ = lean_ctor_get(v_a_3521_, 3);
v_defEqCtx_x3f_3694_ = lean_ctor_get(v_a_3521_, 4);
v_synthPendingDepth_3695_ = lean_ctor_get(v_a_3521_, 5);
v_customCanUnfoldPredicate_x3f_3696_ = lean_ctor_get(v_a_3521_, 6);
v_univApprox_3697_ = lean_ctor_get_uint8(v_a_3521_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3698_ = lean_ctor_get_uint8(v_a_3521_, sizeof(void*)*7 + 2);
v_cacheInferType_3699_ = lean_ctor_get_uint8(v_a_3521_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3689_);
v___x_3700_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3648_, v_keyedConfig_3689_);
lean_inc(v_customCanUnfoldPredicate_x3f_3696_);
lean_inc(v_synthPendingDepth_3695_);
lean_inc(v_defEqCtx_x3f_3694_);
lean_inc_ref(v_localInstances_3693_);
lean_inc_ref(v_lctx_3692_);
lean_inc(v_zetaDeltaSet_3691_);
v___x_3701_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
lean_ctor_set(v___x_3701_, 1, v_zetaDeltaSet_3691_);
lean_ctor_set(v___x_3701_, 2, v_lctx_3692_);
lean_ctor_set(v___x_3701_, 3, v_localInstances_3693_);
lean_ctor_set(v___x_3701_, 4, v_defEqCtx_x3f_3694_);
lean_ctor_set(v___x_3701_, 5, v_synthPendingDepth_3695_);
lean_ctor_set(v___x_3701_, 6, v_customCanUnfoldPredicate_x3f_3696_);
lean_ctor_set_uint8(v___x_3701_, sizeof(void*)*7, v_trackZetaDelta_3690_);
lean_ctor_set_uint8(v___x_3701_, sizeof(void*)*7 + 1, v_univApprox_3697_);
lean_ctor_set_uint8(v___x_3701_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3698_);
lean_ctor_set_uint8(v___x_3701_, sizeof(void*)*7 + 3, v_cacheInferType_3699_);
v___x_3702_ = l_Lean_Meta_mkAppOptM(v_a_3673_, v___x_3687_, v___x_3701_, v_a_3522_, v_a_3523_, v_a_3524_);
lean_dec_ref_known(v___x_3701_, 7);
v___y_3573_ = v___x_3702_;
goto v___jp_3572_;
}
else
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_Meta_mkAppOptM(v_a_3673_, v___x_3687_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
v___y_3573_ = v___x_3703_;
goto v___jp_3572_;
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v_a_3671_);
lean_dec(v_val_3669_);
lean_dec_ref(v___x_3663_);
lean_dec_ref(v___x_3655_);
lean_dec_ref(v___x_3646_);
lean_dec_ref(v___x_3642_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_params_3539_);
lean_del_object(v___x_3535_);
v_a_3704_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3672_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3672_);
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
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec(v_val_3669_);
lean_dec_ref(v___x_3663_);
lean_dec_ref(v___x_3655_);
lean_dec_ref(v___x_3646_);
lean_dec_ref(v___x_3642_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
v_a_3712_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3670_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3670_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3722_; 
lean_dec(v_a_3665_);
lean_dec_ref(v___x_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v___x_3655_);
lean_dec_ref(v___x_3646_);
lean_dec_ref(v___x_3642_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
v___x_3720_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3720_);
v___x_3722_ = v___x_3667_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
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
lean_dec_ref(v___x_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v___x_3655_);
lean_dec_ref(v___x_3646_);
lean_dec_ref(v___x_3642_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
v_a_3725_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3664_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3664_);
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
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec_ref(v___x_3646_);
lean_dec_ref(v___x_3642_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
v_a_3733_ = lean_ctor_get(v___y_3650_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___y_3650_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___y_3650_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___y_3650_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec_ref(v___x_3642_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
v_a_3757_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3644_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3644_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
lean_dec_ref(v___x_3642_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
v___x_3765_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3765_);
v___x_3767_ = v___x_3531_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
v___jp_3572_:
{
if (lean_obj_tag(v___y_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3575_; 
v_a_3574_ = lean_ctor_get(v___y_3573_, 0);
lean_inc_n(v_a_3574_, 2);
lean_dec_ref_known(v___y_3573_, 1);
lean_inc(v_a_3524_);
lean_inc_ref(v_a_3523_);
lean_inc(v_a_3522_);
lean_inc_ref(v_a_3521_);
v___x_3575_ = lean_infer_type(v_a_3574_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3576_);
lean_dec_ref_known(v___x_3575_, 1);
v___x_3577_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_3578_ = lean_unsigned_to_nat(3u);
v___x_3579_ = l_Lean_Expr_isAppOfArity(v_a_3576_, v___x_3577_, v___x_3578_);
if (v___x_3579_ == 0)
{
lean_object* v___x_3580_; 
lean_dec(v_a_3576_);
lean_dec_ref(v_remaining_3543_);
lean_del_object(v___x_3535_);
lean_inc(v_a_3524_);
lean_inc_ref(v_a_3523_);
lean_inc(v_a_3522_);
lean_inc_ref(v_a_3521_);
v___x_3580_ = lean_infer_type(v_a_3574_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3580_, 1);
v___x_3582_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2);
v___x_3583_ = l_Lean_indentExpr(v_a_3581_);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v___x_3584_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
return v___x_3585_;
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
v_a_3586_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3580_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3580_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3594_ = l_Lean_Expr_appArg_x21(v_a_3576_);
lean_dec(v_a_3576_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v_a_3574_);
v___x_3596_ = v___x_3535_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3574_);
v___x_3596_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3597_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3597_, 0, v___x_3594_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
lean_ctor_set_uint8(v___x_3597_, sizeof(void*)*2, v___x_3527_);
v___x_3598_ = l_Array_toSubarray___redArg(v_remaining_3543_, v___x_3571_, v___x_3545_);
v___x_3599_ = l_Subarray_copy___redArg(v___x_3598_);
v___x_3600_ = l_Lean_Meta_Simp_Result_addExtraArgs(v___x_3597_, v___x_3599_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
lean_dec_ref(v___x_3599_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3610_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3610_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3610_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3605_, 0, v_a_3601_);
v___x_3606_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v___x_3606_);
v___x_3608_ = v___x_3603_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
v_a_3611_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3600_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3600_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec(v_a_3574_);
lean_dec_ref(v_remaining_3543_);
lean_del_object(v___x_3535_);
v_a_3620_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3575_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3575_);
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
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v_remaining_3543_);
lean_del_object(v___x_3535_);
v_a_3628_ = lean_ctor_get(v___y_3573_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___y_3573_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___y_3573_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___y_3573_);
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
else
{
lean_object* v___x_3769_; lean_object* v___x_3771_; 
lean_dec_ref(v___x_3563_);
lean_dec_ref(v_remaining_3543_);
lean_dec_ref(v_alts_3542_);
lean_dec_ref(v_discrs_3541_);
lean_dec_ref(v_motive_3540_);
lean_dec_ref(v_params_3539_);
lean_dec(v_matcherName_3538_);
lean_dec_ref(v_toMatcherInfo_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
v___x_3769_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3769_);
v___x_3771_ = v___x_3531_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3769_);
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
}
else
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
lean_dec(v_a_3529_);
v___x_3774_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3774_);
v___x_3776_ = v___x_3531_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3774_);
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
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
v_a_3779_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3528_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3528_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed(lean_object* v_e_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(v_e_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec(v_a_3788_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(lean_object* v_declName_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3797_, v___y_3804_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___boxed(lean_object* v_declName_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(v_declName_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3808_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(lean_object* v_00_u03b1_3817_, lean_object* v_msg_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v___x_3827_; 
v___x_3827_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_3818_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___boxed(lean_object* v_00_u03b1_3828_, lean_object* v_msg_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(v_00_u03b1_3828_, v_msg_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3839_, lean_object* v_constName_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3850_, lean_object* v_constName_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(v_00_u03b1_3850_, v_constName_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b1_3861_, lean_object* v_ref_3862_, lean_object* v_constName_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v___x_3872_; 
v___x_3872_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3862_, v_constName_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b1_3873_, lean_object* v_ref_3874_, lean_object* v_constName_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(v_00_u03b1_3873_, v_ref_3874_, v_constName_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec(v_ref_3874_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3885_, lean_object* v_ref_3886_, lean_object* v_msg_3887_, lean_object* v_declHint_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3886_, v_msg_3887_, v_declHint_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3898_, lean_object* v_ref_3899_, lean_object* v_msg_3900_, lean_object* v_declHint_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_3898_, v_ref_3899_, v_msg_3900_, v_declHint_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec(v_ref_3899_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_3911_, lean_object* v_declHint_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v___x_3921_; 
v___x_3921_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3911_, v_declHint_3912_, v___y_3919_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_3922_, lean_object* v_declHint_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(v_msg_3922_, v_declHint_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(lean_object* v_00_u03b1_3933_, lean_object* v_ref_3934_, lean_object* v_msg_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3934_, v_msg_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___boxed(lean_object* v_00_u03b1_3945_, lean_object* v_ref_3946_, lean_object* v_msg_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(v_00_u03b1_3945_, v_ref_3946_, v_msg_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec(v_ref_3946_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4002_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4003_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4004_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed), 9, 0);
v___x_4005_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4002_, v___x_4003_, v___x_4004_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10____boxed(lean_object* v_a_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_();
return v_res_4007_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0(void){
_start:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
return v___x_4009_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4010_ = lean_unsigned_to_nat(32u);
v___x_4011_ = lean_mk_empty_array_with_capacity(v___x_4010_);
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
return v___x_4012_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2));
v___x_4015_ = l_Lean_stringToMessageData(v___x_4014_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(lean_object* v___x_4016_, lean_object* v___x_4017_, lean_object* v___x_4018_, lean_object* v___x_4019_, lean_object* v___x_4020_, uint8_t v___x_4021_, lean_object* v_mvarId_4022_, uint8_t v___x_4023_, lean_object* v_declName_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_4016_, v___x_4017_, v___x_4018_, v___x_4019_, v___y_4025_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
lean_dec_ref_known(v___x_4030_, 1);
v___x_4032_ = lean_mk_empty_array_with_capacity(v___x_4020_);
v___x_4033_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4034_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4035_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4036_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
lean_inc(v___x_4020_);
v___x_4037_ = l_Lean_Name_num___override(v___x_4036_, v___x_4020_);
v___x_4038_ = l_Lean_Name_str___override(v___x_4037_, v___x_4033_);
v___x_4039_ = l_Lean_Name_str___override(v___x_4038_, v___x_4034_);
v___x_4040_ = l_Lean_Name_str___override(v___x_4039_, v___x_4035_);
v___x_4041_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4042_ = l_Lean_Name_str___override(v___x_4040_, v___x_4041_);
v___x_4043_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_4032_, v___x_4042_, v___x_4021_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; size_t v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___x_4043_, 1);
v___x_4045_ = lean_box(0);
v___x_4046_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0);
lean_inc_n(v___x_4020_, 2);
v___x_4047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
lean_ctor_set(v___x_4047_, 1, v___x_4020_);
v___x_4048_ = lean_unsigned_to_nat(32u);
v___x_4049_ = lean_mk_empty_array_with_capacity(v___x_4048_);
v___x_4050_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1);
v___x_4051_ = ((size_t)5ULL);
v___x_4052_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4052_, 0, v___x_4050_);
lean_ctor_set(v___x_4052_, 1, v___x_4049_);
lean_ctor_set(v___x_4052_, 2, v___x_4020_);
lean_ctor_set(v___x_4052_, 3, v___x_4020_);
lean_ctor_set_usize(v___x_4052_, 4, v___x_4051_);
v___x_4053_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4046_);
lean_ctor_set(v___x_4053_, 1, v___x_4046_);
lean_ctor_set(v___x_4053_, 2, v___x_4046_);
lean_ctor_set(v___x_4053_, 3, v___x_4052_);
v___x_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4047_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = l_Lean_Meta_simpTarget(v_mvarId_4022_, v_a_4031_, v_a_4044_, v___x_4045_, v___x_4023_, v___x_4054_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4098_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4058_ = v___x_4055_;
v_isShared_4059_ = v_isSharedCheck_4098_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4055_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4098_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v_fst_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4096_; 
v_fst_4060_ = lean_ctor_get(v_a_4056_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_a_4056_);
if (v_isSharedCheck_4096_ == 0)
{
lean_object* v_unused_4097_; 
v_unused_4097_ = lean_ctor_get(v_a_4056_, 1);
lean_dec(v_unused_4097_);
v___x_4062_ = v_a_4056_;
v_isShared_4063_ = v_isSharedCheck_4096_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_fst_4060_);
lean_dec(v_a_4056_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4096_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
if (lean_obj_tag(v_fst_4060_) == 0)
{
lean_object* v___x_4064_; lean_object* v___x_4066_; 
lean_del_object(v___x_4062_);
lean_dec(v_declName_4024_);
v___x_4064_ = lean_box(0);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 0, v___x_4064_);
v___x_4066_ = v___x_4058_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
else
{
lean_object* v_val_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4072_; 
lean_del_object(v___x_4058_);
v_val_4068_ = lean_ctor_get(v_fst_4060_, 0);
lean_inc(v_val_4068_);
lean_dec_ref_known(v_fst_4060_, 1);
v___x_4069_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3);
v___x_4070_ = l_Lean_MessageData_ofConstName(v_declName_4024_, v___x_4021_);
if (v_isShared_4063_ == 0)
{
lean_ctor_set_tag(v___x_4062_, 7);
lean_ctor_set(v___x_4062_, 1, v___x_4070_);
lean_ctor_set(v___x_4062_, 0, v___x_4069_);
v___x_4072_ = v___x_4062_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4069_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v___x_4070_);
v___x_4072_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___f_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4073_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_4074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4072_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
v___f_4075_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4075_, 0, v___x_4074_);
v___x_4076_ = lean_box(v___x_4023_);
v___x_4077_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___boxed), 7, 2);
lean_closure_set(v___x_4077_, 0, v_val_4068_);
lean_closure_set(v___x_4077_, 1, v___x_4076_);
v___x_4078_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4077_, v___f_4075_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4078_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4078_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
v_a_4087_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4078_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4078_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
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
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec(v_declName_4024_);
v_a_4099_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4055_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4055_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec(v_a_4031_);
lean_dec(v_declName_4024_);
lean_dec(v_mvarId_4022_);
lean_dec(v___x_4020_);
v_a_4107_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4043_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4043_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_dec(v_declName_4024_);
lean_dec(v_mvarId_4022_);
lean_dec(v___x_4020_);
v_a_4115_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4030_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4030_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___boxed(lean_object* v___x_4123_, lean_object* v___x_4124_, lean_object* v___x_4125_, lean_object* v___x_4126_, lean_object* v___x_4127_, lean_object* v___x_4128_, lean_object* v_mvarId_4129_, lean_object* v___x_4130_, lean_object* v_declName_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
uint8_t v___x_1412__boxed_4137_; uint8_t v___x_1413__boxed_4138_; lean_object* v_res_4139_; 
v___x_1412__boxed_4137_ = lean_unbox(v___x_4128_);
v___x_1413__boxed_4138_ = lean_unbox(v___x_4130_);
v_res_4139_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4123_, v___x_4124_, v___x_4125_, v___x_4126_, v___x_4127_, v___x_1412__boxed_4137_, v_mvarId_4129_, v___x_1413__boxed_4138_, v_declName_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
return v_res_4139_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2(void){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = lean_box(0);
v___x_4150_ = lean_unsigned_to_nat(16u);
v___x_4151_ = lean_mk_array(v___x_4150_, v___x_4149_);
return v___x_4151_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3(void){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4152_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2);
v___x_4153_ = lean_unsigned_to_nat(0u);
v___x_4154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
lean_ctor_set(v___x_4154_, 1, v___x_4152_);
return v___x_4154_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4(void){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
return v___x_4156_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5(void){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; uint8_t v___x_4159_; lean_object* v___x_4160_; 
v___x_4157_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4);
v___x_4158_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3);
v___x_4159_ = 1;
v___x_4160_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4160_, 0, v___x_4158_);
lean_ctor_set(v___x_4160_, 1, v___x_4157_);
lean_ctor_set_uint8(v___x_4160_, sizeof(void*)*2, v___x_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object* v_declName_4161_, lean_object* v_mvarId_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_){
_start:
{
lean_object* v___y_4169_; uint8_t v___x_4186_; uint8_t v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v_transparency_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; uint8_t v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; uint8_t v___x_4196_; 
v___x_4186_ = 0;
v___x_4187_ = 1;
v___x_4188_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0));
v___x_4189_ = l_Lean_Meta_Context_config(v_a_4163_);
v_transparency_4190_ = lean_ctor_get_uint8(v___x_4189_, 9);
lean_dec_ref(v___x_4189_);
v___x_4191_ = lean_unsigned_to_nat(0u);
v___x_4192_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1));
v___x_4193_ = 0;
v___x_4194_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4195_ = l_Lean_Options_empty;
v___x_4196_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4190_, v___x_4193_);
if (v___x_4196_ == 0)
{
lean_object* v_keyedConfig_4197_; uint8_t v_trackZetaDelta_4198_; lean_object* v_zetaDeltaSet_4199_; lean_object* v_lctx_4200_; lean_object* v_localInstances_4201_; lean_object* v_defEqCtx_x3f_4202_; lean_object* v_synthPendingDepth_4203_; lean_object* v_customCanUnfoldPredicate_x3f_4204_; uint8_t v_univApprox_4205_; uint8_t v_inTypeClassResolution_4206_; uint8_t v_cacheInferType_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v_keyedConfig_4197_ = lean_ctor_get(v_a_4163_, 0);
v_trackZetaDelta_4198_ = lean_ctor_get_uint8(v_a_4163_, sizeof(void*)*7);
v_zetaDeltaSet_4199_ = lean_ctor_get(v_a_4163_, 1);
v_lctx_4200_ = lean_ctor_get(v_a_4163_, 2);
v_localInstances_4201_ = lean_ctor_get(v_a_4163_, 3);
v_defEqCtx_x3f_4202_ = lean_ctor_get(v_a_4163_, 4);
v_synthPendingDepth_4203_ = lean_ctor_get(v_a_4163_, 5);
v_customCanUnfoldPredicate_x3f_4204_ = lean_ctor_get(v_a_4163_, 6);
v_univApprox_4205_ = lean_ctor_get_uint8(v_a_4163_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4206_ = lean_ctor_get_uint8(v_a_4163_, sizeof(void*)*7 + 2);
v_cacheInferType_4207_ = lean_ctor_get_uint8(v_a_4163_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4197_);
v___x_4208_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4193_, v_keyedConfig_4197_);
lean_inc(v_customCanUnfoldPredicate_x3f_4204_);
lean_inc(v_synthPendingDepth_4203_);
lean_inc(v_defEqCtx_x3f_4202_);
lean_inc_ref(v_localInstances_4201_);
lean_inc_ref(v_lctx_4200_);
lean_inc(v_zetaDeltaSet_4199_);
v___x_4209_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
lean_ctor_set(v___x_4209_, 1, v_zetaDeltaSet_4199_);
lean_ctor_set(v___x_4209_, 2, v_lctx_4200_);
lean_ctor_set(v___x_4209_, 3, v_localInstances_4201_);
lean_ctor_set(v___x_4209_, 4, v_defEqCtx_x3f_4202_);
lean_ctor_set(v___x_4209_, 5, v_synthPendingDepth_4203_);
lean_ctor_set(v___x_4209_, 6, v_customCanUnfoldPredicate_x3f_4204_);
lean_ctor_set_uint8(v___x_4209_, sizeof(void*)*7, v_trackZetaDelta_4198_);
lean_ctor_set_uint8(v___x_4209_, sizeof(void*)*7 + 1, v_univApprox_4205_);
lean_ctor_set_uint8(v___x_4209_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4206_);
lean_ctor_set_uint8(v___x_4209_, sizeof(void*)*7 + 3, v_cacheInferType_4207_);
v___x_4210_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4188_, v___x_4192_, v___x_4194_, v___x_4195_, v___x_4191_, v___x_4186_, v_mvarId_4162_, v___x_4187_, v_declName_4161_, v___x_4209_, v_a_4164_, v_a_4165_, v_a_4166_);
lean_dec_ref_known(v___x_4209_, 7);
v___y_4169_ = v___x_4210_;
goto v___jp_4168_;
}
else
{
lean_object* v___x_4211_; 
v___x_4211_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4188_, v___x_4192_, v___x_4194_, v___x_4195_, v___x_4191_, v___x_4186_, v_mvarId_4162_, v___x_4187_, v_declName_4161_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
v___y_4169_ = v___x_4211_;
goto v___jp_4168_;
}
v___jp_4168_:
{
if (lean_obj_tag(v___y_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
v_a_4170_ = lean_ctor_get(v___y_4169_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___y_4169_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___y_4169_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___y_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
else
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
v_a_4178_ = lean_ctor_get(v___y_4169_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___y_4169_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___y_4169_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___y_4169_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4178_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___boxed(lean_object* v_declName_4212_, lean_object* v_mvarId_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4212_, v_mvarId_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(lean_object* v_e_4220_, lean_object* v_k_4221_, uint8_t v_cleanupAnnotations_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___f_4228_; uint8_t v___x_4229_; uint8_t v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___f_4228_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4228_, 0, v_k_4221_);
v___x_4229_ = 1;
v___x_4230_ = 0;
v___x_4231_ = lean_box(0);
v___x_4232_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4220_, v___x_4229_, v___x_4230_, v___x_4229_, v___x_4230_, v___x_4231_, v___f_4228_, v_cleanupAnnotations_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4232_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4232_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
v_a_4241_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4232_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4232_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg___boxed(lean_object* v_e_4249_, lean_object* v_k_4250_, lean_object* v_cleanupAnnotations_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4257_; lean_object* v_res_4258_; 
v_cleanupAnnotations_boxed_4257_ = lean_unbox(v_cleanupAnnotations_4251_);
v_res_4258_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4249_, v_k_4250_, v_cleanupAnnotations_boxed_4257_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_object* v_00_u03b1_4259_, lean_object* v_e_4260_, lean_object* v_k_4261_, uint8_t v_cleanupAnnotations_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4260_, v_k_4261_, v_cleanupAnnotations_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed(lean_object* v_00_u03b1_4269_, lean_object* v_e_4270_, lean_object* v_k_4271_, lean_object* v_cleanupAnnotations_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4278_; lean_object* v_res_4279_; 
v_cleanupAnnotations_boxed_4278_ = lean_unbox(v_cleanupAnnotations_4272_);
v_res_4279_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(v_00_u03b1_4269_, v_e_4270_, v_k_4271_, v_cleanupAnnotations_boxed_4278_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(lean_object* v_opts_4280_, lean_object* v_opt_4281_){
_start:
{
lean_object* v_name_4282_; lean_object* v_defValue_4283_; lean_object* v_map_4284_; lean_object* v___x_4285_; 
v_name_4282_ = lean_ctor_get(v_opt_4281_, 0);
v_defValue_4283_ = lean_ctor_get(v_opt_4281_, 1);
v_map_4284_ = lean_ctor_get(v_opts_4280_, 0);
v___x_4285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4284_, v_name_4282_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_inc(v_defValue_4283_);
return v_defValue_4283_;
}
else
{
lean_object* v_val_4286_; 
v_val_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_val_4286_);
lean_dec_ref_known(v___x_4285_, 1);
if (lean_obj_tag(v_val_4286_) == 3)
{
lean_object* v_v_4287_; 
v_v_4287_ = lean_ctor_get(v_val_4286_, 0);
lean_inc(v_v_4287_);
lean_dec_ref_known(v_val_4286_, 1);
return v_v_4287_;
}
else
{
lean_dec(v_val_4286_);
lean_inc(v_defValue_4283_);
return v_defValue_4283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed(lean_object* v_opts_4288_, lean_object* v_opt_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_opts_4288_, v_opt_4289_);
lean_dec_ref(v_opt_4289_);
lean_dec_ref(v_opts_4288_);
return v_res_4290_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4291_; double v___x_4292_; 
v___x_4291_ = lean_unsigned_to_nat(0u);
v___x_4292_ = lean_float_of_nat(v___x_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(lean_object* v_cls_4296_, lean_object* v_msg_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v_ref_4303_; lean_object* v___x_4304_; lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4350_; 
v_ref_4303_ = lean_ctor_get(v___y_4300_, 2);
v___x_4304_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4307_ = v___x_4304_;
v_isShared_4308_ = v_isSharedCheck_4350_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4304_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4350_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4309_; lean_object* v_traceState_4310_; lean_object* v_env_4311_; lean_object* v_nextMacroScope_4312_; lean_object* v_ngen_4313_; lean_object* v_auxDeclNGen_4314_; lean_object* v_cache_4315_; lean_object* v_recordedDeps_4316_; lean_object* v_messages_4317_; lean_object* v_infoState_4318_; lean_object* v_snapshotTasks_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4349_; 
v___x_4309_ = lean_st_ref_take(v___y_4301_);
v_traceState_4310_ = lean_ctor_get(v___x_4309_, 4);
v_env_4311_ = lean_ctor_get(v___x_4309_, 0);
v_nextMacroScope_4312_ = lean_ctor_get(v___x_4309_, 1);
v_ngen_4313_ = lean_ctor_get(v___x_4309_, 2);
v_auxDeclNGen_4314_ = lean_ctor_get(v___x_4309_, 3);
v_cache_4315_ = lean_ctor_get(v___x_4309_, 5);
v_recordedDeps_4316_ = lean_ctor_get(v___x_4309_, 6);
v_messages_4317_ = lean_ctor_get(v___x_4309_, 7);
v_infoState_4318_ = lean_ctor_get(v___x_4309_, 8);
v_snapshotTasks_4319_ = lean_ctor_get(v___x_4309_, 9);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4321_ = v___x_4309_;
v_isShared_4322_ = v_isSharedCheck_4349_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_snapshotTasks_4319_);
lean_inc(v_infoState_4318_);
lean_inc(v_messages_4317_);
lean_inc(v_recordedDeps_4316_);
lean_inc(v_cache_4315_);
lean_inc(v_traceState_4310_);
lean_inc(v_auxDeclNGen_4314_);
lean_inc(v_ngen_4313_);
lean_inc(v_nextMacroScope_4312_);
lean_inc(v_env_4311_);
lean_dec(v___x_4309_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4349_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
uint64_t v_tid_4323_; lean_object* v_traces_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4348_; 
v_tid_4323_ = lean_ctor_get_uint64(v_traceState_4310_, sizeof(void*)*1);
v_traces_4324_ = lean_ctor_get(v_traceState_4310_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v_traceState_4310_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4326_ = v_traceState_4310_;
v_isShared_4327_ = v_isSharedCheck_4348_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_traces_4324_);
lean_dec(v_traceState_4310_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4348_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; double v___x_4330_; uint8_t v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4339_; 
v___x_4328_ = lean_box(0);
v___x_4329_ = lean_box(0);
v___x_4330_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0);
v___x_4331_ = 0;
v___x_4332_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__1));
v___x_4333_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4333_, 0, v_cls_4296_);
lean_ctor_set(v___x_4333_, 1, v___x_4329_);
lean_ctor_set(v___x_4333_, 2, v___x_4332_);
lean_ctor_set_float(v___x_4333_, sizeof(void*)*3, v___x_4330_);
lean_ctor_set_float(v___x_4333_, sizeof(void*)*3 + 8, v___x_4330_);
lean_ctor_set_uint8(v___x_4333_, sizeof(void*)*3 + 16, v___x_4331_);
v___x_4334_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__2));
v___x_4335_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4333_);
lean_ctor_set(v___x_4335_, 1, v_a_4305_);
lean_ctor_set(v___x_4335_, 2, v___x_4334_);
lean_inc(v_ref_4303_);
v___x_4336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4336_, 0, v_ref_4303_);
lean_ctor_set(v___x_4336_, 1, v___x_4335_);
v___x_4337_ = l_Lean_PersistentArray_push___redArg(v_traces_4324_, v___x_4336_);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v___x_4337_);
v___x_4339_ = v___x_4326_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v___x_4337_);
lean_ctor_set_uint64(v_reuseFailAlloc_4347_, sizeof(void*)*1, v_tid_4323_);
v___x_4339_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4341_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 4, v___x_4339_);
v___x_4341_ = v___x_4321_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_env_4311_);
lean_ctor_set(v_reuseFailAlloc_4346_, 1, v_nextMacroScope_4312_);
lean_ctor_set(v_reuseFailAlloc_4346_, 2, v_ngen_4313_);
lean_ctor_set(v_reuseFailAlloc_4346_, 3, v_auxDeclNGen_4314_);
lean_ctor_set(v_reuseFailAlloc_4346_, 4, v___x_4339_);
lean_ctor_set(v_reuseFailAlloc_4346_, 5, v_cache_4315_);
lean_ctor_set(v_reuseFailAlloc_4346_, 6, v_recordedDeps_4316_);
lean_ctor_set(v_reuseFailAlloc_4346_, 7, v_messages_4317_);
lean_ctor_set(v_reuseFailAlloc_4346_, 8, v_infoState_4318_);
lean_ctor_set(v_reuseFailAlloc_4346_, 9, v_snapshotTasks_4319_);
v___x_4341_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
lean_object* v___x_4342_; lean_object* v___x_4344_; 
v___x_4342_ = lean_st_ref_put(v___y_4301_, v___x_4341_);
if (v_isShared_4308_ == 0)
{
lean_ctor_set(v___x_4307_, 0, v___x_4328_);
v___x_4344_ = v___x_4307_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4328_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___boxed(lean_object* v_cls_4351_, lean_object* v_msg_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v_cls_4351_, v_msg_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
return v_res_4358_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4368_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4369_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4370_ = l_Lean_Name_append(v___x_4369_, v___x_4368_);
return v___x_4370_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4372_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__6));
v___x_4373_ = l_Lean_stringToMessageData(v___x_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object* v_levelParams_4374_, lean_object* v_declName_4375_, lean_object* v_wfPreprocessProof_4376_, lean_object* v___x_4377_, lean_object* v_unaryPreDefName_4378_, lean_object* v_xs_4379_, lean_object* v_body_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4389_ = lean_box(0);
lean_inc(v_levelParams_4374_);
v___x_4390_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4374_, v___x_4389_);
lean_inc(v_declName_4375_);
v___x_4391_ = l_Lean_mkConst(v_declName_4375_, v___x_4390_);
v___x_4392_ = l_Lean_mkAppN(v___x_4391_, v_xs_4379_);
v___x_4393_ = l_Lean_Meta_mkEq(v___x_4392_, v_body_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc_n(v_a_4394_, 2);
lean_dec_ref_known(v___x_4393_, 1);
v___x_4395_ = lean_box(0);
v___x_4396_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4394_, v___x_4395_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_a_4397_);
lean_dec_ref_known(v___x_4396_, 1);
v___x_4398_ = l_Lean_Expr_mvarId_x21(v_a_4397_);
v___x_4399_ = l_Lean_Meta_Simp_Result_addExtraArgs(v_wfPreprocessProof_4376_, v_xs_4379_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; uint8_t v___x_4403_; lean_object* v_mvarId_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref_known(v___x_4399_, 1);
v___x_4401_ = l_Lean_Expr_appFn_x21(v_a_4394_);
v___x_4402_ = lean_box(0);
v___x_4403_ = 1;
v___x_4478_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4478_, 0, v___x_4401_);
lean_ctor_set(v___x_4478_, 1, v___x_4402_);
lean_ctor_set_uint8(v___x_4478_, sizeof(void*)*2, v___x_4403_);
v___x_4479_ = l_Lean_Meta_Simp_mkCongr(v___x_4478_, v_a_4400_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; lean_object* v___x_4481_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref_known(v___x_4479_, 1);
v___x_4481_ = l_Lean_Meta_applySimpResultToTarget(v___x_4398_, v_a_4394_, v_a_4480_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; uint8_t v___x_4483_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v___x_4481_, 1);
v___x_4483_ = lean_name_eq(v_declName_4375_, v_unaryPreDefName_4378_);
if (v___x_4483_ == 0)
{
lean_object* v___x_4484_; 
v___x_4484_ = l_Lean_Elab_Eqns_deltaLHS(v_a_4482_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4485_);
lean_dec_ref_known(v___x_4484_, 1);
v_mvarId_4405_ = v_a_4485_;
v___y_4406_ = v___y_4381_;
v___y_4407_ = v___y_4382_;
v___y_4408_ = v___y_4383_;
v___y_4409_ = v___y_4384_;
goto v___jp_4404_;
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec(v_a_4397_);
lean_dec(v_a_4394_);
lean_dec(v___x_4377_);
lean_dec(v_declName_4375_);
lean_dec(v_levelParams_4374_);
v_a_4486_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4484_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4484_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
else
{
v_mvarId_4405_ = v_a_4482_;
v___y_4406_ = v___y_4381_;
v___y_4407_ = v___y_4382_;
v___y_4408_ = v___y_4383_;
v___y_4409_ = v___y_4384_;
goto v___jp_4404_;
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v_a_4397_);
lean_dec(v_a_4394_);
lean_dec(v___x_4377_);
lean_dec(v_declName_4375_);
lean_dec(v_levelParams_4374_);
v_a_4494_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4481_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4481_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
lean_dec(v___x_4398_);
lean_dec(v_a_4397_);
lean_dec(v_a_4394_);
lean_dec(v___x_4377_);
lean_dec(v_declName_4375_);
lean_dec(v_levelParams_4374_);
v_a_4502_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4479_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4479_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
v___jp_4404_:
{
lean_object* v___x_4410_; 
v___x_4410_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v___x_4412_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4375_, v_a_4411_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v___x_4413_; lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4469_; 
lean_dec_ref_known(v___x_4412_, 1);
v___x_4413_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4397_, v___y_4407_);
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4416_ = v___x_4413_;
v_isShared_4417_ = v_isSharedCheck_4469_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4413_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4469_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
uint8_t v___x_4418_; uint8_t v___x_4419_; lean_object* v___x_4420_; 
v___x_4418_ = 0;
v___x_4419_ = 1;
v___x_4420_ = l_Lean_Meta_mkForallFVars(v_xs_4379_, v_a_4394_, v___x_4418_, v___x_4403_, v___x_4403_, v___x_4419_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v___x_4422_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4420_, 1);
v___x_4422_ = l_Lean_Meta_letToHave(v_a_4421_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4424_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
lean_inc(v_a_4423_);
lean_dec_ref_known(v___x_4422_, 1);
v___x_4424_ = l_Lean_Meta_mkLambdaFVars(v_xs_4379_, v_a_4414_, v___x_4418_, v___x_4403_, v___x_4418_, v___x_4403_, v___x_4419_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4430_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
lean_dec_ref_known(v___x_4424_, 1);
lean_inc_n(v___x_4377_, 2);
v___x_4426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4377_);
lean_ctor_set(v___x_4426_, 1, v_levelParams_4374_);
lean_ctor_set(v___x_4426_, 2, v_a_4423_);
v___x_4427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4377_);
lean_ctor_set(v___x_4427_, 1, v___x_4389_);
v___x_4428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4426_);
lean_ctor_set(v___x_4428_, 1, v_a_4425_);
lean_ctor_set(v___x_4428_, 2, v___x_4427_);
if (v_isShared_4417_ == 0)
{
lean_ctor_set_tag(v___x_4416_, 2);
lean_ctor_set(v___x_4416_, 0, v___x_4428_);
v___x_4430_ = v___x_4416_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
lean_object* v___x_4431_; 
v___x_4431_ = l_Lean_addDecl(v___x_4430_, v___x_4418_, v___y_4408_, v___y_4409_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v___x_4432_; 
lean_dec_ref_known(v___x_4431_, 1);
lean_inc(v___x_4377_);
v___x_4432_ = l_Lean_inferDefEqAttr(v___x_4377_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_toCold_4433_; lean_object* v_options_4434_; uint8_t v_hasTrace_4435_; 
lean_dec_ref_known(v___x_4432_, 1);
v_toCold_4433_ = lean_ctor_get(v___y_4408_, 0);
v_options_4434_ = lean_ctor_get(v_toCold_4433_, 2);
v_hasTrace_4435_ = lean_ctor_get_uint8(v_options_4434_, sizeof(void*)*1);
if (v_hasTrace_4435_ == 0)
{
lean_dec(v___x_4377_);
goto v___jp_4386_;
}
else
{
lean_object* v_inheritedTraceOptions_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; uint8_t v___x_4439_; 
v_inheritedTraceOptions_4436_ = lean_ctor_get(v_toCold_4433_, 11);
v___x_4437_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4438_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_4439_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4436_, v_options_4434_, v___x_4438_);
if (v___x_4439_ == 0)
{
lean_dec(v___x_4377_);
goto v___jp_4386_;
}
else
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4440_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7);
v___x_4441_ = l_Lean_MessageData_ofConstName(v___x_4377_, v___x_4418_);
v___x_4442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4440_);
lean_ctor_set(v___x_4442_, 1, v___x_4441_);
v___x_4443_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_4437_, v___x_4442_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
return v___x_4443_;
}
}
}
else
{
lean_dec(v___x_4377_);
return v___x_4432_;
}
}
else
{
lean_dec(v___x_4377_);
return v___x_4431_;
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec(v_a_4423_);
lean_del_object(v___x_4416_);
lean_dec(v___x_4377_);
lean_dec(v_levelParams_4374_);
v_a_4445_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4424_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4424_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_del_object(v___x_4416_);
lean_dec(v_a_4414_);
lean_dec(v___x_4377_);
lean_dec(v_levelParams_4374_);
v_a_4453_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4422_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4422_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
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
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_del_object(v___x_4416_);
lean_dec(v_a_4414_);
lean_dec(v___x_4377_);
lean_dec(v_levelParams_4374_);
v_a_4461_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4420_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4420_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
}
else
{
lean_dec(v_a_4397_);
lean_dec(v_a_4394_);
lean_dec(v___x_4377_);
lean_dec(v_levelParams_4374_);
return v___x_4412_;
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec(v_a_4397_);
lean_dec(v_a_4394_);
lean_dec(v___x_4377_);
lean_dec(v_declName_4375_);
lean_dec(v_levelParams_4374_);
v_a_4470_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4410_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4410_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
lean_dec(v___x_4398_);
lean_dec(v_a_4397_);
lean_dec(v_a_4394_);
lean_dec(v___x_4377_);
lean_dec(v_declName_4375_);
lean_dec(v_levelParams_4374_);
v_a_4510_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4399_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4399_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
lean_dec(v_a_4394_);
lean_dec(v___x_4377_);
lean_dec_ref(v_wfPreprocessProof_4376_);
lean_dec(v_declName_4375_);
lean_dec(v_levelParams_4374_);
v_a_4518_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4396_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4396_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4523_; 
if (v_isShared_4521_ == 0)
{
v___x_4523_ = v___x_4520_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4518_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_dec(v___x_4377_);
lean_dec_ref(v_wfPreprocessProof_4376_);
lean_dec(v_declName_4375_);
lean_dec(v_levelParams_4374_);
v_a_4526_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4393_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4393_);
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
v___jp_4386_:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = lean_box(0);
v___x_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
return v___x_4388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object* v_levelParams_4534_, lean_object* v_declName_4535_, lean_object* v_wfPreprocessProof_4536_, lean_object* v___x_4537_, lean_object* v_unaryPreDefName_4538_, lean_object* v_xs_4539_, lean_object* v_body_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_Elab_WF_mkUnfoldEq___lam__0(v_levelParams_4534_, v_declName_4535_, v_wfPreprocessProof_4536_, v___x_4537_, v_unaryPreDefName_4538_, v_xs_4539_, v_body_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec_ref(v_xs_4539_);
lean_dec(v_unaryPreDefName_4538_);
return v_res_4546_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg(){
_start:
{
lean_object* v___x_4550_; 
v___x_4550_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg___closed__0);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v___dummy_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg();
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(lean_object* v___y_4553_, uint8_t v_isExporting_4554_, lean_object* v___x_4555_, lean_object* v___y_4556_, lean_object* v___x_4557_, lean_object* v_a_x3f_4558_){
_start:
{
lean_object* v___x_4560_; lean_object* v_env_4561_; lean_object* v_nextMacroScope_4562_; lean_object* v_ngen_4563_; lean_object* v_auxDeclNGen_4564_; lean_object* v_traceState_4565_; lean_object* v_recordedDeps_4566_; lean_object* v_messages_4567_; lean_object* v_infoState_4568_; lean_object* v_snapshotTasks_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4594_; 
v___x_4560_ = lean_st_ref_take(v___y_4553_);
v_env_4561_ = lean_ctor_get(v___x_4560_, 0);
v_nextMacroScope_4562_ = lean_ctor_get(v___x_4560_, 1);
v_ngen_4563_ = lean_ctor_get(v___x_4560_, 2);
v_auxDeclNGen_4564_ = lean_ctor_get(v___x_4560_, 3);
v_traceState_4565_ = lean_ctor_get(v___x_4560_, 4);
v_recordedDeps_4566_ = lean_ctor_get(v___x_4560_, 6);
v_messages_4567_ = lean_ctor_get(v___x_4560_, 7);
v_infoState_4568_ = lean_ctor_get(v___x_4560_, 8);
v_snapshotTasks_4569_ = lean_ctor_get(v___x_4560_, 9);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4594_ == 0)
{
lean_object* v_unused_4595_; 
v_unused_4595_ = lean_ctor_get(v___x_4560_, 5);
lean_dec(v_unused_4595_);
v___x_4571_ = v___x_4560_;
v_isShared_4572_ = v_isSharedCheck_4594_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_snapshotTasks_4569_);
lean_inc(v_infoState_4568_);
lean_inc(v_messages_4567_);
lean_inc(v_recordedDeps_4566_);
lean_inc(v_traceState_4565_);
lean_inc(v_auxDeclNGen_4564_);
lean_inc(v_ngen_4563_);
lean_inc(v_nextMacroScope_4562_);
lean_inc(v_env_4561_);
lean_dec(v___x_4560_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4594_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4573_; lean_object* v___x_4575_; 
v___x_4573_ = l_Lean_Environment_setExporting(v_env_4561_, v_isExporting_4554_);
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 5, v___x_4555_);
lean_ctor_set(v___x_4571_, 0, v___x_4573_);
v___x_4575_ = v___x_4571_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4573_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v_nextMacroScope_4562_);
lean_ctor_set(v_reuseFailAlloc_4593_, 2, v_ngen_4563_);
lean_ctor_set(v_reuseFailAlloc_4593_, 3, v_auxDeclNGen_4564_);
lean_ctor_set(v_reuseFailAlloc_4593_, 4, v_traceState_4565_);
lean_ctor_set(v_reuseFailAlloc_4593_, 5, v___x_4555_);
lean_ctor_set(v_reuseFailAlloc_4593_, 6, v_recordedDeps_4566_);
lean_ctor_set(v_reuseFailAlloc_4593_, 7, v_messages_4567_);
lean_ctor_set(v_reuseFailAlloc_4593_, 8, v_infoState_4568_);
lean_ctor_set(v_reuseFailAlloc_4593_, 9, v_snapshotTasks_4569_);
v___x_4575_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v_mctx_4578_; lean_object* v_zetaDeltaFVarIds_4579_; lean_object* v_postponed_4580_; lean_object* v_diag_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4591_; 
v___x_4576_ = lean_st_ref_put(v___y_4553_, v___x_4575_);
v___x_4577_ = lean_st_ref_take(v___y_4556_);
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
lean_object* v___x_4585_; lean_object* v___x_4587_; 
v___x_4585_ = lean_box(0);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 1, v___x_4557_);
v___x_4587_ = v___x_4583_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_mctx_4578_);
lean_ctor_set(v_reuseFailAlloc_4590_, 1, v___x_4557_);
lean_ctor_set(v_reuseFailAlloc_4590_, 2, v_zetaDeltaFVarIds_4579_);
lean_ctor_set(v_reuseFailAlloc_4590_, 3, v_postponed_4580_);
lean_ctor_set(v_reuseFailAlloc_4590_, 4, v_diag_4581_);
v___x_4587_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4588_ = lean_st_ref_put(v___y_4556_, v___x_4587_);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4585_);
return v___x_4589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v___y_4596_, lean_object* v_isExporting_4597_, lean_object* v___x_4598_, lean_object* v___y_4599_, lean_object* v___x_4600_, lean_object* v_a_x3f_4601_, lean_object* v___y_4602_){
_start:
{
uint8_t v_isExporting_boxed_4603_; lean_object* v_res_4604_; 
v_isExporting_boxed_4603_ = lean_unbox(v_isExporting_4597_);
v_res_4604_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(v___y_4596_, v_isExporting_boxed_4603_, v___x_4598_, v___y_4599_, v___x_4600_, v_a_x3f_4601_);
lean_dec(v_a_x3f_4601_);
lean_dec(v___y_4599_);
lean_dec(v___y_4596_);
return v_res_4604_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4605_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4605_);
return v___x_4606_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4607_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0);
v___x_4608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
lean_ctor_set(v___x_4608_, 1, v___x_4607_);
return v___x_4608_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_4609_; 
v___x_4609_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7___redArg();
return v___x_4609_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4610_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0);
v___x_4611_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2);
v___x_4612_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
lean_ctor_set(v___x_4612_, 1, v___x_4610_);
lean_ctor_set(v___x_4612_, 2, v___x_4610_);
lean_ctor_set(v___x_4612_, 3, v___x_4610_);
lean_ctor_set(v___x_4612_, 4, v___x_4610_);
lean_ctor_set(v___x_4612_, 5, v___x_4610_);
lean_ctor_set(v___x_4612_, 6, v___x_4610_);
return v___x_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(lean_object* v_x_4613_, uint8_t v_isExporting_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
lean_object* v___x_4620_; lean_object* v_env_4621_; lean_object* v___x_4622_; uint8_t v_isModule_4623_; 
v___x_4620_ = lean_st_ref_get(v___y_4618_);
v_env_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc_ref(v_env_4621_);
lean_dec(v___x_4620_);
v___x_4622_ = l_Lean_Environment_header(v_env_4621_);
v_isModule_4623_ = lean_ctor_get_uint8(v___x_4622_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4622_);
if (v_isModule_4623_ == 0)
{
lean_object* v___x_4624_; 
lean_dec_ref(v_env_4621_);
lean_inc(v___y_4618_);
lean_inc_ref(v___y_4617_);
lean_inc(v___y_4616_);
lean_inc_ref(v___y_4615_);
v___x_4624_ = lean_apply_5(v_x_4613_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, lean_box(0));
return v___x_4624_;
}
else
{
uint8_t v_isExporting_4625_; 
v_isExporting_4625_ = lean_ctor_get_uint8(v_env_4621_, sizeof(void*)*13);
lean_dec_ref(v_env_4621_);
if (v_isExporting_4614_ == 0)
{
if (v_isExporting_4625_ == 0)
{
lean_object* v___x_4692_; 
lean_inc(v___y_4618_);
lean_inc_ref(v___y_4617_);
lean_inc(v___y_4616_);
lean_inc_ref(v___y_4615_);
v___x_4692_ = lean_apply_5(v_x_4613_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, lean_box(0));
return v___x_4692_;
}
else
{
goto v___jp_4626_;
}
}
else
{
if (v_isExporting_4625_ == 0)
{
goto v___jp_4626_;
}
else
{
lean_object* v___x_4693_; 
lean_inc(v___y_4618_);
lean_inc_ref(v___y_4617_);
lean_inc(v___y_4616_);
lean_inc_ref(v___y_4615_);
v___x_4693_ = lean_apply_5(v_x_4613_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, lean_box(0));
return v___x_4693_;
}
}
v___jp_4626_:
{
lean_object* v___x_4627_; lean_object* v_env_4628_; lean_object* v_nextMacroScope_4629_; lean_object* v_ngen_4630_; lean_object* v_auxDeclNGen_4631_; lean_object* v_traceState_4632_; lean_object* v_recordedDeps_4633_; lean_object* v_messages_4634_; lean_object* v_infoState_4635_; lean_object* v_snapshotTasks_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4690_; 
v___x_4627_ = lean_st_ref_take(v___y_4618_);
v_env_4628_ = lean_ctor_get(v___x_4627_, 0);
v_nextMacroScope_4629_ = lean_ctor_get(v___x_4627_, 1);
v_ngen_4630_ = lean_ctor_get(v___x_4627_, 2);
v_auxDeclNGen_4631_ = lean_ctor_get(v___x_4627_, 3);
v_traceState_4632_ = lean_ctor_get(v___x_4627_, 4);
v_recordedDeps_4633_ = lean_ctor_get(v___x_4627_, 6);
v_messages_4634_ = lean_ctor_get(v___x_4627_, 7);
v_infoState_4635_ = lean_ctor_get(v___x_4627_, 8);
v_snapshotTasks_4636_ = lean_ctor_get(v___x_4627_, 9);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4690_ == 0)
{
lean_object* v_unused_4691_; 
v_unused_4691_ = lean_ctor_get(v___x_4627_, 5);
lean_dec(v_unused_4691_);
v___x_4638_ = v___x_4627_;
v_isShared_4639_ = v_isSharedCheck_4690_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_snapshotTasks_4636_);
lean_inc(v_infoState_4635_);
lean_inc(v_messages_4634_);
lean_inc(v_recordedDeps_4633_);
lean_inc(v_traceState_4632_);
lean_inc(v_auxDeclNGen_4631_);
lean_inc(v_ngen_4630_);
lean_inc(v_nextMacroScope_4629_);
lean_inc(v_env_4628_);
lean_dec(v___x_4627_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4690_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4643_; 
v___x_4640_ = l_Lean_Environment_setExporting(v_env_4628_, v_isExporting_4614_);
v___x_4641_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 5, v___x_4641_);
lean_ctor_set(v___x_4638_, 0, v___x_4640_);
v___x_4643_ = v___x_4638_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v___x_4640_);
lean_ctor_set(v_reuseFailAlloc_4689_, 1, v_nextMacroScope_4629_);
lean_ctor_set(v_reuseFailAlloc_4689_, 2, v_ngen_4630_);
lean_ctor_set(v_reuseFailAlloc_4689_, 3, v_auxDeclNGen_4631_);
lean_ctor_set(v_reuseFailAlloc_4689_, 4, v_traceState_4632_);
lean_ctor_set(v_reuseFailAlloc_4689_, 5, v___x_4641_);
lean_ctor_set(v_reuseFailAlloc_4689_, 6, v_recordedDeps_4633_);
lean_ctor_set(v_reuseFailAlloc_4689_, 7, v_messages_4634_);
lean_ctor_set(v_reuseFailAlloc_4689_, 8, v_infoState_4635_);
lean_ctor_set(v_reuseFailAlloc_4689_, 9, v_snapshotTasks_4636_);
v___x_4643_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v_mctx_4646_; lean_object* v_zetaDeltaFVarIds_4647_; lean_object* v_postponed_4648_; lean_object* v_diag_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4687_; 
v___x_4644_ = lean_st_ref_put(v___y_4618_, v___x_4643_);
v___x_4645_ = lean_st_ref_take(v___y_4616_);
v_mctx_4646_ = lean_ctor_get(v___x_4645_, 0);
v_zetaDeltaFVarIds_4647_ = lean_ctor_get(v___x_4645_, 2);
v_postponed_4648_ = lean_ctor_get(v___x_4645_, 3);
v_diag_4649_ = lean_ctor_get(v___x_4645_, 4);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4687_ == 0)
{
lean_object* v_unused_4688_; 
v_unused_4688_ = lean_ctor_get(v___x_4645_, 1);
lean_dec(v_unused_4688_);
v___x_4651_ = v___x_4645_;
v_isShared_4652_ = v_isSharedCheck_4687_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_diag_4649_);
lean_inc(v_postponed_4648_);
lean_inc(v_zetaDeltaFVarIds_4647_);
lean_inc(v_mctx_4646_);
lean_dec(v___x_4645_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4687_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4653_; lean_object* v___x_4655_; 
v___x_4653_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__3);
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 1, v___x_4653_);
v___x_4655_ = v___x_4651_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_mctx_4646_);
lean_ctor_set(v_reuseFailAlloc_4686_, 1, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4686_, 2, v_zetaDeltaFVarIds_4647_);
lean_ctor_set(v_reuseFailAlloc_4686_, 3, v_postponed_4648_);
lean_ctor_set(v_reuseFailAlloc_4686_, 4, v_diag_4649_);
v___x_4655_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
lean_object* v___x_4656_; lean_object* v_r_4657_; 
v___x_4656_ = lean_st_ref_put(v___y_4616_, v___x_4655_);
lean_inc(v___y_4618_);
lean_inc_ref(v___y_4617_);
lean_inc(v___y_4616_);
lean_inc_ref(v___y_4615_);
v_r_4657_ = lean_apply_5(v_x_4613_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, lean_box(0));
if (lean_obj_tag(v_r_4657_) == 0)
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4674_; 
v_a_4658_ = lean_ctor_get(v_r_4657_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v_r_4657_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4660_ = v_r_4657_;
v_isShared_4661_ = v_isSharedCheck_4674_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v_r_4657_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4674_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
lean_inc(v_a_4658_);
if (v_isShared_4661_ == 0)
{
lean_ctor_set_tag(v___x_4660_, 1);
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
lean_object* v___x_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
v___x_4664_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(v___y_4618_, v_isExporting_4625_, v___x_4641_, v___y_4616_, v___x_4653_, v___x_4663_);
lean_dec_ref(v___x_4663_);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4671_ == 0)
{
lean_object* v_unused_4672_; 
v_unused_4672_ = lean_ctor_get(v___x_4664_, 0);
lean_dec(v_unused_4672_);
v___x_4666_ = v___x_4664_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_dec(v___x_4664_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 0, v_a_4658_);
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4658_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
}
else
{
lean_object* v_a_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
v_a_4675_ = lean_ctor_get(v_r_4657_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v_r_4657_, 1);
v___x_4676_ = lean_box(0);
v___x_4677_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(v___y_4618_, v_isExporting_4625_, v___x_4641_, v___y_4616_, v___x_4653_, v___x_4676_);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4684_ == 0)
{
lean_object* v_unused_4685_; 
v_unused_4685_ = lean_ctor_get(v___x_4677_, 0);
lean_dec(v_unused_4685_);
v___x_4679_ = v___x_4677_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_dec(v___x_4677_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
lean_ctor_set_tag(v___x_4679_, 1);
lean_ctor_set(v___x_4679_, 0, v_a_4675_);
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4675_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___boxed(lean_object* v_x_4694_, lean_object* v_isExporting_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
uint8_t v_isExporting_boxed_4701_; lean_object* v_res_4702_; 
v_isExporting_boxed_4701_ = lean_unbox(v_isExporting_4695_);
v_res_4702_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(v_x_4694_, v_isExporting_boxed_4701_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(lean_object* v_x_4703_, uint8_t v_when_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
if (v_when_4704_ == 0)
{
lean_object* v___x_4710_; 
lean_inc(v___y_4708_);
lean_inc_ref(v___y_4707_);
lean_inc(v___y_4706_);
lean_inc_ref(v___y_4705_);
v___x_4710_ = lean_apply_5(v_x_4703_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, lean_box(0));
return v___x_4710_;
}
else
{
uint8_t v___x_4711_; lean_object* v___x_4712_; 
v___x_4711_ = 0;
v___x_4712_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(v_x_4703_, v___x_4711_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
return v___x_4712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg___boxed(lean_object* v_x_4713_, lean_object* v_when_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
uint8_t v_when_boxed_4720_; lean_object* v_res_4721_; 
v_when_boxed_4720_ = lean_unbox(v_when_4714_);
v_res_4721_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(v_x_4713_, v_when_boxed_4720_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5(lean_object* v_o_4722_, lean_object* v_k_4723_, uint8_t v_v_4724_){
_start:
{
lean_object* v_map_4725_; uint8_t v_hasTrace_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4740_; 
v_map_4725_ = lean_ctor_get(v_o_4722_, 0);
v_hasTrace_4726_ = lean_ctor_get_uint8(v_o_4722_, sizeof(void*)*1);
v_isSharedCheck_4740_ = !lean_is_exclusive(v_o_4722_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4728_ = v_o_4722_;
v_isShared_4729_ = v_isSharedCheck_4740_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_map_4725_);
lean_dec(v_o_4722_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4740_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4730_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4730_, 0, v_v_4724_);
lean_inc(v_k_4723_);
v___x_4731_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4723_, v___x_4730_, v_map_4725_);
if (v_hasTrace_4726_ == 0)
{
lean_object* v___x_4732_; uint8_t v___x_4733_; lean_object* v___x_4735_; 
v___x_4732_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4733_ = l_Lean_Name_isPrefixOf(v___x_4732_, v_k_4723_);
lean_dec(v_k_4723_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 0, v___x_4731_);
v___x_4735_ = v___x_4728_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v___x_4731_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
lean_ctor_set_uint8(v___x_4735_, sizeof(void*)*1, v___x_4733_);
return v___x_4735_;
}
}
else
{
lean_object* v___x_4738_; 
lean_dec(v_k_4723_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 0, v___x_4731_);
v___x_4738_ = v___x_4728_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___x_4731_);
lean_ctor_set_uint8(v_reuseFailAlloc_4739_, sizeof(void*)*1, v_hasTrace_4726_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5___boxed(lean_object* v_o_4741_, lean_object* v_k_4742_, lean_object* v_v_4743_){
_start:
{
uint8_t v_v_boxed_4744_; lean_object* v_res_4745_; 
v_v_boxed_4744_ = lean_unbox(v_v_4743_);
v_res_4745_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5(v_o_4741_, v_k_4742_, v_v_boxed_4744_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(lean_object* v_opts_4746_, lean_object* v_opt_4747_, uint8_t v_val_4748_){
_start:
{
lean_object* v_name_4749_; lean_object* v___x_4750_; 
v_name_4749_ = lean_ctor_get(v_opt_4747_, 0);
lean_inc(v_name_4749_);
lean_dec_ref(v_opt_4747_);
v___x_4750_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5(v_opts_4746_, v_name_4749_, v_val_4748_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4___boxed(lean_object* v_opts_4751_, lean_object* v_opt_4752_, lean_object* v_val_4753_){
_start:
{
uint8_t v_val_boxed_4754_; lean_object* v_res_4755_; 
v_val_boxed_4754_ = lean_unbox(v_val_4753_);
v_res_4755_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_opts_4751_, v_opt_4752_, v_val_boxed_4754_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(lean_object* v___x_4756_, uint8_t v___x_4757_, uint8_t v___x_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_){
_start:
{
lean_object* v___y_4765_; uint16_t v___y_4766_; lean_object* v_fileName_4767_; lean_object* v_fileMap_4768_; lean_object* v_currNamespace_4769_; lean_object* v_openDecls_4770_; lean_object* v_initHeartbeats_4771_; lean_object* v_maxHeartbeats_4772_; lean_object* v_quotContext_4773_; lean_object* v_currMacroScope_4774_; lean_object* v_cancelTk_x3f_4775_; lean_object* v_inheritedTraceOptions_4776_; lean_object* v_currRecDepth_4777_; lean_object* v_ref_4778_; uint8_t v_suppressElabErrors_4779_; uint8_t v_checkDeprecated_4780_; uint8_t v_isRecordingDeps_4781_; lean_object* v___y_4782_; lean_object* v_toCold_4788_; lean_object* v_currRecDepth_4789_; lean_object* v_ref_4790_; uint8_t v_suppressElabErrors_4791_; uint8_t v_checkDeprecated_4792_; uint8_t v_isRecordingDeps_4793_; lean_object* v_fileName_4794_; lean_object* v_fileMap_4795_; lean_object* v_options_4796_; lean_object* v_currNamespace_4797_; lean_object* v_openDecls_4798_; lean_object* v_initHeartbeats_4799_; lean_object* v_maxHeartbeats_4800_; lean_object* v_quotContext_4801_; lean_object* v_currMacroScope_4802_; lean_object* v_cancelTk_x3f_4803_; lean_object* v_inheritedTraceOptions_4804_; lean_object* v___y_4806_; uint16_t v___y_4807_; uint8_t v___y_4808_; lean_object* v___y_4831_; 
v_toCold_4788_ = lean_ctor_get(v___y_4761_, 0);
v_currRecDepth_4789_ = lean_ctor_get(v___y_4761_, 1);
v_ref_4790_ = lean_ctor_get(v___y_4761_, 2);
v_suppressElabErrors_4791_ = lean_ctor_get_uint8(v___y_4761_, sizeof(void*)*3 + 2);
v_checkDeprecated_4792_ = lean_ctor_get_uint8(v___y_4761_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4793_ = lean_ctor_get_uint8(v___y_4761_, sizeof(void*)*3 + 4);
v_fileName_4794_ = lean_ctor_get(v_toCold_4788_, 0);
v_fileMap_4795_ = lean_ctor_get(v_toCold_4788_, 1);
v_options_4796_ = lean_ctor_get(v_toCold_4788_, 2);
v_currNamespace_4797_ = lean_ctor_get(v_toCold_4788_, 4);
v_openDecls_4798_ = lean_ctor_get(v_toCold_4788_, 5);
v_initHeartbeats_4799_ = lean_ctor_get(v_toCold_4788_, 6);
v_maxHeartbeats_4800_ = lean_ctor_get(v_toCold_4788_, 7);
v_quotContext_4801_ = lean_ctor_get(v_toCold_4788_, 8);
v_currMacroScope_4802_ = lean_ctor_get(v_toCold_4788_, 9);
v_cancelTk_x3f_4803_ = lean_ctor_get(v_toCold_4788_, 10);
v_inheritedTraceOptions_4804_ = lean_ctor_get(v_toCold_4788_, 11);
if (v_isRecordingDeps_4793_ == 0)
{
lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4840_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_4796_);
v___x_4841_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_options_4796_, v___x_4840_, v_isRecordingDeps_4793_);
v___y_4831_ = v___x_4841_;
goto v___jp_4830_;
}
else
{
lean_object* v___x_4842_; 
lean_inc_ref(v_options_4796_);
v___x_4842_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_4796_);
v___y_4831_ = v___x_4842_;
goto v___jp_4830_;
}
v___jp_4764_:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4783_ = l_Lean_maxRecDepth;
v___x_4784_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v___y_4765_, v___x_4783_);
v___x_4785_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4785_, 0, v_fileName_4767_);
lean_ctor_set(v___x_4785_, 1, v_fileMap_4768_);
lean_ctor_set(v___x_4785_, 2, v___y_4765_);
lean_ctor_set(v___x_4785_, 3, v___x_4784_);
lean_ctor_set(v___x_4785_, 4, v_currNamespace_4769_);
lean_ctor_set(v___x_4785_, 5, v_openDecls_4770_);
lean_ctor_set(v___x_4785_, 6, v_initHeartbeats_4771_);
lean_ctor_set(v___x_4785_, 7, v_maxHeartbeats_4772_);
lean_ctor_set(v___x_4785_, 8, v_quotContext_4773_);
lean_ctor_set(v___x_4785_, 9, v_currMacroScope_4774_);
lean_ctor_set(v___x_4785_, 10, v_cancelTk_x3f_4775_);
lean_ctor_set(v___x_4785_, 11, v_inheritedTraceOptions_4776_);
lean_inc(v_ref_4778_);
lean_inc(v_currRecDepth_4777_);
v___x_4786_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4786_, 0, v___x_4785_);
lean_ctor_set(v___x_4786_, 1, v_currRecDepth_4777_);
lean_ctor_set(v___x_4786_, 2, v_ref_4778_);
lean_ctor_set_uint16(v___x_4786_, sizeof(void*)*3, v___y_4766_);
lean_ctor_set_uint8(v___x_4786_, sizeof(void*)*3 + 2, v_suppressElabErrors_4779_);
lean_ctor_set_uint8(v___x_4786_, sizeof(void*)*3 + 3, v_checkDeprecated_4780_);
lean_ctor_set_uint8(v___x_4786_, sizeof(void*)*3 + 4, v_isRecordingDeps_4781_);
v___x_4787_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(v___x_4756_, v___x_4757_, v___y_4759_, v___y_4760_, v___x_4786_, v___y_4782_);
lean_dec_ref_known(v___x_4786_, 3);
return v___x_4787_;
}
v___jp_4805_:
{
lean_object* v___x_4809_; lean_object* v_env_4810_; lean_object* v_nextMacroScope_4811_; lean_object* v_ngen_4812_; lean_object* v_auxDeclNGen_4813_; lean_object* v_traceState_4814_; lean_object* v_recordedDeps_4815_; lean_object* v_messages_4816_; lean_object* v_infoState_4817_; lean_object* v_snapshotTasks_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4828_; 
v___x_4809_ = lean_st_ref_take(v___y_4762_);
v_env_4810_ = lean_ctor_get(v___x_4809_, 0);
v_nextMacroScope_4811_ = lean_ctor_get(v___x_4809_, 1);
v_ngen_4812_ = lean_ctor_get(v___x_4809_, 2);
v_auxDeclNGen_4813_ = lean_ctor_get(v___x_4809_, 3);
v_traceState_4814_ = lean_ctor_get(v___x_4809_, 4);
v_recordedDeps_4815_ = lean_ctor_get(v___x_4809_, 6);
v_messages_4816_ = lean_ctor_get(v___x_4809_, 7);
v_infoState_4817_ = lean_ctor_get(v___x_4809_, 8);
v_snapshotTasks_4818_ = lean_ctor_get(v___x_4809_, 9);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4828_ == 0)
{
lean_object* v_unused_4829_; 
v_unused_4829_ = lean_ctor_get(v___x_4809_, 5);
lean_dec(v_unused_4829_);
v___x_4820_ = v___x_4809_;
v_isShared_4821_ = v_isSharedCheck_4828_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_snapshotTasks_4818_);
lean_inc(v_infoState_4817_);
lean_inc(v_messages_4816_);
lean_inc(v_recordedDeps_4815_);
lean_inc(v_traceState_4814_);
lean_inc(v_auxDeclNGen_4813_);
lean_inc(v_ngen_4812_);
lean_inc(v_nextMacroScope_4811_);
lean_inc(v_env_4810_);
lean_dec(v___x_4809_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4828_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4825_; 
v___x_4822_ = l_Lean_Kernel_enableDiag(v_env_4810_, v___y_4808_);
v___x_4823_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 5, v___x_4823_);
lean_ctor_set(v___x_4820_, 0, v___x_4822_);
v___x_4825_ = v___x_4820_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v___x_4822_);
lean_ctor_set(v_reuseFailAlloc_4827_, 1, v_nextMacroScope_4811_);
lean_ctor_set(v_reuseFailAlloc_4827_, 2, v_ngen_4812_);
lean_ctor_set(v_reuseFailAlloc_4827_, 3, v_auxDeclNGen_4813_);
lean_ctor_set(v_reuseFailAlloc_4827_, 4, v_traceState_4814_);
lean_ctor_set(v_reuseFailAlloc_4827_, 5, v___x_4823_);
lean_ctor_set(v_reuseFailAlloc_4827_, 6, v_recordedDeps_4815_);
lean_ctor_set(v_reuseFailAlloc_4827_, 7, v_messages_4816_);
lean_ctor_set(v_reuseFailAlloc_4827_, 8, v_infoState_4817_);
lean_ctor_set(v_reuseFailAlloc_4827_, 9, v_snapshotTasks_4818_);
v___x_4825_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
lean_object* v___x_4826_; 
v___x_4826_ = lean_st_ref_put(v___y_4762_, v___x_4825_);
lean_inc_ref(v_inheritedTraceOptions_4804_);
lean_inc(v_cancelTk_x3f_4803_);
lean_inc(v_currMacroScope_4802_);
lean_inc(v_quotContext_4801_);
lean_inc(v_maxHeartbeats_4800_);
lean_inc(v_initHeartbeats_4799_);
lean_inc(v_openDecls_4798_);
lean_inc(v_currNamespace_4797_);
lean_inc_ref(v_fileMap_4795_);
lean_inc_ref(v_fileName_4794_);
v___y_4765_ = v___y_4806_;
v___y_4766_ = v___y_4807_;
v_fileName_4767_ = v_fileName_4794_;
v_fileMap_4768_ = v_fileMap_4795_;
v_currNamespace_4769_ = v_currNamespace_4797_;
v_openDecls_4770_ = v_openDecls_4798_;
v_initHeartbeats_4771_ = v_initHeartbeats_4799_;
v_maxHeartbeats_4772_ = v_maxHeartbeats_4800_;
v_quotContext_4773_ = v_quotContext_4801_;
v_currMacroScope_4774_ = v_currMacroScope_4802_;
v_cancelTk_x3f_4775_ = v_cancelTk_x3f_4803_;
v_inheritedTraceOptions_4776_ = v_inheritedTraceOptions_4804_;
v_currRecDepth_4777_ = v_currRecDepth_4789_;
v_ref_4778_ = v_ref_4790_;
v_suppressElabErrors_4779_ = v_suppressElabErrors_4791_;
v_checkDeprecated_4780_ = v_checkDeprecated_4792_;
v_isRecordingDeps_4781_ = v_isRecordingDeps_4793_;
v___y_4782_ = v___y_4762_;
goto v___jp_4764_;
}
}
}
v___jp_4830_:
{
uint16_t v___x_4832_; lean_object* v___x_4833_; lean_object* v_env_4834_; uint8_t v___x_4835_; uint16_t v___x_4836_; uint16_t v___x_4837_; uint16_t v___x_4838_; uint8_t v___x_4839_; 
v___x_4832_ = l_Lean_OptionFlags_ofOptions(v___y_4831_);
v___x_4833_ = lean_st_ref_get(v___y_4762_);
v_env_4834_ = lean_ctor_get(v___x_4833_, 0);
lean_inc_ref(v_env_4834_);
lean_dec(v___x_4833_);
v___x_4835_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4834_);
lean_dec_ref(v_env_4834_);
v___x_4836_ = 512;
v___x_4837_ = lean_uint16_land(v___x_4832_, v___x_4836_);
v___x_4838_ = 0;
v___x_4839_ = lean_uint16_dec_eq(v___x_4837_, v___x_4838_);
if (v___x_4839_ == 0)
{
if (v___x_4835_ == 0)
{
v___y_4806_ = v___y_4831_;
v___y_4807_ = v___x_4832_;
v___y_4808_ = v___x_4757_;
goto v___jp_4805_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_4804_);
lean_inc(v_cancelTk_x3f_4803_);
lean_inc(v_currMacroScope_4802_);
lean_inc(v_quotContext_4801_);
lean_inc(v_maxHeartbeats_4800_);
lean_inc(v_initHeartbeats_4799_);
lean_inc(v_openDecls_4798_);
lean_inc(v_currNamespace_4797_);
lean_inc_ref(v_fileMap_4795_);
lean_inc_ref(v_fileName_4794_);
v___y_4765_ = v___y_4831_;
v___y_4766_ = v___x_4832_;
v_fileName_4767_ = v_fileName_4794_;
v_fileMap_4768_ = v_fileMap_4795_;
v_currNamespace_4769_ = v_currNamespace_4797_;
v_openDecls_4770_ = v_openDecls_4798_;
v_initHeartbeats_4771_ = v_initHeartbeats_4799_;
v_maxHeartbeats_4772_ = v_maxHeartbeats_4800_;
v_quotContext_4773_ = v_quotContext_4801_;
v_currMacroScope_4774_ = v_currMacroScope_4802_;
v_cancelTk_x3f_4775_ = v_cancelTk_x3f_4803_;
v_inheritedTraceOptions_4776_ = v_inheritedTraceOptions_4804_;
v_currRecDepth_4777_ = v_currRecDepth_4789_;
v_ref_4778_ = v_ref_4790_;
v_suppressElabErrors_4779_ = v_suppressElabErrors_4791_;
v_checkDeprecated_4780_ = v_checkDeprecated_4792_;
v_isRecordingDeps_4781_ = v_isRecordingDeps_4793_;
v___y_4782_ = v___y_4762_;
goto v___jp_4764_;
}
}
else
{
if (v___x_4835_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_4804_);
lean_inc(v_cancelTk_x3f_4803_);
lean_inc(v_currMacroScope_4802_);
lean_inc(v_quotContext_4801_);
lean_inc(v_maxHeartbeats_4800_);
lean_inc(v_initHeartbeats_4799_);
lean_inc(v_openDecls_4798_);
lean_inc(v_currNamespace_4797_);
lean_inc_ref(v_fileMap_4795_);
lean_inc_ref(v_fileName_4794_);
v___y_4765_ = v___y_4831_;
v___y_4766_ = v___x_4832_;
v_fileName_4767_ = v_fileName_4794_;
v_fileMap_4768_ = v_fileMap_4795_;
v_currNamespace_4769_ = v_currNamespace_4797_;
v_openDecls_4770_ = v_openDecls_4798_;
v_initHeartbeats_4771_ = v_initHeartbeats_4799_;
v_maxHeartbeats_4772_ = v_maxHeartbeats_4800_;
v_quotContext_4773_ = v_quotContext_4801_;
v_currMacroScope_4774_ = v_currMacroScope_4802_;
v_cancelTk_x3f_4775_ = v_cancelTk_x3f_4803_;
v_inheritedTraceOptions_4776_ = v_inheritedTraceOptions_4804_;
v_currRecDepth_4777_ = v_currRecDepth_4789_;
v_ref_4778_ = v_ref_4790_;
v_suppressElabErrors_4779_ = v_suppressElabErrors_4791_;
v_checkDeprecated_4780_ = v_checkDeprecated_4792_;
v_isRecordingDeps_4781_ = v_isRecordingDeps_4793_;
v___y_4782_ = v___y_4762_;
goto v___jp_4764_;
}
else
{
v___y_4806_ = v___y_4831_;
v___y_4807_ = v___x_4832_;
v___y_4808_ = v___x_4758_;
goto v___jp_4805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object* v___x_4843_, lean_object* v___x_4844_, lean_object* v___x_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_){
_start:
{
uint8_t v___x_10050__boxed_4851_; uint8_t v___x_10051__boxed_4852_; lean_object* v_res_4853_; 
v___x_10050__boxed_4851_ = lean_unbox(v___x_4844_);
v___x_10051__boxed_4852_ = lean_unbox(v___x_4845_);
v_res_4853_ = l_Lean_Elab_WF_mkUnfoldEq___lam__2(v___x_4843_, v___x_10050__boxed_4851_, v___x_10051__boxed_4852_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
return v_res_4853_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4855_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___closed__0));
v___x_4856_ = l_Lean_stringToMessageData(v___x_4855_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object* v_preDef_4857_, lean_object* v_unaryPreDefName_4858_, lean_object* v_wfPreprocessProof_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_){
_start:
{
lean_object* v___x_4865_; lean_object* v_env_4866_; lean_object* v_levelParams_4867_; lean_object* v_declName_4868_; lean_object* v_value_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___f_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___f_4876_; uint8_t v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; uint8_t v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___f_4883_; lean_object* v___x_4884_; 
v___x_4865_ = lean_st_ref_get(v_a_4863_);
v_env_4866_ = lean_ctor_get(v___x_4865_, 0);
lean_inc_ref(v_env_4866_);
lean_dec(v___x_4865_);
v_levelParams_4867_ = lean_ctor_get(v_preDef_4857_, 1);
lean_inc(v_levelParams_4867_);
v_declName_4868_ = lean_ctor_get(v_preDef_4857_, 3);
lean_inc_n(v_declName_4868_, 2);
v_value_4869_ = lean_ctor_get(v_preDef_4857_, 7);
lean_inc_ref(v_value_4869_);
lean_dec_ref(v_preDef_4857_);
v___x_4870_ = l_Lean_Meta_unfoldThmSuffix;
v___x_4871_ = l_Lean_Meta_mkEqLikeNameFor(v_env_4866_, v_declName_4868_, v___x_4870_);
lean_inc(v___x_4871_);
v___f_4872_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4872_, 0, v_levelParams_4867_);
lean_closure_set(v___f_4872_, 1, v_declName_4868_);
lean_closure_set(v___f_4872_, 2, v_wfPreprocessProof_4859_);
lean_closure_set(v___f_4872_, 3, v___x_4871_);
lean_closure_set(v___f_4872_, 4, v_unaryPreDefName_4858_);
v___x_4873_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___closed__1, &l_Lean_Elab_WF_mkUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1);
v___x_4874_ = l_Lean_MessageData_ofName(v___x_4871_);
v___x_4875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4875_, 0, v___x_4873_);
lean_ctor_set(v___x_4875_, 1, v___x_4874_);
v___f_4876_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4876_, 0, v___x_4875_);
v___x_4877_ = 0;
v___x_4878_ = lean_box(v___x_4877_);
v___x_4879_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed), 9, 4);
lean_closure_set(v___x_4879_, 0, lean_box(0));
lean_closure_set(v___x_4879_, 1, v_value_4869_);
lean_closure_set(v___x_4879_, 2, v___f_4872_);
lean_closure_set(v___x_4879_, 3, v___x_4878_);
v___x_4880_ = 1;
v___x_4881_ = lean_box(v___x_4880_);
v___x_4882_ = lean_box(v___x_4877_);
v___f_4883_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_4883_, 0, v___x_4879_);
lean_closure_set(v___f_4883_, 1, v___x_4881_);
lean_closure_set(v___f_4883_, 2, v___x_4882_);
v___x_4884_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4883_, v___f_4876_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4884_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4884_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
v_a_4893_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4884_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4884_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___boxed(lean_object* v_preDef_4901_, lean_object* v_unaryPreDefName_4902_, lean_object* v_wfPreprocessProof_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v_res_4909_; 
v_res_4909_ = l_Lean_Elab_WF_mkUnfoldEq(v_preDef_4901_, v_unaryPreDefName_4902_, v_wfPreprocessProof_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_);
lean_dec(v_a_4907_);
lean_dec_ref(v_a_4906_);
lean_dec(v_a_4905_);
lean_dec_ref(v_a_4904_);
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object* v_00_u03b1_4910_, lean_object* v_x_4911_, uint8_t v_when_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
lean_object* v___x_4918_; 
v___x_4918_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(v_x_4911_, v_when_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object* v_00_u03b1_4919_, lean_object* v_x_4920_, lean_object* v_when_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
uint8_t v_when_boxed_4927_; lean_object* v_res_4928_; 
v_when_boxed_4927_ = lean_unbox(v_when_4921_);
v_res_4928_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v_00_u03b1_4919_, v_x_4920_, v_when_boxed_4927_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
lean_dec(v___y_4925_);
lean_dec_ref(v___y_4924_);
lean_dec(v___y_4923_);
lean_dec_ref(v___y_4922_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(lean_object* v_00_u03b1_4929_, lean_object* v_x_4930_, uint8_t v_isExporting_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
lean_object* v___x_4937_; 
v___x_4937_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(v_x_4930_, v_isExporting_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___boxed(lean_object* v_00_u03b1_4938_, lean_object* v_x_4939_, lean_object* v_isExporting_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_){
_start:
{
uint8_t v_isExporting_boxed_4946_; lean_object* v_res_4947_; 
v_isExporting_boxed_4946_ = lean_unbox(v_isExporting_4940_);
v_res_4947_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(v_00_u03b1_4938_, v_x_4939_, v_isExporting_boxed_4946_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_4948_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4___redArg(){
_start:
{
lean_object* v___x_4951_; 
v___x_4951_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2);
return v___x_4951_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v___dummy_4952_){
_start:
{
lean_object* v_res_4953_; 
v_res_4953_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4___redArg();
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_4954_){
_start:
{
lean_object* v___x_4955_; 
v___x_4955_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2);
return v___x_4955_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4957_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0));
v___x_4958_ = l_Lean_stringToMessageData(v___x_4957_);
return v___x_4958_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4964_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3));
v___x_4965_ = l_Lean_stringToMessageData(v___x_4964_);
return v___x_4965_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; 
v___x_4967_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5));
v___x_4968_ = l_Lean_stringToMessageData(v___x_4967_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object* v_levelParams_4969_, lean_object* v_declName_4970_, lean_object* v___x_4971_, lean_object* v___x_4972_, lean_object* v___x_4973_, lean_object* v_xs_4974_, lean_object* v_body_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_){
_start:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4984_ = lean_box(0);
lean_inc(v_levelParams_4969_);
v___x_4985_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4969_, v___x_4984_);
v___x_4986_ = l_Lean_mkConst(v_declName_4970_, v___x_4985_);
v___x_4987_ = l_Lean_mkAppN(v___x_4986_, v_xs_4974_);
v___x_4988_ = l_Lean_Meta_mkEq(v___x_4987_, v_body_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v_a_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
lean_inc_n(v_a_4989_, 2);
lean_dec_ref_known(v___x_4988_, 1);
v___x_4990_ = lean_box(0);
v___x_4991_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4989_, v___x_4990_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
if (lean_obj_tag(v___x_4991_) == 0)
{
lean_object* v_a_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v_a_4992_ = lean_ctor_get(v___x_4991_, 0);
lean_inc(v_a_4992_);
lean_dec_ref_known(v___x_4991_, 1);
v___x_4993_ = l_Lean_Expr_mvarId_x21(v_a_4992_);
v___x_4994_ = l_Lean_Elab_Eqns_deltaLHS(v___x_4993_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
if (lean_obj_tag(v___x_4994_) == 0)
{
lean_object* v_a_4995_; uint8_t v___x_4996_; uint8_t v___x_4997_; lean_object* v___y_4999_; lean_object* v___y_5000_; lean_object* v___y_5001_; lean_object* v___y_5002_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc_n(v_a_4995_, 2);
lean_dec_ref_known(v___x_4994_, 1);
v___x_4996_ = 1;
v___x_4997_ = 0;
v___x_5059_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2));
v___x_5060_ = l_Lean_MVarId_applyConst(v_a_4995_, v___x_4972_, v___x_5059_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; uint8_t v___x_5062_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
lean_dec_ref_known(v___x_5060_, 1);
v___x_5062_ = l_List_isEmpty___redArg(v_a_5061_);
lean_dec(v_a_5061_);
if (v___x_5062_ == 0)
{
lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
lean_dec(v_a_4992_);
lean_dec(v_a_4989_);
lean_dec(v___x_4971_);
lean_dec(v_levelParams_4969_);
v___x_5063_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4);
v___x_5064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5063_);
lean_ctor_set(v___x_5064_, 1, v___x_4973_);
v___x_5065_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6);
v___x_5066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5066_, 0, v___x_5064_);
lean_ctor_set(v___x_5066_, 1, v___x_5065_);
v___x_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5067_, 0, v_a_4995_);
v___x_5068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5066_);
lean_ctor_set(v___x_5068_, 1, v___x_5067_);
v___x_5069_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5068_);
lean_ctor_set(v___x_5070_, 1, v___x_5069_);
v___x_5071_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_5070_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
return v___x_5071_;
}
else
{
lean_dec(v_a_4995_);
lean_dec_ref(v___x_4973_);
v___y_4999_ = v___y_4976_;
v___y_5000_ = v___y_4977_;
v___y_5001_ = v___y_4978_;
v___y_5002_ = v___y_4979_;
goto v___jp_4998_;
}
}
else
{
lean_object* v_a_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5079_; 
lean_dec(v_a_4995_);
lean_dec(v_a_4992_);
lean_dec(v_a_4989_);
lean_dec_ref(v___x_4973_);
lean_dec(v___x_4971_);
lean_dec(v_levelParams_4969_);
v_a_5072_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5074_ = v___x_5060_;
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_5060_);
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
v___jp_4998_:
{
lean_object* v___x_5003_; lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5058_; 
v___x_5003_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4992_, v___y_5000_);
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5058_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5058_ == 0)
{
v___x_5006_ = v___x_5003_;
v_isShared_5007_ = v_isSharedCheck_5058_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_5003_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5058_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
uint8_t v___x_5008_; lean_object* v___x_5009_; 
v___x_5008_ = 1;
v___x_5009_ = l_Lean_Meta_mkForallFVars(v_xs_4974_, v_a_4989_, v___x_4997_, v___x_4996_, v___x_4996_, v___x_5008_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v_a_5010_; lean_object* v___x_5011_; 
v_a_5010_ = lean_ctor_get(v___x_5009_, 0);
lean_inc(v_a_5010_);
lean_dec_ref_known(v___x_5009_, 1);
v___x_5011_ = l_Lean_Meta_letToHave(v_a_5010_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5013_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_a_5012_);
lean_dec_ref_known(v___x_5011_, 1);
v___x_5013_ = l_Lean_Meta_mkLambdaFVars(v_xs_4974_, v_a_5004_, v___x_4997_, v___x_4996_, v___x_4997_, v___x_4996_, v___x_5008_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5013_) == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5019_; 
v_a_5014_ = lean_ctor_get(v___x_5013_, 0);
lean_inc(v_a_5014_);
lean_dec_ref_known(v___x_5013_, 1);
lean_inc_n(v___x_4971_, 2);
v___x_5015_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5015_, 0, v___x_4971_);
lean_ctor_set(v___x_5015_, 1, v_levelParams_4969_);
lean_ctor_set(v___x_5015_, 2, v_a_5012_);
v___x_5016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5016_, 0, v___x_4971_);
lean_ctor_set(v___x_5016_, 1, v___x_4984_);
v___x_5017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5015_);
lean_ctor_set(v___x_5017_, 1, v_a_5014_);
lean_ctor_set(v___x_5017_, 2, v___x_5016_);
if (v_isShared_5007_ == 0)
{
lean_ctor_set_tag(v___x_5006_, 2);
lean_ctor_set(v___x_5006_, 0, v___x_5017_);
v___x_5019_ = v___x_5006_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v___x_5017_);
v___x_5019_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
lean_object* v___x_5020_; 
v___x_5020_ = l_Lean_addDecl(v___x_5019_, v___x_4997_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v___x_5021_; 
lean_dec_ref_known(v___x_5020_, 1);
lean_inc(v___x_4971_);
v___x_5021_ = l_Lean_inferDefEqAttr(v___x_4971_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_toCold_5022_; lean_object* v_options_5023_; uint8_t v_hasTrace_5024_; 
lean_dec_ref_known(v___x_5021_, 1);
v_toCold_5022_ = lean_ctor_get(v___y_5001_, 0);
v_options_5023_ = lean_ctor_get(v_toCold_5022_, 2);
v_hasTrace_5024_ = lean_ctor_get_uint8(v_options_5023_, sizeof(void*)*1);
if (v_hasTrace_5024_ == 0)
{
lean_dec(v___x_4971_);
goto v___jp_4981_;
}
else
{
lean_object* v_inheritedTraceOptions_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; uint8_t v___x_5028_; 
v_inheritedTraceOptions_5025_ = lean_ctor_get(v_toCold_5022_, 11);
v___x_5026_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_5027_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_5028_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5025_, v_options_5023_, v___x_5027_);
if (v___x_5028_ == 0)
{
lean_dec(v___x_4971_);
goto v___jp_4981_;
}
else
{
lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5029_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1);
v___x_5030_ = l_Lean_MessageData_ofConstName(v___x_4971_, v___x_4997_);
v___x_5031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5029_);
lean_ctor_set(v___x_5031_, 1, v___x_5030_);
v___x_5032_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_5026_, v___x_5031_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
return v___x_5032_;
}
}
}
else
{
lean_dec(v___x_4971_);
return v___x_5021_;
}
}
else
{
lean_dec(v___x_4971_);
return v___x_5020_;
}
}
}
else
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5041_; 
lean_dec(v_a_5012_);
lean_del_object(v___x_5006_);
lean_dec(v___x_4971_);
lean_dec(v_levelParams_4969_);
v_a_5034_ = lean_ctor_get(v___x_5013_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5036_ = v___x_5013_;
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_a_5034_);
lean_dec(v___x_5013_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5039_; 
if (v_isShared_5037_ == 0)
{
v___x_5039_ = v___x_5036_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
}
else
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5049_; 
lean_del_object(v___x_5006_);
lean_dec(v_a_5004_);
lean_dec(v___x_4971_);
lean_dec(v_levelParams_4969_);
v_a_5042_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5044_ = v___x_5011_;
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_5011_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v___x_5047_; 
if (v_isShared_5045_ == 0)
{
v___x_5047_ = v___x_5044_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5042_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
}
}
else
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
lean_del_object(v___x_5006_);
lean_dec(v_a_5004_);
lean_dec(v___x_4971_);
lean_dec(v_levelParams_4969_);
v_a_5050_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5052_ = v___x_5009_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5009_);
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
}
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5087_; 
lean_dec(v_a_4992_);
lean_dec(v_a_4989_);
lean_dec_ref(v___x_4973_);
lean_dec(v___x_4972_);
lean_dec(v___x_4971_);
lean_dec(v_levelParams_4969_);
v_a_5080_ = lean_ctor_get(v___x_4994_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5082_ = v___x_4994_;
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_4994_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5085_; 
if (v_isShared_5083_ == 0)
{
v___x_5085_ = v___x_5082_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
v___x_5085_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
return v___x_5085_;
}
}
}
}
else
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
lean_dec(v_a_4989_);
lean_dec_ref(v___x_4973_);
lean_dec(v___x_4972_);
lean_dec(v___x_4971_);
lean_dec(v_levelParams_4969_);
v_a_5088_ = lean_ctor_get(v___x_4991_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_4991_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5090_ = v___x_4991_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_4991_);
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
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
lean_dec_ref(v___x_4973_);
lean_dec(v___x_4972_);
lean_dec(v___x_4971_);
lean_dec(v_levelParams_4969_);
v_a_5096_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_4988_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_4988_);
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
v___jp_4981_:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4982_ = lean_box(0);
v___x_4983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4982_);
return v___x_4983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed(lean_object* v_levelParams_5104_, lean_object* v_declName_5105_, lean_object* v___x_5106_, lean_object* v___x_5107_, lean_object* v___x_5108_, lean_object* v_xs_5109_, lean_object* v_body_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_){
_start:
{
lean_object* v_res_5116_; 
v_res_5116_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(v_levelParams_5104_, v_declName_5105_, v___x_5106_, v___x_5107_, v___x_5108_, v_xs_5109_, v_body_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
lean_dec(v___y_5114_);
lean_dec_ref(v___y_5113_);
lean_dec(v___y_5112_);
lean_dec_ref(v___y_5111_);
lean_dec_ref(v_xs_5109_);
return v_res_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(lean_object* v_value_5117_, lean_object* v___f_5118_, uint8_t v___x_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_){
_start:
{
uint16_t v___y_5126_; lean_object* v___y_5127_; lean_object* v_fileName_5128_; lean_object* v_fileMap_5129_; lean_object* v_currNamespace_5130_; lean_object* v_openDecls_5131_; lean_object* v_initHeartbeats_5132_; lean_object* v_maxHeartbeats_5133_; lean_object* v_quotContext_5134_; lean_object* v_currMacroScope_5135_; lean_object* v_cancelTk_x3f_5136_; lean_object* v_inheritedTraceOptions_5137_; lean_object* v_currRecDepth_5138_; lean_object* v_ref_5139_; uint8_t v_suppressElabErrors_5140_; uint8_t v_checkDeprecated_5141_; uint8_t v_isRecordingDeps_5142_; lean_object* v___y_5143_; lean_object* v_toCold_5149_; lean_object* v_currRecDepth_5150_; lean_object* v_ref_5151_; uint8_t v_suppressElabErrors_5152_; uint8_t v_checkDeprecated_5153_; uint8_t v_isRecordingDeps_5154_; lean_object* v_fileName_5155_; lean_object* v_fileMap_5156_; lean_object* v_options_5157_; lean_object* v_currNamespace_5158_; lean_object* v_openDecls_5159_; lean_object* v_initHeartbeats_5160_; lean_object* v_maxHeartbeats_5161_; lean_object* v_quotContext_5162_; lean_object* v_currMacroScope_5163_; lean_object* v_cancelTk_x3f_5164_; lean_object* v_inheritedTraceOptions_5165_; uint16_t v___y_5167_; uint8_t v___y_5168_; lean_object* v___y_5169_; lean_object* v___y_5192_; 
v_toCold_5149_ = lean_ctor_get(v___y_5122_, 0);
v_currRecDepth_5150_ = lean_ctor_get(v___y_5122_, 1);
v_ref_5151_ = lean_ctor_get(v___y_5122_, 2);
v_suppressElabErrors_5152_ = lean_ctor_get_uint8(v___y_5122_, sizeof(void*)*3 + 2);
v_checkDeprecated_5153_ = lean_ctor_get_uint8(v___y_5122_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5154_ = lean_ctor_get_uint8(v___y_5122_, sizeof(void*)*3 + 4);
v_fileName_5155_ = lean_ctor_get(v_toCold_5149_, 0);
v_fileMap_5156_ = lean_ctor_get(v_toCold_5149_, 1);
v_options_5157_ = lean_ctor_get(v_toCold_5149_, 2);
v_currNamespace_5158_ = lean_ctor_get(v_toCold_5149_, 4);
v_openDecls_5159_ = lean_ctor_get(v_toCold_5149_, 5);
v_initHeartbeats_5160_ = lean_ctor_get(v_toCold_5149_, 6);
v_maxHeartbeats_5161_ = lean_ctor_get(v_toCold_5149_, 7);
v_quotContext_5162_ = lean_ctor_get(v_toCold_5149_, 8);
v_currMacroScope_5163_ = lean_ctor_get(v_toCold_5149_, 9);
v_cancelTk_x3f_5164_ = lean_ctor_get(v_toCold_5149_, 10);
v_inheritedTraceOptions_5165_ = lean_ctor_get(v_toCold_5149_, 11);
if (v_isRecordingDeps_5154_ == 0)
{
lean_object* v___x_5202_; lean_object* v___x_5203_; 
v___x_5202_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_5157_);
v___x_5203_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_options_5157_, v___x_5202_, v_isRecordingDeps_5154_);
v___y_5192_ = v___x_5203_;
goto v___jp_5191_;
}
else
{
lean_object* v___x_5204_; 
lean_inc_ref(v_options_5157_);
v___x_5204_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_5157_);
v___y_5192_ = v___x_5204_;
goto v___jp_5191_;
}
v___jp_5125_:
{
lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
v___x_5144_ = l_Lean_maxRecDepth;
v___x_5145_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v___y_5127_, v___x_5144_);
v___x_5146_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_5146_, 0, v_fileName_5128_);
lean_ctor_set(v___x_5146_, 1, v_fileMap_5129_);
lean_ctor_set(v___x_5146_, 2, v___y_5127_);
lean_ctor_set(v___x_5146_, 3, v___x_5145_);
lean_ctor_set(v___x_5146_, 4, v_currNamespace_5130_);
lean_ctor_set(v___x_5146_, 5, v_openDecls_5131_);
lean_ctor_set(v___x_5146_, 6, v_initHeartbeats_5132_);
lean_ctor_set(v___x_5146_, 7, v_maxHeartbeats_5133_);
lean_ctor_set(v___x_5146_, 8, v_quotContext_5134_);
lean_ctor_set(v___x_5146_, 9, v_currMacroScope_5135_);
lean_ctor_set(v___x_5146_, 10, v_cancelTk_x3f_5136_);
lean_ctor_set(v___x_5146_, 11, v_inheritedTraceOptions_5137_);
lean_inc(v_ref_5139_);
lean_inc(v_currRecDepth_5138_);
v___x_5147_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5147_, 0, v___x_5146_);
lean_ctor_set(v___x_5147_, 1, v_currRecDepth_5138_);
lean_ctor_set(v___x_5147_, 2, v_ref_5139_);
lean_ctor_set_uint16(v___x_5147_, sizeof(void*)*3, v___y_5126_);
lean_ctor_set_uint8(v___x_5147_, sizeof(void*)*3 + 2, v_suppressElabErrors_5140_);
lean_ctor_set_uint8(v___x_5147_, sizeof(void*)*3 + 3, v_checkDeprecated_5141_);
lean_ctor_set_uint8(v___x_5147_, sizeof(void*)*3 + 4, v_isRecordingDeps_5142_);
v___x_5148_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_value_5117_, v___f_5118_, v___x_5119_, v___y_5120_, v___y_5121_, v___x_5147_, v___y_5143_);
lean_dec_ref_known(v___x_5147_, 3);
return v___x_5148_;
}
v___jp_5166_:
{
lean_object* v___x_5170_; lean_object* v_env_5171_; lean_object* v_nextMacroScope_5172_; lean_object* v_ngen_5173_; lean_object* v_auxDeclNGen_5174_; lean_object* v_traceState_5175_; lean_object* v_recordedDeps_5176_; lean_object* v_messages_5177_; lean_object* v_infoState_5178_; lean_object* v_snapshotTasks_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5189_; 
v___x_5170_ = lean_st_ref_take(v___y_5123_);
v_env_5171_ = lean_ctor_get(v___x_5170_, 0);
v_nextMacroScope_5172_ = lean_ctor_get(v___x_5170_, 1);
v_ngen_5173_ = lean_ctor_get(v___x_5170_, 2);
v_auxDeclNGen_5174_ = lean_ctor_get(v___x_5170_, 3);
v_traceState_5175_ = lean_ctor_get(v___x_5170_, 4);
v_recordedDeps_5176_ = lean_ctor_get(v___x_5170_, 6);
v_messages_5177_ = lean_ctor_get(v___x_5170_, 7);
v_infoState_5178_ = lean_ctor_get(v___x_5170_, 8);
v_snapshotTasks_5179_ = lean_ctor_get(v___x_5170_, 9);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5170_);
if (v_isSharedCheck_5189_ == 0)
{
lean_object* v_unused_5190_; 
v_unused_5190_ = lean_ctor_get(v___x_5170_, 5);
lean_dec(v_unused_5190_);
v___x_5181_ = v___x_5170_;
v_isShared_5182_ = v_isSharedCheck_5189_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_snapshotTasks_5179_);
lean_inc(v_infoState_5178_);
lean_inc(v_messages_5177_);
lean_inc(v_recordedDeps_5176_);
lean_inc(v_traceState_5175_);
lean_inc(v_auxDeclNGen_5174_);
lean_inc(v_ngen_5173_);
lean_inc(v_nextMacroScope_5172_);
lean_inc(v_env_5171_);
lean_dec(v___x_5170_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5189_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5186_; 
v___x_5183_ = l_Lean_Kernel_enableDiag(v_env_5171_, v___y_5168_);
v___x_5184_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1);
if (v_isShared_5182_ == 0)
{
lean_ctor_set(v___x_5181_, 5, v___x_5184_);
lean_ctor_set(v___x_5181_, 0, v___x_5183_);
v___x_5186_ = v___x_5181_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5183_);
lean_ctor_set(v_reuseFailAlloc_5188_, 1, v_nextMacroScope_5172_);
lean_ctor_set(v_reuseFailAlloc_5188_, 2, v_ngen_5173_);
lean_ctor_set(v_reuseFailAlloc_5188_, 3, v_auxDeclNGen_5174_);
lean_ctor_set(v_reuseFailAlloc_5188_, 4, v_traceState_5175_);
lean_ctor_set(v_reuseFailAlloc_5188_, 5, v___x_5184_);
lean_ctor_set(v_reuseFailAlloc_5188_, 6, v_recordedDeps_5176_);
lean_ctor_set(v_reuseFailAlloc_5188_, 7, v_messages_5177_);
lean_ctor_set(v_reuseFailAlloc_5188_, 8, v_infoState_5178_);
lean_ctor_set(v_reuseFailAlloc_5188_, 9, v_snapshotTasks_5179_);
v___x_5186_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
lean_object* v___x_5187_; 
v___x_5187_ = lean_st_ref_put(v___y_5123_, v___x_5186_);
lean_inc_ref(v_inheritedTraceOptions_5165_);
lean_inc(v_cancelTk_x3f_5164_);
lean_inc(v_currMacroScope_5163_);
lean_inc(v_quotContext_5162_);
lean_inc(v_maxHeartbeats_5161_);
lean_inc(v_initHeartbeats_5160_);
lean_inc(v_openDecls_5159_);
lean_inc(v_currNamespace_5158_);
lean_inc_ref(v_fileMap_5156_);
lean_inc_ref(v_fileName_5155_);
v___y_5126_ = v___y_5167_;
v___y_5127_ = v___y_5169_;
v_fileName_5128_ = v_fileName_5155_;
v_fileMap_5129_ = v_fileMap_5156_;
v_currNamespace_5130_ = v_currNamespace_5158_;
v_openDecls_5131_ = v_openDecls_5159_;
v_initHeartbeats_5132_ = v_initHeartbeats_5160_;
v_maxHeartbeats_5133_ = v_maxHeartbeats_5161_;
v_quotContext_5134_ = v_quotContext_5162_;
v_currMacroScope_5135_ = v_currMacroScope_5163_;
v_cancelTk_x3f_5136_ = v_cancelTk_x3f_5164_;
v_inheritedTraceOptions_5137_ = v_inheritedTraceOptions_5165_;
v_currRecDepth_5138_ = v_currRecDepth_5150_;
v_ref_5139_ = v_ref_5151_;
v_suppressElabErrors_5140_ = v_suppressElabErrors_5152_;
v_checkDeprecated_5141_ = v_checkDeprecated_5153_;
v_isRecordingDeps_5142_ = v_isRecordingDeps_5154_;
v___y_5143_ = v___y_5123_;
goto v___jp_5125_;
}
}
}
v___jp_5191_:
{
uint16_t v___x_5193_; lean_object* v___x_5194_; lean_object* v_env_5195_; uint8_t v___x_5196_; uint16_t v___x_5197_; uint16_t v___x_5198_; uint16_t v___x_5199_; uint8_t v___x_5200_; 
v___x_5193_ = l_Lean_OptionFlags_ofOptions(v___y_5192_);
v___x_5194_ = lean_st_ref_get(v___y_5123_);
v_env_5195_ = lean_ctor_get(v___x_5194_, 0);
lean_inc_ref(v_env_5195_);
lean_dec(v___x_5194_);
v___x_5196_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5195_);
lean_dec_ref(v_env_5195_);
v___x_5197_ = 512;
v___x_5198_ = lean_uint16_land(v___x_5193_, v___x_5197_);
v___x_5199_ = 0;
v___x_5200_ = lean_uint16_dec_eq(v___x_5198_, v___x_5199_);
if (v___x_5200_ == 0)
{
if (v___x_5196_ == 0)
{
uint8_t v___x_5201_; 
v___x_5201_ = 1;
v___y_5167_ = v___x_5193_;
v___y_5168_ = v___x_5201_;
v___y_5169_ = v___y_5192_;
goto v___jp_5166_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_5165_);
lean_inc(v_cancelTk_x3f_5164_);
lean_inc(v_currMacroScope_5163_);
lean_inc(v_quotContext_5162_);
lean_inc(v_maxHeartbeats_5161_);
lean_inc(v_initHeartbeats_5160_);
lean_inc(v_openDecls_5159_);
lean_inc(v_currNamespace_5158_);
lean_inc_ref(v_fileMap_5156_);
lean_inc_ref(v_fileName_5155_);
v___y_5126_ = v___x_5193_;
v___y_5127_ = v___y_5192_;
v_fileName_5128_ = v_fileName_5155_;
v_fileMap_5129_ = v_fileMap_5156_;
v_currNamespace_5130_ = v_currNamespace_5158_;
v_openDecls_5131_ = v_openDecls_5159_;
v_initHeartbeats_5132_ = v_initHeartbeats_5160_;
v_maxHeartbeats_5133_ = v_maxHeartbeats_5161_;
v_quotContext_5134_ = v_quotContext_5162_;
v_currMacroScope_5135_ = v_currMacroScope_5163_;
v_cancelTk_x3f_5136_ = v_cancelTk_x3f_5164_;
v_inheritedTraceOptions_5137_ = v_inheritedTraceOptions_5165_;
v_currRecDepth_5138_ = v_currRecDepth_5150_;
v_ref_5139_ = v_ref_5151_;
v_suppressElabErrors_5140_ = v_suppressElabErrors_5152_;
v_checkDeprecated_5141_ = v_checkDeprecated_5153_;
v_isRecordingDeps_5142_ = v_isRecordingDeps_5154_;
v___y_5143_ = v___y_5123_;
goto v___jp_5125_;
}
}
else
{
if (v___x_5196_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_5165_);
lean_inc(v_cancelTk_x3f_5164_);
lean_inc(v_currMacroScope_5163_);
lean_inc(v_quotContext_5162_);
lean_inc(v_maxHeartbeats_5161_);
lean_inc(v_initHeartbeats_5160_);
lean_inc(v_openDecls_5159_);
lean_inc(v_currNamespace_5158_);
lean_inc_ref(v_fileMap_5156_);
lean_inc_ref(v_fileName_5155_);
v___y_5126_ = v___x_5193_;
v___y_5127_ = v___y_5192_;
v_fileName_5128_ = v_fileName_5155_;
v_fileMap_5129_ = v_fileMap_5156_;
v_currNamespace_5130_ = v_currNamespace_5158_;
v_openDecls_5131_ = v_openDecls_5159_;
v_initHeartbeats_5132_ = v_initHeartbeats_5160_;
v_maxHeartbeats_5133_ = v_maxHeartbeats_5161_;
v_quotContext_5134_ = v_quotContext_5162_;
v_currMacroScope_5135_ = v_currMacroScope_5163_;
v_cancelTk_x3f_5136_ = v_cancelTk_x3f_5164_;
v_inheritedTraceOptions_5137_ = v_inheritedTraceOptions_5165_;
v_currRecDepth_5138_ = v_currRecDepth_5150_;
v_ref_5139_ = v_ref_5151_;
v_suppressElabErrors_5140_ = v_suppressElabErrors_5152_;
v_checkDeprecated_5141_ = v_checkDeprecated_5153_;
v_isRecordingDeps_5142_ = v_isRecordingDeps_5154_;
v___y_5143_ = v___y_5123_;
goto v___jp_5125_;
}
else
{
v___y_5167_ = v___x_5193_;
v___y_5168_ = v___x_5119_;
v___y_5169_ = v___y_5192_;
goto v___jp_5166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed(lean_object* v_value_5205_, lean_object* v___f_5206_, lean_object* v___x_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_){
_start:
{
uint8_t v___x_5319__boxed_5213_; lean_object* v_res_5214_; 
v___x_5319__boxed_5213_ = lean_unbox(v___x_5207_);
v_res_5214_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(v_value_5205_, v___f_5206_, v___x_5319__boxed_5213_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_);
lean_dec(v___y_5211_);
lean_dec_ref(v___y_5210_);
lean_dec(v___y_5209_);
lean_dec_ref(v___y_5208_);
return v_res_5214_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_5216_; lean_object* v___x_5217_; 
v___x_5216_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0));
v___x_5217_ = l_Lean_stringToMessageData(v___x_5216_);
return v___x_5217_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3(void){
_start:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; 
v___x_5219_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__2));
v___x_5220_ = l_Lean_stringToMessageData(v___x_5219_);
return v___x_5220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object* v_preDef_5221_, lean_object* v_unaryPreDefName_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_){
_start:
{
lean_object* v___x_5228_; lean_object* v_env_5229_; lean_object* v_levelParams_5230_; lean_object* v_declName_5231_; lean_object* v_value_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v_env_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___f_5244_; lean_object* v___x_5245_; lean_object* v___f_5246_; uint8_t v___x_5247_; lean_object* v___x_5248_; lean_object* v___f_5249_; lean_object* v___x_5250_; 
v___x_5228_ = lean_st_ref_get(v_a_5226_);
v_env_5229_ = lean_ctor_get(v___x_5228_, 0);
lean_inc_ref(v_env_5229_);
lean_dec(v___x_5228_);
v_levelParams_5230_ = lean_ctor_get(v_preDef_5221_, 1);
lean_inc(v_levelParams_5230_);
v_declName_5231_ = lean_ctor_get(v_preDef_5221_, 3);
lean_inc_n(v_declName_5231_, 2);
v_value_5232_ = lean_ctor_get(v_preDef_5221_, 7);
lean_inc_ref(v_value_5232_);
lean_dec_ref(v_preDef_5221_);
v___x_5233_ = l_Lean_Meta_unfoldThmSuffix;
v___x_5234_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5229_, v_declName_5231_, v___x_5233_);
v___x_5235_ = lean_st_ref_get(v_a_5226_);
v_env_5236_ = lean_ctor_get(v___x_5235_, 0);
lean_inc_ref(v_env_5236_);
lean_dec(v___x_5235_);
v___x_5237_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5236_, v_unaryPreDefName_5222_, v___x_5233_);
v___x_5238_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1);
lean_inc(v___x_5234_);
v___x_5239_ = l_Lean_MessageData_ofName(v___x_5234_);
v___x_5240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5240_, 0, v___x_5238_);
lean_ctor_set(v___x_5240_, 1, v___x_5239_);
v___x_5241_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3);
v___x_5242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5242_, 0, v___x_5240_);
lean_ctor_set(v___x_5242_, 1, v___x_5241_);
lean_inc(v___x_5237_);
v___x_5243_ = l_Lean_MessageData_ofName(v___x_5237_);
lean_inc_ref(v___x_5243_);
v___f_5244_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5244_, 0, v_levelParams_5230_);
lean_closure_set(v___f_5244_, 1, v_declName_5231_);
lean_closure_set(v___f_5244_, 2, v___x_5234_);
lean_closure_set(v___f_5244_, 3, v___x_5237_);
lean_closure_set(v___f_5244_, 4, v___x_5243_);
v___x_5245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5245_, 0, v___x_5242_);
lean_ctor_set(v___x_5245_, 1, v___x_5243_);
v___f_5246_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_5246_, 0, v___x_5245_);
v___x_5247_ = 0;
v___x_5248_ = lean_box(v___x_5247_);
v___f_5249_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_5249_, 0, v_value_5232_);
lean_closure_set(v___f_5249_, 1, v___f_5244_);
lean_closure_set(v___f_5249_, 2, v___x_5248_);
v___x_5250_ = l_Lean_Meta_mapErrorImp___redArg(v___f_5249_, v___f_5246_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
if (lean_obj_tag(v___x_5250_) == 0)
{
lean_object* v_a_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5258_; 
v_a_5251_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5253_ = v___x_5250_;
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_a_5251_);
lean_dec(v___x_5250_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v___x_5256_; 
if (v_isShared_5254_ == 0)
{
v___x_5256_ = v___x_5253_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_a_5251_);
v___x_5256_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
return v___x_5256_;
}
}
}
else
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
v_a_5259_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___x_5250_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_5250_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___boxed(lean_object* v_preDef_5267_, lean_object* v_unaryPreDefName_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_){
_start:
{
lean_object* v_res_5274_; 
v_res_5274_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_preDef_5267_, v_unaryPreDefName_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
lean_dec(v_a_5272_);
lean_dec_ref(v_a_5271_);
lean_dec(v_a_5270_);
lean_dec_ref(v_a_5269_);
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5319_; uint8_t v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; 
v___x_5319_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5320_ = 0;
v___x_5321_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5322_ = l_Lean_registerTraceClass(v___x_5319_, v___x_5320_, v___x_5321_);
return v___x_5322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2____boxed(lean_object* v_a_5323_){
_start:
{
lean_object* v_res_5324_; 
v_res_5324_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_();
return v_res_5324_;
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
