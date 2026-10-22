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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_5970__boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v___x_5970__boxed_157_ = lean_unbox(v___x_155_);
v_res_158_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(v___x_5970__boxed_157_, v_x_156_);
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
uint8_t v___x_5978__boxed_188_; uint8_t v___x_5979__boxed_189_; lean_object* v_res_190_; 
v___x_5978__boxed_188_ = lean_unbox(v___x_179_);
v___x_5979__boxed_189_ = lean_unbox(v___x_180_);
v_res_190_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(v___x_177_, v___x_178_, v___x_5978__boxed_188_, v___x_5979__boxed_189_, v_ys_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
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
size_t v_x_6158__boxed_379_; size_t v_x_6159__boxed_380_; lean_object* v_res_381_; 
v_x_6158__boxed_379_ = lean_unbox_usize(v_x_375_);
lean_dec(v_x_375_);
v_x_6159__boxed_380_ = lean_unbox_usize(v_x_376_);
lean_dec(v_x_376_);
v_res_381_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_374_, v_x_6158__boxed_379_, v_x_6159__boxed_380_, v_x_377_, v_x_378_);
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
lean_object* v___x_393_; lean_object* v_mctx_394_; lean_object* v_cache_395_; lean_object* v_zetaDeltaFVarIds_396_; lean_object* v_postponed_397_; lean_object* v_diag_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_427_; 
v___x_393_ = lean_st_ref_take(v___y_391_);
v_mctx_394_ = lean_ctor_get(v___x_393_, 0);
v_cache_395_ = lean_ctor_get(v___x_393_, 1);
v_zetaDeltaFVarIds_396_ = lean_ctor_get(v___x_393_, 2);
v_postponed_397_ = lean_ctor_get(v___x_393_, 3);
v_diag_398_ = lean_ctor_get(v___x_393_, 4);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_427_ == 0)
{
v___x_400_ = v___x_393_;
v_isShared_401_ = v_isSharedCheck_427_;
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
v_isShared_401_ = v_isSharedCheck_427_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_depth_402_; lean_object* v_levelAssignDepth_403_; lean_object* v_lmvarCounter_404_; lean_object* v_mvarCounter_405_; lean_object* v_lDecls_406_; lean_object* v_decls_407_; lean_object* v_userNames_408_; lean_object* v_lAssignment_409_; lean_object* v_eAssignment_410_; lean_object* v_dAssignment_411_; lean_object* v_synthNormMemo_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_426_; 
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
v_synthNormMemo_412_ = lean_ctor_get(v_mctx_394_, 10);
v_isSharedCheck_426_ = !lean_is_exclusive(v_mctx_394_);
if (v_isSharedCheck_426_ == 0)
{
v___x_414_ = v_mctx_394_;
v_isShared_415_ = v_isSharedCheck_426_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_synthNormMemo_412_);
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
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_426_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_416_ = lean_box(0);
v___x_417_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_eAssignment_410_, v_mvarId_389_, v_val_390_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 8, v___x_417_);
v___x_419_ = v___x_414_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_depth_402_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_levelAssignDepth_403_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_lmvarCounter_404_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v_mvarCounter_405_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v_lDecls_406_);
lean_ctor_set(v_reuseFailAlloc_425_, 5, v_decls_407_);
lean_ctor_set(v_reuseFailAlloc_425_, 6, v_userNames_408_);
lean_ctor_set(v_reuseFailAlloc_425_, 7, v_lAssignment_409_);
lean_ctor_set(v_reuseFailAlloc_425_, 8, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_425_, 9, v_dAssignment_411_);
lean_ctor_set(v_reuseFailAlloc_425_, 10, v_synthNormMemo_412_);
v___x_419_ = v_reuseFailAlloc_425_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_421_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_419_);
v___x_421_ = v___x_400_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_cache_395_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_zetaDeltaFVarIds_396_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_postponed_397_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_diag_398_);
v___x_421_ = v_reuseFailAlloc_424_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_st_ref_put(v___y_391_, v___x_421_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_416_);
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg___boxed(lean_object* v_mvarId_428_, lean_object* v_val_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_428_, v_val_429_, v___y_430_);
lean_dec(v___y_430_);
return v_res_432_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_439_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4));
v___x_440_ = lean_unsigned_to_nat(41u);
v___x_441_ = lean_unsigned_to_nat(34u);
v___x_442_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3));
v___x_443_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_444_ = l_mkPanicMessageWithDecl(v___x_443_, v___x_442_, v___x_441_, v___x_440_, v___x_439_);
return v___x_444_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9));
v___x_452_ = l_Lean_stringToMessageData(v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18(void){
_start:
{
lean_object* v___x_467_; lean_object* v_dummy_468_; 
v___x_467_ = lean_box(0);
v_dummy_468_ = l_Lean_Expr_sort___override(v___x_467_);
return v_dummy_468_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20));
v___x_475_ = l_Lean_stringToMessageData(v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object* v_mvarId_476_, lean_object* v___x_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
lean_inc(v_mvarId_476_);
v___x_483_ = l_Lean_MVarId_getType_x27(v_mvarId_476_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
v___x_485_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_486_ = lean_unsigned_to_nat(3u);
v___x_487_ = l_Lean_Expr_isAppOfArity(v_a_484_, v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v_a_484_);
lean_dec_ref(v___x_477_);
lean_dec(v_mvarId_476_);
v___x_488_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5);
v___x_489_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(v___x_488_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; lean_object* v___f_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___f_498_; lean_object* v___x_499_; 
v___x_490_ = lean_box(v___x_487_);
v___f_491_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_491_, 0, v___x_490_);
v___x_492_ = l_Lean_Expr_appFn_x21(v_a_484_);
v___x_493_ = l_Lean_Expr_appArg_x21(v___x_492_);
lean_dec_ref(v___x_492_);
v___x_494_ = l_Lean_Expr_appArg_x21(v_a_484_);
lean_dec(v_a_484_);
v___x_495_ = 0;
v___x_496_ = lean_box(v___x_495_);
v___x_497_ = lean_box(v___x_487_);
lean_inc_ref_n(v___x_493_, 2);
v___f_498_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed), 11, 4);
lean_closure_set(v___f_498_, 0, v___x_493_);
lean_closure_set(v___f_498_, 1, v___x_477_);
lean_closure_set(v___f_498_, 2, v___x_496_);
lean_closure_set(v___f_498_, 3, v___x_497_);
v___x_499_ = l_Lean_Meta_delta_x3f(v___x_493_, v___f_491_, v___x_495_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
if (lean_obj_tag(v_a_500_) == 1)
{
lean_object* v_val_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref(v___x_493_);
v_val_501_ = lean_ctor_get(v_a_500_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_a_500_);
if (v_isSharedCheck_650_ == 0)
{
v___x_503_ = v_a_500_;
v_isShared_504_ = v_isSharedCheck_650_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_val_501_);
lean_dec(v_a_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_650_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_h_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___x_601_; 
lean_inc(v_val_501_);
v___x_601_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_val_501_, v___y_479_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v___x_603_ = l_Lean_Expr_cleanupAnnotations(v_a_602_);
v___x_604_ = l_Lean_Expr_isApp(v___x_603_);
if (v___x_604_ == 0)
{
lean_dec_ref(v___x_603_);
v___y_580_ = v___y_478_;
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
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
v___y_580_ = v___y_478_;
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
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
v___y_580_ = v___y_478_;
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
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
v___y_580_ = v___y_478_;
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
goto v___jp_579_;
}
else
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = l_Lean_Expr_appFnCleanup___redArg(v___x_609_);
v___x_612_ = l_Lean_Expr_isApp(v___x_611_);
if (v___x_612_ == 0)
{
lean_dec_ref(v___x_611_);
v___y_580_ = v___y_478_;
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
goto v___jp_579_;
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
v___y_580_ = v___y_478_;
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
goto v___jp_579_;
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
v___y_580_ = v___y_478_;
v___y_581_ = v___y_479_;
v___y_582_ = v___y_480_;
v___y_583_ = v___y_481_;
goto v___jp_579_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_dummy_624_; lean_object* v_nargs_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_del_object(v___x_503_);
v___x_620_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17));
v___x_621_ = l_Lean_Expr_getAppFn(v_val_501_);
v___x_622_ = l_Lean_Expr_constLevels_x21(v___x_621_);
lean_dec_ref(v___x_621_);
v___x_623_ = l_Lean_mkConst(v___x_620_, v___x_622_);
v_dummy_624_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_625_ = l_Lean_Expr_getAppNumArgs(v_val_501_);
lean_inc(v_nargs_625_);
v___x_626_ = lean_mk_array(v_nargs_625_, v_dummy_624_);
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_sub(v_nargs_625_, v___x_627_);
lean_dec(v_nargs_625_);
lean_inc(v_val_501_);
v___x_629_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_501_, v___x_626_, v___x_628_);
v___x_630_ = l_Lean_mkAppN(v___x_623_, v___x_629_);
lean_dec_ref(v___x_629_);
v_h_506_ = v___x_630_;
v___y_507_ = v___y_478_;
v___y_508_ = v___y_479_;
v___y_509_ = v___y_480_;
v___y_510_ = v___y_481_;
goto v___jp_505_;
}
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_dummy_635_; lean_object* v_nargs_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec_ref(v___x_613_);
lean_del_object(v___x_503_);
v___x_631_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19));
v___x_632_ = l_Lean_Expr_getAppFn(v_val_501_);
v___x_633_ = l_Lean_Expr_constLevels_x21(v___x_632_);
lean_dec_ref(v___x_632_);
v___x_634_ = l_Lean_mkConst(v___x_631_, v___x_633_);
v_dummy_635_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_636_ = l_Lean_Expr_getAppNumArgs(v_val_501_);
lean_inc(v_nargs_636_);
v___x_637_ = lean_mk_array(v_nargs_636_, v_dummy_635_);
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_sub(v_nargs_636_, v___x_638_);
lean_dec(v_nargs_636_);
lean_inc(v_val_501_);
v___x_640_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_501_, v___x_637_, v___x_639_);
v___x_641_ = l_Lean_mkAppN(v___x_634_, v___x_640_);
lean_dec_ref(v___x_640_);
v_h_506_ = v___x_641_;
v___y_507_ = v___y_478_;
v___y_508_ = v___y_479_;
v___y_509_ = v___y_480_;
v___y_510_ = v___y_481_;
goto v___jp_505_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_del_object(v___x_503_);
lean_dec(v_val_501_);
lean_dec_ref(v___f_498_);
lean_dec_ref(v___x_494_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v_mvarId_476_);
v_a_642_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_601_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_601_);
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
v___jp_505_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_511_ = l_Lean_Expr_appFn_x21(v_val_501_);
v___x_512_ = l_Lean_Expr_appArg_x21(v___x_511_);
lean_dec_ref(v___x_511_);
v___x_513_ = l_Lean_Expr_appArg_x21(v_val_501_);
lean_dec(v_val_501_);
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
v___x_519_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_517_, v___x_518_, v___f_498_, v___x_495_, v___x_495_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = l_Lean_mkAppB(v___x_512_, v___x_513_, v_a_520_);
v___x_522_ = l_Lean_Meta_mkEq(v___x_521_, v___x_494_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
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
v___x_529_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_476_, v_a_528_, v___y_508_);
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
lean_dec(v_mvarId_476_);
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
lean_dec(v_mvarId_476_);
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
lean_dec(v_mvarId_476_);
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
lean_dec_ref(v___x_494_);
lean_dec(v_mvarId_476_);
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
lean_dec_ref(v___f_498_);
lean_dec_ref(v___x_494_);
lean_dec(v_mvarId_476_);
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
lean_inc(v_val_501_);
v___x_586_ = l_Lean_MessageData_ofExpr(v_val_501_);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_587_);
v___x_589_ = v___x_503_;
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
lean_inc(v_mvarId_476_);
v___x_590_ = l_Lean_Meta_throwTacticEx___redArg(v___x_584_, v_mvarId_476_, v___x_589_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
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
lean_dec(v_val_501_);
lean_dec_ref(v___f_498_);
lean_dec_ref(v___x_494_);
lean_dec(v_mvarId_476_);
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
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec(v_a_500_);
lean_dec_ref(v___f_498_);
lean_dec_ref(v___x_494_);
lean_dec(v_mvarId_476_);
v___x_651_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21);
v___x_652_ = l_Lean_MessageData_ofExpr(v___x_493_);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_653_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v___x_654_;
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v___f_498_);
lean_dec_ref(v___x_494_);
lean_dec_ref(v___x_493_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v_mvarId_476_);
v_a_655_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_499_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_499_);
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
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec_ref(v___x_477_);
lean_dec(v_mvarId_476_);
v_a_663_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_483_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_483_);
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
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
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
size_t v_x_6933__boxed_745_; size_t v_x_6934__boxed_746_; lean_object* v_res_747_; 
v_x_6933__boxed_745_ = lean_unbox_usize(v_x_741_);
lean_dec(v_x_741_);
v_x_6934__boxed_746_ = lean_unbox_usize(v_x_742_);
lean_dec(v_x_742_);
v_res_747_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(v_00_u03b2_739_, v_x_740_, v_x_6933__boxed_745_, v_x_6934__boxed_746_, v_x_743_, v_x_744_);
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
lean_dec_ref_known(v___x_788_, 1);
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
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
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
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(lean_object* v___x_840_, lean_object* v_xs_841_, lean_object* v_t_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = lean_array_get_size(v_xs_841_);
v___x_852_ = lean_nat_dec_eq(v___x_851_, v___x_840_);
if (v___x_852_ == 0)
{
goto v___jp_848_;
}
else
{
uint8_t v___x_853_; 
v___x_853_ = l_Lean_Expr_isForall(v_t_842_);
if (v___x_853_ == 0)
{
goto v___jp_848_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_854_ = l_Lean_Expr_bindingBody_x21(v_t_842_);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_expr_has_loose_bvar(v___x_854_, v___x_855_);
if (v___x_856_ == 0)
{
uint8_t v___x_857_; lean_object* v___x_858_; 
v___x_857_ = 1;
v___x_858_ = l_Lean_Meta_mkLambdaFVars(v_xs_841_, v___x_854_, v___x_856_, v___x_853_, v___x_856_, v___x_853_, v___x_857_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_867_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_867_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v_a_859_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_863_);
v___x_865_ = v___x_861_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_858_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_858_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_dec_ref(v___x_854_);
goto v___jp_848_;
}
}
}
v___jp_848_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_box(0);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed(lean_object* v___x_876_, lean_object* v_xs_877_, lean_object* v_t_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(v___x_876_, v_xs_877_, v_t_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec_ref(v_t_878_);
lean_dec_ref(v_xs_877_);
lean_dec(v___x_876_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(lean_object* v_matcherApp_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_motive_891_; lean_object* v_discrs_892_; lean_object* v___x_893_; lean_object* v___f_894_; uint8_t v___x_895_; lean_object* v___x_896_; 
v_motive_891_ = lean_ctor_get(v_matcherApp_885_, 4);
lean_inc_ref(v_motive_891_);
v_discrs_892_ = lean_ctor_get(v_matcherApp_885_, 5);
lean_inc_ref(v_discrs_892_);
lean_dec_ref(v_matcherApp_885_);
v___x_893_ = lean_array_get_size(v_discrs_892_);
lean_dec_ref(v_discrs_892_);
v___f_894_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed), 8, 1);
lean_closure_set(v___f_894_, 0, v___x_893_);
v___x_895_ = 0;
v___x_896_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_motive_891_, v___x_893_, v___f_894_, v___x_895_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___boxed(lean_object* v_matcherApp_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_matcherApp_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(lean_object* v_e_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; lean_object* v_env_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_907_ = lean_st_ref_get(v___y_905_);
v_env_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc_ref(v_env_908_);
lean_dec(v___x_907_);
v___x_909_ = l_Lean_Meta_isMatcherAppCore(v_env_908_, v_e_904_);
v___x_910_ = lean_box(v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg___boxed(lean_object* v_e_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v_e_912_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(lean_object* v_e_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_916_, v___y_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___boxed(lean_object* v_e_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(v_e_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec_ref(v_e_923_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(lean_object* v_msg_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___f_936_; lean_object* v___x_613__overap_937_; lean_object* v___x_938_; 
v___f_936_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_613__overap_937_ = lean_panic_fn_borrowed(v___f_936_, v_msg_930_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
lean_inc(v___y_932_);
lean_inc_ref(v___y_931_);
v___x_938_ = lean_apply_5(v___x_613__overap_937_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, lean_box(0));
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1___boxed(lean_object* v_msg_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v_msg_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(size_t v_sz_946_, size_t v_i_947_, lean_object* v_bs_948_){
_start:
{
uint8_t v___x_949_; 
v___x_949_ = lean_usize_dec_lt(v_i_947_, v_sz_946_);
if (v___x_949_ == 0)
{
return v_bs_948_;
}
else
{
lean_object* v_v_950_; lean_object* v_toInductionSubgoal_951_; lean_object* v_mvarId_952_; lean_object* v___x_953_; lean_object* v_bs_x27_954_; size_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; 
v_v_950_ = lean_array_uget_borrowed(v_bs_948_, v_i_947_);
v_toInductionSubgoal_951_ = lean_ctor_get(v_v_950_, 0);
v_mvarId_952_ = lean_ctor_get(v_toInductionSubgoal_951_, 0);
lean_inc(v_mvarId_952_);
v___x_953_ = lean_unsigned_to_nat(0u);
v_bs_x27_954_ = lean_array_uset(v_bs_948_, v_i_947_, v___x_953_);
v___x_955_ = ((size_t)1ULL);
v___x_956_ = lean_usize_add(v_i_947_, v___x_955_);
v___x_957_ = lean_array_uset(v_bs_x27_954_, v_i_947_, v_mvarId_952_);
v_i_947_ = v___x_956_;
v_bs_948_ = v___x_957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2___boxed(lean_object* v_sz_959_, lean_object* v_i_960_, lean_object* v_bs_961_){
_start:
{
size_t v_sz_boxed_962_; size_t v_i_boxed_963_; lean_object* v_res_964_; 
v_sz_boxed_962_ = lean_unbox_usize(v_sz_959_);
lean_dec(v_sz_959_);
v_i_boxed_963_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_boxed_962_, v_i_boxed_963_, v_bs_961_);
return v_res_964_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_967_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1));
v___x_968_ = lean_unsigned_to_nat(4u);
v___x_969_ = lean_unsigned_to_nat(79u);
v___x_970_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0));
v___x_971_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_972_ = l_mkPanicMessageWithDecl(v___x_971_, v___x_970_, v___x_969_, v___x_968_, v___x_967_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(lean_object* v_mvarId_975_, lean_object* v_e_976_, lean_object* v_matcherInfo_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v_a_985_; uint8_t v___x_986_; 
v___x_983_ = l_Lean_instInhabitedExpr;
v___x_984_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_976_, v_a_981_);
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_984_);
v___x_986_ = lean_unbox(v_a_985_);
if (v___x_986_ == 0)
{
lean_object* v_numParams_987_; lean_object* v_numDiscrs_988_; lean_object* v_nargs_989_; lean_object* v_dummy_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v_numParams_987_ = lean_ctor_get(v_matcherInfo_977_, 0);
v_numDiscrs_988_ = lean_ctor_get(v_matcherInfo_977_, 1);
v_nargs_989_ = l_Lean_Expr_getAppNumArgs(v_e_976_);
v_dummy_990_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_989_);
v___x_991_ = lean_mk_array(v_nargs_989_, v_dummy_990_);
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_nat_sub(v_nargs_989_, v___x_992_);
lean_dec(v_nargs_989_);
v___x_994_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_976_, v___x_991_, v___x_993_);
v___x_995_ = lean_nat_add(v_numParams_987_, v_numDiscrs_988_);
v___x_996_ = lean_array_get(v___x_983_, v___x_994_, v___x_995_);
lean_dec(v___x_995_);
lean_dec_ref(v___x_994_);
v___x_997_ = l_Lean_Expr_isFVar(v___x_996_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v___x_996_);
lean_dec(v_a_985_);
lean_dec(v_mvarId_975_);
v___x_998_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2);
v___x_999_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v___x_998_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_999_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; lean_object* v___x_1004_; 
v___x_1000_ = l_Lean_Expr_fvarId_x21(v___x_996_);
lean_dec(v___x_996_);
v___x_1001_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3));
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_unbox(v_a_985_);
lean_dec(v_a_985_);
v___x_1004_ = l_Lean_MVarId_cases(v_mvarId_975_, v___x_1000_, v___x_1001_, v___x_1003_, v___x_1002_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1016_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1016_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1016_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
size_t v_sz_1009_; size_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
v_sz_1009_ = lean_array_size(v_a_1005_);
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_1009_, v___x_1010_, v_a_1005_);
v___x_1012_ = lean_array_to_list(v___x_1011_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1012_);
v___x_1014_ = v___x_1007_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1004_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1004_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
else
{
lean_object* v___x_1025_; 
lean_dec(v_a_985_);
v___x_1025_ = l_Lean_Meta_Split_splitMatch(v_mvarId_975_, v_e_976_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___boxed(lean_object* v_mvarId_1026_, lean_object* v_e_1027_, lean_object* v_matcherInfo_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v_mvarId_1026_, v_e_1027_, v_matcherInfo_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec_ref(v_matcherInfo_1028_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(lean_object* v_msg_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___f_1041_; lean_object* v___x_11820__overap_1042_; lean_object* v___x_1043_; 
v___f_1041_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_11820__overap_1042_ = lean_panic_fn_borrowed(v___f_1041_, v_msg_1035_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
v___x_1043_ = lean_apply_5(v___x_11820__overap_1042_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, lean_box(0));
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1___boxed(lean_object* v_msg_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v_msg_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(lean_object* v_type_1051_, lean_object* v_k_1052_, uint8_t v_cleanupAnnotations_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___f_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1059_, 0, v_k_1052_);
v___x_1060_ = 0;
v___x_1061_ = lean_box(0);
v___x_1062_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1060_, v___x_1061_, v_type_1051_, v___f_1059_, v_cleanupAnnotations_1053_, v___x_1060_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_a_1071_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1062_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1062_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg___boxed(lean_object* v_type_1079_, lean_object* v_k_1080_, lean_object* v_cleanupAnnotations_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1087_; lean_object* v_res_1088_; 
v_cleanupAnnotations_boxed_1087_ = lean_unbox(v_cleanupAnnotations_1081_);
v_res_1088_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1079_, v_k_1080_, v_cleanupAnnotations_boxed_1087_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(lean_object* v_00_u03b1_1089_, lean_object* v_type_1090_, lean_object* v_k_1091_, uint8_t v_cleanupAnnotations_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1090_, v_k_1091_, v_cleanupAnnotations_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___boxed(lean_object* v_00_u03b1_1099_, lean_object* v_type_1100_, lean_object* v_k_1101_, lean_object* v_cleanupAnnotations_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1108_; lean_object* v_res_1109_; 
v_cleanupAnnotations_boxed_1108_ = lean_unbox(v_cleanupAnnotations_1102_);
v_res_1109_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(v_00_u03b1_1099_, v_type_1100_, v_k_1101_, v_cleanupAnnotations_boxed_1108_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(lean_object* v_e_1110_, lean_object* v___y_1111_){
_start:
{
uint8_t v___x_1113_; 
v___x_1113_ = l_Lean_Expr_hasMVar(v_e_1110_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_e_1110_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; lean_object* v_mctx_1116_; lean_object* v___x_1117_; lean_object* v_fst_1118_; lean_object* v_snd_1119_; lean_object* v___x_1120_; lean_object* v_cache_1121_; lean_object* v_zetaDeltaFVarIds_1122_; lean_object* v_postponed_1123_; lean_object* v_diag_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1133_; 
v___x_1115_ = lean_st_ref_get(v___y_1111_);
v_mctx_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref(v_mctx_1116_);
lean_dec(v___x_1115_);
v___x_1117_ = l_Lean_instantiateMVarsCore(v_mctx_1116_, v_e_1110_);
v_fst_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_fst_1118_);
v_snd_1119_ = lean_ctor_get(v___x_1117_, 1);
lean_inc(v_snd_1119_);
lean_dec_ref(v___x_1117_);
v___x_1120_ = lean_st_ref_take(v___y_1111_);
v_cache_1121_ = lean_ctor_get(v___x_1120_, 1);
v_zetaDeltaFVarIds_1122_ = lean_ctor_get(v___x_1120_, 2);
v_postponed_1123_ = lean_ctor_get(v___x_1120_, 3);
v_diag_1124_ = lean_ctor_get(v___x_1120_, 4);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v___x_1120_, 0);
lean_dec(v_unused_1134_);
v___x_1126_ = v___x_1120_;
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_diag_1124_);
lean_inc(v_postponed_1123_);
lean_inc(v_zetaDeltaFVarIds_1122_);
lean_inc(v_cache_1121_);
lean_dec(v___x_1120_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v_snd_1119_);
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_snd_1119_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_cache_1121_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_zetaDeltaFVarIds_1122_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_postponed_1123_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_diag_1124_);
v___x_1129_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_st_ref_put(v___y_1111_, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_fst_1118_);
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg___boxed(lean_object* v_e_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1135_, v___y_1136_);
lean_dec(v___y_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(lean_object* v_e_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1139_, v___y_1141_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___boxed(lean_object* v_e_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(v_e_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(lean_object* v_x_1153_, lean_object* v_motiveBody_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Meta_getLevel(v_motiveBody_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0___boxed(lean_object* v_x_1161_, lean_object* v_motiveBody_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(v_x_1161_, v_motiveBody_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec_ref(v_x_1161_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(lean_object* v___x_1169_, lean_object* v___x_1170_, lean_object* v_alpha_1171_, uint8_t v___x_1172_, lean_object* v_xs_1173_, lean_object* v_x_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; uint8_t v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; 
v___x_1180_ = l_Lean_Level_ofNat(v___x_1169_);
v___x_1181_ = l_Lean_Expr_sort___override(v___x_1180_);
v___x_1182_ = l_Lean_Expr_forallE___override(v___x_1170_, v_alpha_1171_, v___x_1181_, v___x_1172_);
v___x_1183_ = 0;
v___x_1184_ = 1;
v___x_1185_ = 1;
v___x_1186_ = l_Lean_Meta_mkForallFVars(v_xs_1173_, v___x_1182_, v___x_1183_, v___x_1184_, v___x_1184_, v___x_1185_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed(lean_object* v___x_1187_, lean_object* v___x_1188_, lean_object* v_alpha_1189_, lean_object* v___x_1190_, lean_object* v_xs_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v___x_15896__boxed_1198_; lean_object* v_res_1199_; 
v___x_15896__boxed_1198_ = lean_unbox(v___x_1190_);
v_res_1199_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(v___x_1187_, v___x_1188_, v_alpha_1189_, v___x_15896__boxed_1198_, v_xs_1191_, v_x_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_x_1192_);
lean_dec_ref(v_xs_1191_);
lean_dec(v___x_1187_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(lean_object* v___x_1206_, lean_object* v___x_1207_, lean_object* v_rel_1208_, lean_object* v___x_1209_, lean_object* v_beta_1210_, uint8_t v___x_1211_, lean_object* v_alpha_1212_, uint8_t v___x_1213_, lean_object* v_xs_1214_, lean_object* v_x_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1221_ = l_Lean_mkAppN(v___x_1206_, v_xs_1214_);
v___x_1222_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_xs_1214_);
v___x_1224_ = lean_array_push(v_xs_1214_, v___x_1207_);
v___x_1225_ = l_Lean_mkAppN(v_rel_1208_, v___x_1224_);
lean_dec_ref(v___x_1224_);
v___x_1226_ = l_Lean_Expr_bvar___override(v___x_1209_);
v___x_1227_ = l_Lean_Expr_app___override(v_beta_1210_, v___x_1226_);
v___x_1228_ = l_Lean_Expr_forallE___override(v___x_1223_, v___x_1225_, v___x_1227_, v___x_1211_);
v___x_1229_ = l_Lean_Expr_forallE___override(v___x_1222_, v_alpha_1212_, v___x_1228_, v___x_1211_);
v___x_1230_ = l_Lean_mkArrow(v___x_1229_, v___x_1221_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; uint8_t v___x_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = 1;
v___x_1233_ = 1;
v___x_1234_ = l_Lean_Meta_mkLambdaFVars(v_xs_1214_, v_a_1231_, v___x_1213_, v___x_1232_, v___x_1213_, v___x_1232_, v___x_1233_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec_ref(v_xs_1214_);
return v___x_1234_;
}
else
{
lean_dec_ref(v_xs_1214_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed(lean_object* v___x_1235_, lean_object* v___x_1236_, lean_object* v_rel_1237_, lean_object* v___x_1238_, lean_object* v_beta_1239_, lean_object* v___x_1240_, lean_object* v_alpha_1241_, lean_object* v___x_1242_, lean_object* v_xs_1243_, lean_object* v_x_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
uint8_t v___x_15950__boxed_1250_; uint8_t v___x_15951__boxed_1251_; lean_object* v_res_1252_; 
v___x_15950__boxed_1250_ = lean_unbox(v___x_1240_);
v___x_15951__boxed_1251_ = lean_unbox(v___x_1242_);
v_res_1252_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(v___x_1235_, v___x_1236_, v_rel_1237_, v___x_1238_, v_beta_1239_, v___x_15950__boxed_1250_, v_alpha_1241_, v___x_15951__boxed_1251_, v_xs_1243_, v_x_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec_ref(v_x_1244_);
return v_res_1252_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1));
v___x_1256_ = lean_unsigned_to_nat(10u);
v___x_1257_ = lean_unsigned_to_nat(146u);
v___x_1258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0));
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_1260_ = l_mkPanicMessageWithDecl(v___x_1259_, v___x_1258_, v___x_1257_, v___x_1256_, v___x_1255_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(lean_object* v___f_1261_, uint8_t v___x_1262_, lean_object* v_a_1263_, uint8_t v___x_1264_, lean_object* v_ys_1265_, lean_object* v_altBodyType_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
uint8_t v___x_1272_; 
v___x_1272_ = l_Lean_Expr_isForall(v_altBodyType_1266_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec_ref(v_ys_1265_);
lean_dec_ref(v_a_1263_);
lean_dec_ref(v___f_1261_);
v___x_1273_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2);
v___x_1274_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v___x_1273_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1274_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = l_Lean_Expr_bindingDomain_x21(v_altBodyType_1266_);
v___x_1276_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_1277_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_1275_, v___x_1276_, v___f_1261_, v___x_1262_, v___x_1262_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
lean_inc_ref(v_ys_1265_);
v___x_1279_ = lean_array_push(v_ys_1265_, v_a_1278_);
v___x_1280_ = l_Lean_mkAppN(v_a_1263_, v___x_1279_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = 1;
v___x_1282_ = l_Lean_Meta_mkLambdaFVars(v_ys_1265_, v___x_1280_, v___x_1262_, v___x_1264_, v___x_1262_, v___x_1264_, v___x_1281_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec_ref(v_ys_1265_);
return v___x_1282_;
}
else
{
lean_dec_ref(v_ys_1265_);
lean_dec_ref(v_a_1263_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed(lean_object* v___f_1283_, lean_object* v___x_1284_, lean_object* v_a_1285_, lean_object* v___x_1286_, lean_object* v_ys_1287_, lean_object* v_altBodyType_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
uint8_t v___x_16035__boxed_1294_; uint8_t v___x_16036__boxed_1295_; lean_object* v_res_1296_; 
v___x_16035__boxed_1294_ = lean_unbox(v___x_1284_);
v___x_16036__boxed_1295_ = lean_unbox(v___x_1286_);
v_res_1296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(v___f_1283_, v___x_16035__boxed_1294_, v_a_1285_, v___x_16036__boxed_1295_, v_ys_1287_, v_altBodyType_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec_ref(v_altBodyType_1288_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(lean_object* v___x_1297_, lean_object* v___x_1298_, lean_object* v_f_1299_, uint8_t v___x_1300_, uint8_t v___x_1301_, lean_object* v_ys_1302_, lean_object* v_x_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; 
v___x_1309_ = lean_array_get_borrowed(v___x_1297_, v_ys_1302_, v___x_1298_);
lean_inc(v___x_1309_);
v___x_1310_ = l_Lean_Expr_app___override(v_f_1299_, v___x_1309_);
v___x_1311_ = 1;
v___x_1312_ = l_Lean_Meta_mkLambdaFVars(v_ys_1302_, v___x_1310_, v___x_1300_, v___x_1301_, v___x_1300_, v___x_1301_, v___x_1311_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed(lean_object* v___x_1313_, lean_object* v___x_1314_, lean_object* v_f_1315_, lean_object* v___x_1316_, lean_object* v___x_1317_, lean_object* v_ys_1318_, lean_object* v_x_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v___x_16091__boxed_1325_; uint8_t v___x_16092__boxed_1326_; lean_object* v_res_1327_; 
v___x_16091__boxed_1325_ = lean_unbox(v___x_1316_);
v___x_16092__boxed_1326_ = lean_unbox(v___x_1317_);
v_res_1327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(v___x_1313_, v___x_1314_, v_f_1315_, v___x_16091__boxed_1325_, v___x_16092__boxed_1326_, v_ys_1318_, v_x_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v_x_1319_);
lean_dec_ref(v_ys_1318_);
lean_dec(v___x_1314_);
lean_dec_ref(v___x_1313_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(lean_object* v_f_1328_, lean_object* v_as_1329_, size_t v_sz_1330_, size_t v_i_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_usize_dec_lt(v_i_1331_, v_sz_1330_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref(v_f_1328_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_b_1332_);
return v___x_1339_;
}
else
{
lean_object* v_snd_1340_; lean_object* v_fst_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1404_; 
v_snd_1340_ = lean_ctor_get(v_b_1332_, 1);
v_fst_1341_ = lean_ctor_get(v_b_1332_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_b_1332_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1343_ = v_b_1332_;
v_isShared_1344_ = v_isSharedCheck_1404_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_snd_1340_);
lean_inc(v_fst_1341_);
lean_dec(v_b_1332_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1404_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_array_1345_; lean_object* v_start_1346_; lean_object* v_stop_1347_; uint8_t v___x_1348_; 
v_array_1345_ = lean_ctor_get(v_snd_1340_, 0);
v_start_1346_ = lean_ctor_get(v_snd_1340_, 1);
v_stop_1347_ = lean_ctor_get(v_snd_1340_, 2);
v___x_1348_ = lean_nat_dec_lt(v_start_1346_, v_stop_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1350_; 
lean_dec_ref(v_f_1328_);
if (v_isShared_1344_ == 0)
{
v___x_1350_ = v___x_1343_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_fst_1341_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_snd_1340_);
v___x_1350_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
}
else
{
lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1400_; 
lean_inc(v_stop_1347_);
lean_inc(v_start_1346_);
lean_inc_ref(v_array_1345_);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_snd_1340_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; lean_object* v_unused_1402_; lean_object* v_unused_1403_; 
v_unused_1401_ = lean_ctor_get(v_snd_1340_, 2);
lean_dec(v_unused_1401_);
v_unused_1402_ = lean_ctor_get(v_snd_1340_, 1);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_snd_1340_, 0);
lean_dec(v_unused_1403_);
v___x_1354_ = v_snd_1340_;
v_isShared_1355_ = v_isSharedCheck_1400_;
goto v_resetjp_1353_;
}
else
{
lean_dec(v_snd_1340_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1400_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; lean_object* v_a_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___f_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1356_ = l_Lean_instInhabitedExpr;
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = 0;
v_a_1359_ = lean_array_uget_borrowed(v_as_1329_, v_i_1331_);
v___x_1360_ = lean_box(v___x_1358_);
v___x_1361_ = lean_box(v___x_1348_);
lean_inc_ref(v_f_1328_);
v___f_1362_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1362_, 0, v___x_1356_);
lean_closure_set(v___f_1362_, 1, v___x_1357_);
lean_closure_set(v___f_1362_, 2, v_f_1328_);
lean_closure_set(v___f_1362_, 3, v___x_1360_);
lean_closure_set(v___f_1362_, 4, v___x_1361_);
v___x_1363_ = lean_box(v___x_1358_);
v___x_1364_ = lean_box(v___x_1348_);
lean_inc(v_a_1359_);
v___f_1365_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1365_, 0, v___f_1362_);
lean_closure_set(v___f_1365_, 1, v___x_1363_);
lean_closure_set(v___f_1365_, 2, v_a_1359_);
lean_closure_set(v___f_1365_, 3, v___x_1364_);
v___x_1366_ = lean_array_fget(v_array_1345_, v_start_1346_);
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_add(v_start_1346_, v___x_1367_);
lean_dec(v_start_1346_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v___x_1368_);
v___x_1370_ = v___x_1354_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_array_1345_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_stop_1347_);
v___x_1370_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; 
lean_inc(v___y_1336_);
lean_inc_ref(v___y_1335_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v_a_1359_);
v___x_1371_ = lean_infer_type(v_a_1359_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1366_);
v___x_1374_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1372_, v___x_1373_, v___f_1365_, v___x_1358_, v___x_1358_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = l_Lean_Expr_app___override(v_fst_1341_, v_a_1375_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 1, v___x_1370_);
lean_ctor_set(v___x_1343_, 0, v___x_1376_);
v___x_1378_ = v___x_1343_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v___x_1370_);
v___x_1378_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
size_t v___x_1379_; size_t v___x_1380_; 
v___x_1379_ = ((size_t)1ULL);
v___x_1380_ = lean_usize_add(v_i_1331_, v___x_1379_);
v_i_1331_ = v___x_1380_;
v_b_1332_ = v___x_1378_;
goto _start;
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v___x_1370_);
lean_del_object(v___x_1343_);
lean_dec(v_fst_1341_);
lean_dec_ref(v_f_1328_);
v_a_1383_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1374_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1374_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec_ref(v___x_1370_);
lean_dec(v___x_1366_);
lean_dec_ref(v___f_1365_);
lean_del_object(v___x_1343_);
lean_dec(v_fst_1341_);
lean_dec_ref(v_f_1328_);
v_a_1391_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1371_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1371_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___boxed(lean_object* v_f_1405_, lean_object* v_as_1406_, lean_object* v_sz_1407_, lean_object* v_i_1408_, lean_object* v_b_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
size_t v_sz_boxed_1415_; size_t v_i_boxed_1416_; lean_object* v_res_1417_; 
v_sz_boxed_1415_ = lean_unbox_usize(v_sz_1407_);
lean_dec(v_sz_1407_);
v_i_boxed_1416_ = lean_unbox_usize(v_i_1408_);
lean_dec(v_i_1408_);
v_res_1417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1405_, v_as_1406_, v_sz_boxed_1415_, v_i_boxed_1416_, v_b_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec_ref(v_as_1406_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(lean_object* v_as_x27_1418_, lean_object* v_b_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
if (lean_obj_tag(v_as_x27_1418_) == 0)
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_b_1419_);
return v___x_1425_;
}
else
{
lean_object* v_head_1426_; lean_object* v_tail_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; lean_object* v___x_1430_; 
v_head_1426_ = lean_ctor_get(v_as_x27_1418_, 0);
v_tail_1427_ = lean_ctor_get(v_as_x27_1418_, 1);
v___x_1428_ = lean_box(0);
v___x_1429_ = 1;
lean_inc(v_head_1426_);
v___x_1430_ = l_Lean_MVarId_refl(v_head_1426_, v___x_1429_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_dec_ref_known(v___x_1430_, 1);
v_as_x27_1418_ = v_tail_1427_;
v_b_1419_ = v___x_1428_;
goto _start;
}
else
{
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg___boxed(lean_object* v_as_x27_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_1432_, v_b_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v_as_x27_1432_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(lean_object* v___x_1440_, lean_object* v_matcherInfo_1441_, lean_object* v___x_1442_, lean_object* v___x_1443_, lean_object* v_f_1444_, lean_object* v_discrs_1445_, lean_object* v___x_1446_, lean_object* v_rel_1447_, lean_object* v___x_1448_, uint8_t v___x_1449_, lean_object* v_alpha_1450_, lean_object* v___x_1451_, lean_object* v_beta_1452_, lean_object* v___x_1453_, uint8_t v___x_1454_, lean_object* v___x_1455_, lean_object* v___x_1456_, lean_object* v___x_1457_, lean_object* v_alts_1458_, lean_object* v_x_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; size_t v_sz_1470_; size_t v___x_1471_; lean_object* v___x_1472_; 
v___x_1465_ = l_Lean_mkAppN(v___x_1440_, v_alts_1458_);
lean_inc_ref(v_matcherInfo_1441_);
v___x_1466_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_matcherInfo_1441_);
v___x_1467_ = lean_array_get_size(v___x_1466_);
v___x_1468_ = l_Array_toSubarray___redArg(v___x_1466_, v___x_1442_, v___x_1467_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1443_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v_sz_1470_ = lean_array_size(v_alts_1458_);
v___x_1471_ = ((size_t)0ULL);
lean_inc_ref(v_f_1444_);
v___x_1472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1444_, v_alts_1458_, v_sz_1470_, v___x_1471_, v___x_1469_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v_fst_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1568_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v_fst_1474_ = lean_ctor_get(v_a_1473_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_a_1473_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_a_1473_, 1);
lean_dec(v_unused_1569_);
v___x_1476_ = v_a_1473_;
v_isShared_1477_ = v_isSharedCheck_1568_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_fst_1474_);
lean_dec(v_a_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1568_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1478_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1479_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_discrs_1445_);
v___x_1480_ = lean_array_push(v_discrs_1445_, v___x_1446_);
lean_inc_ref(v_rel_1447_);
v___x_1481_ = l_Lean_mkAppN(v_rel_1447_, v___x_1480_);
lean_dec_ref(v___x_1480_);
v___x_1482_ = l_Lean_Expr_bvar___override(v___x_1448_);
lean_inc_ref(v_f_1444_);
v___x_1483_ = l_Lean_Expr_app___override(v_f_1444_, v___x_1482_);
v___x_1484_ = l_Lean_Expr_lam___override(v___x_1479_, v___x_1481_, v___x_1483_, v___x_1449_);
lean_inc_ref(v_alpha_1450_);
v___x_1485_ = l_Lean_Expr_lam___override(v___x_1478_, v_alpha_1450_, v___x_1484_, v___x_1449_);
v___x_1486_ = l_Lean_Expr_app___override(v___x_1465_, v___x_1485_);
lean_inc(v_fst_1474_);
v___x_1487_ = l_Lean_Meta_mkEq(v___x_1486_, v_fst_1474_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc_n(v_a_1488_, 2);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1489_ = lean_box(0);
v___x_1490_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1488_, v___x_1489_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v___x_1492_ = l_Lean_Expr_mvarId_x21(v_a_1491_);
v___x_1493_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v___x_1492_, v_fst_1474_, v_matcherInfo_1441_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec_ref(v_matcherInfo_1441_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v___x_1495_ = lean_box(0);
v___x_1496_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_a_1494_, v___x_1495_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v_a_1494_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v___x_1497_; lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref_known(v___x_1496_, 1);
v___x_1497_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_1491_, v___y_1461_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1543_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1543_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; 
v___x_1502_ = lean_unsigned_to_nat(5u);
v___x_1503_ = lean_mk_empty_array_with_capacity(v___x_1502_);
v___x_1504_ = lean_array_push(v___x_1503_, v___x_1451_);
v___x_1505_ = lean_array_push(v___x_1504_, v_alpha_1450_);
v___x_1506_ = lean_array_push(v___x_1505_, v_beta_1452_);
v___x_1507_ = lean_array_push(v___x_1506_, v_f_1444_);
v___x_1508_ = lean_array_push(v___x_1507_, v_rel_1447_);
v___x_1509_ = l_Array_append___redArg(v___x_1453_, v___x_1508_);
lean_dec_ref(v___x_1508_);
v___x_1510_ = l_Array_append___redArg(v___x_1509_, v_discrs_1445_);
lean_dec_ref(v_discrs_1445_);
v___x_1511_ = l_Array_append___redArg(v___x_1510_, v_alts_1458_);
v___x_1512_ = 1;
v___x_1513_ = 1;
v___x_1514_ = l_Lean_Meta_mkForallFVars(v___x_1511_, v_a_1488_, v___x_1454_, v___x_1512_, v___x_1512_, v___x_1513_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = l_Lean_Meta_mkLambdaFVars(v___x_1511_, v_a_1498_, v___x_1454_, v___x_1512_, v___x_1454_, v___x_1512_, v___x_1513_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec_ref(v___x_1511_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
lean_inc(v___x_1455_);
v___x_1518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1455_);
lean_ctor_set(v___x_1518_, 1, v___x_1456_);
lean_ctor_set(v___x_1518_, 2, v_a_1515_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set_tag(v___x_1476_, 1);
lean_ctor_set(v___x_1476_, 1, v___x_1457_);
lean_ctor_set(v___x_1476_, 0, v___x_1455_);
v___x_1520_ = v___x_1476_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___x_1457_);
v___x_1520_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1518_);
lean_ctor_set(v___x_1521_, 1, v_a_1517_);
lean_ctor_set(v___x_1521_, 2, v___x_1520_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set_tag(v___x_1500_, 2);
lean_ctor_set(v___x_1500_, 0, v___x_1521_);
v___x_1523_ = v___x_1500_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_addDecl(v___x_1523_, v___x_1454_, v___y_1462_, v___y_1463_);
return v___x_1524_;
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_a_1515_);
lean_del_object(v___x_1500_);
lean_del_object(v___x_1476_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec(v___x_1455_);
v_a_1527_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1516_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1516_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v___x_1511_);
lean_del_object(v___x_1500_);
lean_dec(v_a_1498_);
lean_del_object(v___x_1476_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec(v___x_1455_);
v_a_1535_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1514_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1514_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
else
{
lean_dec(v_a_1491_);
lean_dec(v_a_1488_);
lean_del_object(v___x_1476_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec(v___x_1455_);
lean_dec_ref(v___x_1453_);
lean_dec_ref(v_beta_1452_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_alpha_1450_);
lean_dec_ref(v_rel_1447_);
lean_dec_ref(v_discrs_1445_);
lean_dec_ref(v_f_1444_);
return v___x_1496_;
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_a_1491_);
lean_dec(v_a_1488_);
lean_del_object(v___x_1476_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec(v___x_1455_);
lean_dec_ref(v___x_1453_);
lean_dec_ref(v_beta_1452_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_alpha_1450_);
lean_dec_ref(v_rel_1447_);
lean_dec_ref(v_discrs_1445_);
lean_dec_ref(v_f_1444_);
v_a_1544_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1493_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1493_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_a_1488_);
lean_del_object(v___x_1476_);
lean_dec(v_fst_1474_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec(v___x_1455_);
lean_dec_ref(v___x_1453_);
lean_dec_ref(v_beta_1452_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_alpha_1450_);
lean_dec_ref(v_rel_1447_);
lean_dec_ref(v_discrs_1445_);
lean_dec_ref(v_f_1444_);
lean_dec_ref(v_matcherInfo_1441_);
v_a_1552_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1490_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1490_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1476_);
lean_dec(v_fst_1474_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec(v___x_1455_);
lean_dec_ref(v___x_1453_);
lean_dec_ref(v_beta_1452_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_alpha_1450_);
lean_dec_ref(v_rel_1447_);
lean_dec_ref(v_discrs_1445_);
lean_dec_ref(v_f_1444_);
lean_dec_ref(v_matcherInfo_1441_);
v_a_1560_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1487_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1487_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec_ref(v___x_1465_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
lean_dec(v___x_1455_);
lean_dec_ref(v___x_1453_);
lean_dec_ref(v_beta_1452_);
lean_dec_ref(v___x_1451_);
lean_dec_ref(v_alpha_1450_);
lean_dec(v___x_1448_);
lean_dec_ref(v_rel_1447_);
lean_dec_ref(v___x_1446_);
lean_dec_ref(v_discrs_1445_);
lean_dec_ref(v_f_1444_);
lean_dec_ref(v_matcherInfo_1441_);
v_a_1570_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1472_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1472_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed(lean_object** _args){
lean_object* v___x_1578_ = _args[0];
lean_object* v_matcherInfo_1579_ = _args[1];
lean_object* v___x_1580_ = _args[2];
lean_object* v___x_1581_ = _args[3];
lean_object* v_f_1582_ = _args[4];
lean_object* v_discrs_1583_ = _args[5];
lean_object* v___x_1584_ = _args[6];
lean_object* v_rel_1585_ = _args[7];
lean_object* v___x_1586_ = _args[8];
lean_object* v___x_1587_ = _args[9];
lean_object* v_alpha_1588_ = _args[10];
lean_object* v___x_1589_ = _args[11];
lean_object* v_beta_1590_ = _args[12];
lean_object* v___x_1591_ = _args[13];
lean_object* v___x_1592_ = _args[14];
lean_object* v___x_1593_ = _args[15];
lean_object* v___x_1594_ = _args[16];
lean_object* v___x_1595_ = _args[17];
lean_object* v_alts_1596_ = _args[18];
lean_object* v_x_1597_ = _args[19];
lean_object* v___y_1598_ = _args[20];
lean_object* v___y_1599_ = _args[21];
lean_object* v___y_1600_ = _args[22];
lean_object* v___y_1601_ = _args[23];
lean_object* v___y_1602_ = _args[24];
_start:
{
uint8_t v___x_16306__boxed_1603_; uint8_t v___x_16309__boxed_1604_; lean_object* v_res_1605_; 
v___x_16306__boxed_1603_ = lean_unbox(v___x_1587_);
v___x_16309__boxed_1604_ = lean_unbox(v___x_1592_);
v_res_1605_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(v___x_1578_, v_matcherInfo_1579_, v___x_1580_, v___x_1581_, v_f_1582_, v_discrs_1583_, v___x_1584_, v_rel_1585_, v___x_1586_, v___x_16306__boxed_1603_, v_alpha_1588_, v___x_1589_, v_beta_1590_, v___x_1591_, v___x_16309__boxed_1604_, v___x_1593_, v___x_1594_, v___x_1595_, v_alts_1596_, v_x_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v_x_1597_);
lean_dec_ref(v_alts_1596_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(lean_object* v___x_1606_, lean_object* v___x_1607_, lean_object* v_matcherInfo_1608_, lean_object* v___x_1609_, lean_object* v_f_1610_, lean_object* v___x_1611_, lean_object* v_rel_1612_, lean_object* v___x_1613_, uint8_t v___x_1614_, lean_object* v_alpha_1615_, lean_object* v___x_1616_, lean_object* v_beta_1617_, lean_object* v___x_1618_, uint8_t v___x_1619_, lean_object* v___x_1620_, lean_object* v___x_1621_, lean_object* v___x_1622_, lean_object* v_discrs_1623_, lean_object* v_x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___f_1634_; lean_object* v___x_1635_; 
v___x_1630_ = l_Lean_mkAppN(v___x_1606_, v_discrs_1623_);
v___x_1631_ = l_Lean_mkAppN(v___x_1607_, v_discrs_1623_);
v___x_1632_ = lean_box(v___x_1614_);
v___x_1633_ = lean_box(v___x_1619_);
lean_inc_ref(v_matcherInfo_1608_);
lean_inc_ref(v___x_1630_);
v___f_1634_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1634_, 0, v___x_1630_);
lean_closure_set(v___f_1634_, 1, v_matcherInfo_1608_);
lean_closure_set(v___f_1634_, 2, v___x_1609_);
lean_closure_set(v___f_1634_, 3, v___x_1631_);
lean_closure_set(v___f_1634_, 4, v_f_1610_);
lean_closure_set(v___f_1634_, 5, v_discrs_1623_);
lean_closure_set(v___f_1634_, 6, v___x_1611_);
lean_closure_set(v___f_1634_, 7, v_rel_1612_);
lean_closure_set(v___f_1634_, 8, v___x_1613_);
lean_closure_set(v___f_1634_, 9, v___x_1632_);
lean_closure_set(v___f_1634_, 10, v_alpha_1615_);
lean_closure_set(v___f_1634_, 11, v___x_1616_);
lean_closure_set(v___f_1634_, 12, v_beta_1617_);
lean_closure_set(v___f_1634_, 13, v___x_1618_);
lean_closure_set(v___f_1634_, 14, v___x_1633_);
lean_closure_set(v___f_1634_, 15, v___x_1620_);
lean_closure_set(v___f_1634_, 16, v___x_1621_);
lean_closure_set(v___f_1634_, 17, v___x_1622_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
lean_inc(v___y_1626_);
lean_inc_ref(v___y_1625_);
v___x_1635_ = lean_infer_type(v___x_1630_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_matcherInfo_1608_);
lean_dec_ref(v_matcherInfo_1608_);
v___x_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
v___x_1639_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1636_, v___x_1638_, v___f_1634_, v___x_1619_, v___x_1619_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1639_;
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___f_1634_);
lean_dec_ref(v_matcherInfo_1608_);
v_a_1640_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1635_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1635_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed(lean_object** _args){
lean_object* v___x_1648_ = _args[0];
lean_object* v___x_1649_ = _args[1];
lean_object* v_matcherInfo_1650_ = _args[2];
lean_object* v___x_1651_ = _args[3];
lean_object* v_f_1652_ = _args[4];
lean_object* v___x_1653_ = _args[5];
lean_object* v_rel_1654_ = _args[6];
lean_object* v___x_1655_ = _args[7];
lean_object* v___x_1656_ = _args[8];
lean_object* v_alpha_1657_ = _args[9];
lean_object* v___x_1658_ = _args[10];
lean_object* v_beta_1659_ = _args[11];
lean_object* v___x_1660_ = _args[12];
lean_object* v___x_1661_ = _args[13];
lean_object* v___x_1662_ = _args[14];
lean_object* v___x_1663_ = _args[15];
lean_object* v___x_1664_ = _args[16];
lean_object* v_discrs_1665_ = _args[17];
lean_object* v_x_1666_ = _args[18];
lean_object* v___y_1667_ = _args[19];
lean_object* v___y_1668_ = _args[20];
lean_object* v___y_1669_ = _args[21];
lean_object* v___y_1670_ = _args[22];
lean_object* v___y_1671_ = _args[23];
_start:
{
uint8_t v___x_16587__boxed_1672_; uint8_t v___x_16590__boxed_1673_; lean_object* v_res_1674_; 
v___x_16587__boxed_1672_ = lean_unbox(v___x_1656_);
v___x_16590__boxed_1673_ = lean_unbox(v___x_1661_);
v_res_1674_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(v___x_1648_, v___x_1649_, v_matcherInfo_1650_, v___x_1651_, v_f_1652_, v___x_1653_, v_rel_1654_, v___x_1655_, v___x_16587__boxed_1672_, v_alpha_1657_, v___x_1658_, v_beta_1659_, v___x_1660_, v___x_16590__boxed_1673_, v___x_1662_, v___x_1663_, v___x_1664_, v_discrs_1665_, v_x_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec_ref(v_x_1666_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
if (lean_obj_tag(v_a_1675_) == 0)
{
lean_object* v___x_1677_; 
v___x_1677_ = l_List_reverse___redArg(v_a_1676_);
return v___x_1677_;
}
else
{
lean_object* v_head_1678_; lean_object* v_tail_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1688_; 
v_head_1678_ = lean_ctor_get(v_a_1675_, 0);
v_tail_1679_ = lean_ctor_get(v_a_1675_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_a_1675_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1681_ = v_a_1675_;
v_isShared_1682_ = v_isSharedCheck_1688_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_tail_1679_);
lean_inc(v_head_1678_);
lean_dec(v_a_1675_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1688_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = l_Lean_mkLevelParam(v_head_1678_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v_a_1676_);
lean_ctor_set(v___x_1681_, 0, v___x_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_a_1676_);
v___x_1685_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
v_a_1675_ = v_tail_1679_;
v_a_1676_ = v___x_1685_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__0));
v___x_1691_ = l_Lean_stringToMessageData(v___x_1690_);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__2));
v___x_1694_ = l_Lean_stringToMessageData(v___x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(lean_object* v___x_1695_, lean_object* v___x_1696_, lean_object* v___x_1697_, lean_object* v_beta_1698_, uint8_t v___x_1699_, lean_object* v_alpha_1700_, uint8_t v___x_1701_, lean_object* v_numDiscrs_1702_, lean_object* v___f_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_levelParams_1706_, lean_object* v_matcherName_1707_, lean_object* v___x_1708_, lean_object* v_matcherInfo_1709_, lean_object* v___x_1710_, lean_object* v_f_1711_, lean_object* v___x_1712_, lean_object* v_uElimPos_x3f_1713_, lean_object* v_rel_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___f_1722_; lean_object* v___x_1723_; 
v___x_1720_ = lean_box(v___x_1699_);
v___x_1721_ = lean_box(v___x_1701_);
lean_inc_ref(v_alpha_1700_);
lean_inc_ref(v_beta_1698_);
lean_inc(v___x_1697_);
lean_inc_ref(v_rel_1714_);
lean_inc_ref(v___x_1696_);
lean_inc_ref_n(v___x_1695_, 2);
v___f_1722_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed), 15, 8);
lean_closure_set(v___f_1722_, 0, v___x_1695_);
lean_closure_set(v___f_1722_, 1, v___x_1696_);
lean_closure_set(v___f_1722_, 2, v_rel_1714_);
lean_closure_set(v___f_1722_, 3, v___x_1697_);
lean_closure_set(v___f_1722_, 4, v_beta_1698_);
lean_closure_set(v___f_1722_, 5, v___x_1720_);
lean_closure_set(v___f_1722_, 6, v_alpha_1700_);
lean_closure_set(v___f_1722_, 7, v___x_1721_);
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
v___x_1723_ = lean_infer_type(v___x_1695_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1724_, v___f_1722_, v___x_1701_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc_n(v_a_1726_, 2);
lean_dec_ref_known(v___x_1725_, 1);
lean_inc(v_numDiscrs_1702_);
v___x_1727_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_a_1726_, v_numDiscrs_1702_, v___f_1703_, v___x_1701_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v_matcherLevels_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_a_1704_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_a_1705_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
lean_inc(v_levelParams_1706_);
v___x_1732_ = l_List_appendTR___redArg(v_levelParams_1706_, v___x_1731_);
v___x_1733_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_1706_, v___x_1729_);
if (lean_obj_tag(v_uElimPos_x3f_1713_) == 0)
{
uint8_t v___x_1762_; 
v___x_1762_ = l_Lean_Level_isZero(v_a_1728_);
lean_dec(v_a_1728_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec(v___x_1733_);
lean_dec(v___x_1732_);
lean_dec(v_a_1726_);
lean_dec_ref(v_rel_1714_);
lean_dec(v___x_1712_);
lean_dec_ref(v_f_1711_);
lean_dec(v___x_1710_);
lean_dec_ref(v_matcherInfo_1709_);
lean_dec_ref(v___x_1708_);
lean_dec(v_numDiscrs_1702_);
lean_dec_ref(v_alpha_1700_);
lean_dec_ref(v_beta_1698_);
lean_dec(v___x_1697_);
lean_dec_ref(v___x_1696_);
lean_dec_ref(v___x_1695_);
v___x_1763_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1);
v___x_1764_ = l_Lean_MessageData_ofConstName(v_matcherName_1707_, v___x_1701_);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_1767_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1768_;
}
else
{
lean_inc(v___x_1733_);
v_matcherLevels_1735_ = v___x_1733_;
v___y_1736_ = v___y_1715_;
v___y_1737_ = v___y_1716_;
v___y_1738_ = v___y_1717_;
v___y_1739_ = v___y_1718_;
goto v___jp_1734_;
}
}
else
{
lean_object* v_val_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_val_1769_ = lean_ctor_get(v_uElimPos_x3f_1713_, 0);
lean_inc(v___x_1733_);
v___x_1770_ = lean_array_mk(v___x_1733_);
v___x_1771_ = lean_array_set(v___x_1770_, v_val_1769_, v_a_1728_);
v___x_1772_ = lean_array_to_list(v___x_1771_);
v_matcherLevels_1735_ = v___x_1772_;
v___y_1736_ = v___y_1715_;
v___y_1737_ = v___y_1716_;
v___y_1738_ = v___y_1717_;
v___y_1739_ = v___y_1718_;
goto v___jp_1734_;
}
v___jp_1734_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___f_1749_; lean_object* v___x_1750_; 
lean_inc(v_matcherName_1707_);
v___x_1740_ = l_Lean_Expr_const___override(v_matcherName_1707_, v_matcherLevels_1735_);
v___x_1741_ = l_Lean_Expr_const___override(v_matcherName_1707_, v___x_1733_);
v___x_1742_ = l_Subarray_copy___redArg(v___x_1708_);
v___x_1743_ = l_Lean_mkAppN(v___x_1740_, v___x_1742_);
v___x_1744_ = l_Lean_mkAppN(v___x_1741_, v___x_1742_);
v___x_1745_ = l_Lean_Expr_app___override(v___x_1743_, v_a_1726_);
lean_inc_ref(v___x_1695_);
v___x_1746_ = l_Lean_Expr_app___override(v___x_1744_, v___x_1695_);
v___x_1747_ = lean_box(v___x_1699_);
v___x_1748_ = lean_box(v___x_1701_);
lean_inc_ref(v___x_1745_);
v___f_1749_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed), 24, 17);
lean_closure_set(v___f_1749_, 0, v___x_1745_);
lean_closure_set(v___f_1749_, 1, v___x_1746_);
lean_closure_set(v___f_1749_, 2, v_matcherInfo_1709_);
lean_closure_set(v___f_1749_, 3, v___x_1710_);
lean_closure_set(v___f_1749_, 4, v_f_1711_);
lean_closure_set(v___f_1749_, 5, v___x_1696_);
lean_closure_set(v___f_1749_, 6, v_rel_1714_);
lean_closure_set(v___f_1749_, 7, v___x_1697_);
lean_closure_set(v___f_1749_, 8, v___x_1747_);
lean_closure_set(v___f_1749_, 9, v_alpha_1700_);
lean_closure_set(v___f_1749_, 10, v___x_1695_);
lean_closure_set(v___f_1749_, 11, v_beta_1698_);
lean_closure_set(v___f_1749_, 12, v___x_1742_);
lean_closure_set(v___f_1749_, 13, v___x_1748_);
lean_closure_set(v___f_1749_, 14, v___x_1712_);
lean_closure_set(v___f_1749_, 15, v___x_1732_);
lean_closure_set(v___f_1749_, 16, v___x_1729_);
lean_inc(v___y_1739_);
lean_inc_ref(v___y_1738_);
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1736_);
v___x_1750_ = lean_infer_type(v___x_1745_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_numDiscrs_1702_);
v___x_1753_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1751_, v___x_1752_, v___f_1749_, v___x_1701_, v___x_1701_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
return v___x_1753_;
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v___f_1749_);
lean_dec(v_numDiscrs_1702_);
v_a_1754_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1750_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1750_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_a_1726_);
lean_dec_ref(v_rel_1714_);
lean_dec(v___x_1712_);
lean_dec_ref(v_f_1711_);
lean_dec(v___x_1710_);
lean_dec_ref(v_matcherInfo_1709_);
lean_dec_ref(v___x_1708_);
lean_dec(v_matcherName_1707_);
lean_dec(v_levelParams_1706_);
lean_dec(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec(v_numDiscrs_1702_);
lean_dec_ref(v_alpha_1700_);
lean_dec_ref(v_beta_1698_);
lean_dec(v___x_1697_);
lean_dec_ref(v___x_1696_);
lean_dec_ref(v___x_1695_);
v_a_1773_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1727_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1727_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v_rel_1714_);
lean_dec(v___x_1712_);
lean_dec_ref(v_f_1711_);
lean_dec(v___x_1710_);
lean_dec_ref(v_matcherInfo_1709_);
lean_dec_ref(v___x_1708_);
lean_dec(v_matcherName_1707_);
lean_dec(v_levelParams_1706_);
lean_dec(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v___f_1703_);
lean_dec(v_numDiscrs_1702_);
lean_dec_ref(v_alpha_1700_);
lean_dec_ref(v_beta_1698_);
lean_dec(v___x_1697_);
lean_dec_ref(v___x_1696_);
lean_dec_ref(v___x_1695_);
v_a_1781_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1725_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1725_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v___f_1722_);
lean_dec_ref(v_rel_1714_);
lean_dec(v___x_1712_);
lean_dec_ref(v_f_1711_);
lean_dec(v___x_1710_);
lean_dec_ref(v_matcherInfo_1709_);
lean_dec_ref(v___x_1708_);
lean_dec(v_matcherName_1707_);
lean_dec(v_levelParams_1706_);
lean_dec(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v___f_1703_);
lean_dec(v_numDiscrs_1702_);
lean_dec_ref(v_alpha_1700_);
lean_dec_ref(v_beta_1698_);
lean_dec(v___x_1697_);
lean_dec_ref(v___x_1696_);
lean_dec_ref(v___x_1695_);
v_a_1789_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1723_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1723_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed(lean_object** _args){
lean_object* v___x_1797_ = _args[0];
lean_object* v___x_1798_ = _args[1];
lean_object* v___x_1799_ = _args[2];
lean_object* v_beta_1800_ = _args[3];
lean_object* v___x_1801_ = _args[4];
lean_object* v_alpha_1802_ = _args[5];
lean_object* v___x_1803_ = _args[6];
lean_object* v_numDiscrs_1804_ = _args[7];
lean_object* v___f_1805_ = _args[8];
lean_object* v_a_1806_ = _args[9];
lean_object* v_a_1807_ = _args[10];
lean_object* v_levelParams_1808_ = _args[11];
lean_object* v_matcherName_1809_ = _args[12];
lean_object* v___x_1810_ = _args[13];
lean_object* v_matcherInfo_1811_ = _args[14];
lean_object* v___x_1812_ = _args[15];
lean_object* v_f_1813_ = _args[16];
lean_object* v___x_1814_ = _args[17];
lean_object* v_uElimPos_x3f_1815_ = _args[18];
lean_object* v_rel_1816_ = _args[19];
lean_object* v___y_1817_ = _args[20];
lean_object* v___y_1818_ = _args[21];
lean_object* v___y_1819_ = _args[22];
lean_object* v___y_1820_ = _args[23];
lean_object* v___y_1821_ = _args[24];
_start:
{
uint8_t v___x_16715__boxed_1822_; uint8_t v___x_16716__boxed_1823_; lean_object* v_res_1824_; 
v___x_16715__boxed_1822_ = lean_unbox(v___x_1801_);
v___x_16716__boxed_1823_ = lean_unbox(v___x_1803_);
v_res_1824_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(v___x_1797_, v___x_1798_, v___x_1799_, v_beta_1800_, v___x_16715__boxed_1822_, v_alpha_1802_, v___x_16716__boxed_1823_, v_numDiscrs_1804_, v___f_1805_, v_a_1806_, v_a_1807_, v_levelParams_1808_, v_matcherName_1809_, v___x_1810_, v_matcherInfo_1811_, v___x_1812_, v_f_1813_, v___x_1814_, v_uElimPos_x3f_1815_, v_rel_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v_uElimPos_x3f_1815_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(lean_object* v_k_1825_, lean_object* v_b_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___x_1832_; 
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
v___x_1832_ = lean_apply_6(v_k_1825_, v_b_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, lean_box(0));
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v_k_1833_, lean_object* v_b_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(v_k_1833_, v_b_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(lean_object* v_name_1841_, uint8_t v_bi_1842_, lean_object* v_type_1843_, lean_object* v_k_1844_, uint8_t v_kind_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___f_1851_; lean_object* v___x_1852_; 
v___f_1851_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1851_, 0, v_k_1844_);
v___x_1852_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1841_, v_bi_1842_, v_type_1843_, v___f_1851_, v_kind_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v_a_1861_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1852_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1852_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___boxed(lean_object* v_name_1869_, lean_object* v_bi_1870_, lean_object* v_type_1871_, lean_object* v_k_1872_, lean_object* v_kind_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
uint8_t v_bi_boxed_1879_; uint8_t v_kind_boxed_1880_; lean_object* v_res_1881_; 
v_bi_boxed_1879_ = lean_unbox(v_bi_1870_);
v_kind_boxed_1880_ = lean_unbox(v_kind_1873_);
v_res_1881_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1869_, v_bi_boxed_1879_, v_type_1871_, v_k_1872_, v_kind_boxed_1880_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(lean_object* v_name_1882_, lean_object* v_type_1883_, lean_object* v_k_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
uint8_t v___x_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = 0;
v___x_1891_ = 0;
v___x_1892_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1882_, v___x_1890_, v_type_1883_, v_k_1884_, v___x_1891_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg___boxed(lean_object* v_name_1893_, lean_object* v_type_1894_, lean_object* v_k_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_1893_, v_type_1894_, v_k_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(lean_object* v___x_1905_, lean_object* v___x_1906_, lean_object* v___x_1907_, lean_object* v_beta_1908_, uint8_t v___x_1909_, lean_object* v_alpha_1910_, lean_object* v_numDiscrs_1911_, lean_object* v___f_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_levelParams_1915_, lean_object* v_matcherName_1916_, lean_object* v___x_1917_, lean_object* v_matcherInfo_1918_, lean_object* v___x_1919_, lean_object* v___x_1920_, lean_object* v_uElimPos_x3f_1921_, lean_object* v___f_1922_, lean_object* v_f_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; 
lean_inc(v___y_1927_);
lean_inc_ref(v___y_1926_);
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
lean_inc_ref(v___x_1905_);
v___x_1929_ = lean_infer_type(v___x_1905_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1931_ = 0;
v___x_1932_ = lean_box(v___x_1909_);
v___x_1933_ = lean_box(v___x_1931_);
v___f_1934_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed), 25, 19);
lean_closure_set(v___f_1934_, 0, v___x_1905_);
lean_closure_set(v___f_1934_, 1, v___x_1906_);
lean_closure_set(v___f_1934_, 2, v___x_1907_);
lean_closure_set(v___f_1934_, 3, v_beta_1908_);
lean_closure_set(v___f_1934_, 4, v___x_1932_);
lean_closure_set(v___f_1934_, 5, v_alpha_1910_);
lean_closure_set(v___f_1934_, 6, v___x_1933_);
lean_closure_set(v___f_1934_, 7, v_numDiscrs_1911_);
lean_closure_set(v___f_1934_, 8, v___f_1912_);
lean_closure_set(v___f_1934_, 9, v_a_1913_);
lean_closure_set(v___f_1934_, 10, v_a_1914_);
lean_closure_set(v___f_1934_, 11, v_levelParams_1915_);
lean_closure_set(v___f_1934_, 12, v_matcherName_1916_);
lean_closure_set(v___f_1934_, 13, v___x_1917_);
lean_closure_set(v___f_1934_, 14, v_matcherInfo_1918_);
lean_closure_set(v___f_1934_, 15, v___x_1919_);
lean_closure_set(v___f_1934_, 16, v_f_1923_);
lean_closure_set(v___f_1934_, 17, v___x_1920_);
lean_closure_set(v___f_1934_, 18, v_uElimPos_x3f_1921_);
v___x_1935_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1930_, v___f_1922_, v___x_1931_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__1));
v___x_1938_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_1937_, v_a_1936_, v___f_1934_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
return v___x_1938_;
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v___f_1934_);
v_a_1939_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1935_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1935_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v_f_1923_);
lean_dec_ref(v___f_1922_);
lean_dec(v_uElimPos_x3f_1921_);
lean_dec(v___x_1920_);
lean_dec(v___x_1919_);
lean_dec_ref(v_matcherInfo_1918_);
lean_dec_ref(v___x_1917_);
lean_dec(v_matcherName_1916_);
lean_dec(v_levelParams_1915_);
lean_dec(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec_ref(v___f_1912_);
lean_dec(v_numDiscrs_1911_);
lean_dec_ref(v_alpha_1910_);
lean_dec_ref(v_beta_1908_);
lean_dec(v___x_1907_);
lean_dec_ref(v___x_1906_);
lean_dec_ref(v___x_1905_);
v_a_1947_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1929_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1929_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed(lean_object** _args){
lean_object* v___x_1955_ = _args[0];
lean_object* v___x_1956_ = _args[1];
lean_object* v___x_1957_ = _args[2];
lean_object* v_beta_1958_ = _args[3];
lean_object* v___x_1959_ = _args[4];
lean_object* v_alpha_1960_ = _args[5];
lean_object* v_numDiscrs_1961_ = _args[6];
lean_object* v___f_1962_ = _args[7];
lean_object* v_a_1963_ = _args[8];
lean_object* v_a_1964_ = _args[9];
lean_object* v_levelParams_1965_ = _args[10];
lean_object* v_matcherName_1966_ = _args[11];
lean_object* v___x_1967_ = _args[12];
lean_object* v_matcherInfo_1968_ = _args[13];
lean_object* v___x_1969_ = _args[14];
lean_object* v___x_1970_ = _args[15];
lean_object* v_uElimPos_x3f_1971_ = _args[16];
lean_object* v___f_1972_ = _args[17];
lean_object* v_f_1973_ = _args[18];
lean_object* v___y_1974_ = _args[19];
lean_object* v___y_1975_ = _args[20];
lean_object* v___y_1976_ = _args[21];
lean_object* v___y_1977_ = _args[22];
lean_object* v___y_1978_ = _args[23];
_start:
{
uint8_t v___x_17018__boxed_1979_; lean_object* v_res_1980_; 
v___x_17018__boxed_1979_ = lean_unbox(v___x_1959_);
v_res_1980_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(v___x_1955_, v___x_1956_, v___x_1957_, v_beta_1958_, v___x_17018__boxed_1979_, v_alpha_1960_, v_numDiscrs_1961_, v___f_1962_, v_a_1963_, v_a_1964_, v_levelParams_1965_, v_matcherName_1966_, v___x_1967_, v_matcherInfo_1968_, v___x_1969_, v___x_1970_, v_uElimPos_x3f_1971_, v___f_1972_, v_f_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(lean_object* v___x_1987_, lean_object* v_alpha_1988_, lean_object* v___x_1989_, lean_object* v___x_1990_, lean_object* v_numDiscrs_1991_, lean_object* v___f_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_levelParams_1995_, lean_object* v_matcherName_1996_, lean_object* v___x_1997_, lean_object* v_matcherInfo_1998_, lean_object* v___x_1999_, lean_object* v_uElimPos_x3f_2000_, lean_object* v_beta_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; lean_object* v___f_2013_; lean_object* v___x_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2007_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__1));
v___x_2008_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__3));
lean_inc_n(v___x_1987_, 2);
v___x_2009_ = l_Lean_Expr_bvar___override(v___x_1987_);
lean_inc_ref(v___x_2009_);
lean_inc_ref(v_beta_2001_);
v___x_2010_ = l_Lean_Expr_app___override(v_beta_2001_, v___x_2009_);
v___x_2011_ = 0;
v___x_2012_ = lean_box(v___x_2011_);
lean_inc_ref_n(v_alpha_1988_, 2);
v___f_2013_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2013_, 0, v___x_1987_);
lean_closure_set(v___f_2013_, 1, v___x_2008_);
lean_closure_set(v___f_2013_, 2, v_alpha_1988_);
lean_closure_set(v___f_2013_, 3, v___x_2012_);
v___x_2014_ = lean_box(v___x_2011_);
v___f_2015_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed), 24, 18);
lean_closure_set(v___f_2015_, 0, v___x_1989_);
lean_closure_set(v___f_2015_, 1, v___x_2009_);
lean_closure_set(v___f_2015_, 2, v___x_1990_);
lean_closure_set(v___f_2015_, 3, v_beta_2001_);
lean_closure_set(v___f_2015_, 4, v___x_2014_);
lean_closure_set(v___f_2015_, 5, v_alpha_1988_);
lean_closure_set(v___f_2015_, 6, v_numDiscrs_1991_);
lean_closure_set(v___f_2015_, 7, v___f_1992_);
lean_closure_set(v___f_2015_, 8, v_a_1993_);
lean_closure_set(v___f_2015_, 9, v_a_1994_);
lean_closure_set(v___f_2015_, 10, v_levelParams_1995_);
lean_closure_set(v___f_2015_, 11, v_matcherName_1996_);
lean_closure_set(v___f_2015_, 12, v___x_1997_);
lean_closure_set(v___f_2015_, 13, v_matcherInfo_1998_);
lean_closure_set(v___f_2015_, 14, v___x_1987_);
lean_closure_set(v___f_2015_, 15, v___x_1999_);
lean_closure_set(v___f_2015_, 16, v_uElimPos_x3f_2000_);
lean_closure_set(v___f_2015_, 17, v___f_2013_);
v___x_2016_ = l_Lean_Expr_forallE___override(v___x_2008_, v_alpha_1988_, v___x_2010_, v___x_2011_);
v___x_2017_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2007_, v___x_2016_, v___f_2015_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed(lean_object** _args){
lean_object* v___x_2018_ = _args[0];
lean_object* v_alpha_2019_ = _args[1];
lean_object* v___x_2020_ = _args[2];
lean_object* v___x_2021_ = _args[3];
lean_object* v_numDiscrs_2022_ = _args[4];
lean_object* v___f_2023_ = _args[5];
lean_object* v_a_2024_ = _args[6];
lean_object* v_a_2025_ = _args[7];
lean_object* v_levelParams_2026_ = _args[8];
lean_object* v_matcherName_2027_ = _args[9];
lean_object* v___x_2028_ = _args[10];
lean_object* v_matcherInfo_2029_ = _args[11];
lean_object* v___x_2030_ = _args[12];
lean_object* v_uElimPos_x3f_2031_ = _args[13];
lean_object* v_beta_2032_ = _args[14];
lean_object* v___y_2033_ = _args[15];
lean_object* v___y_2034_ = _args[16];
lean_object* v___y_2035_ = _args[17];
lean_object* v___y_2036_ = _args[18];
lean_object* v___y_2037_ = _args[19];
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(v___x_2018_, v_alpha_2019_, v___x_2020_, v___x_2021_, v_numDiscrs_2022_, v___f_2023_, v_a_2024_, v_a_2025_, v_levelParams_2026_, v_matcherName_2027_, v___x_2028_, v_matcherInfo_2029_, v___x_2030_, v_uElimPos_x3f_2031_, v_beta_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(lean_object* v___x_2042_, lean_object* v___x_2043_, lean_object* v___x_2044_, lean_object* v_numDiscrs_2045_, lean_object* v___f_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_levelParams_2049_, lean_object* v_matcherName_2050_, lean_object* v___x_2051_, lean_object* v_matcherInfo_2052_, lean_object* v___x_2053_, lean_object* v_uElimPos_x3f_2054_, lean_object* v_alpha_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___f_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_inc(v_a_2047_);
lean_inc_ref(v_alpha_2055_);
v___f_2061_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed), 20, 14);
lean_closure_set(v___f_2061_, 0, v___x_2042_);
lean_closure_set(v___f_2061_, 1, v_alpha_2055_);
lean_closure_set(v___f_2061_, 2, v___x_2043_);
lean_closure_set(v___f_2061_, 3, v___x_2044_);
lean_closure_set(v___f_2061_, 4, v_numDiscrs_2045_);
lean_closure_set(v___f_2061_, 5, v___f_2046_);
lean_closure_set(v___f_2061_, 6, v_a_2047_);
lean_closure_set(v___f_2061_, 7, v_a_2048_);
lean_closure_set(v___f_2061_, 8, v_levelParams_2049_);
lean_closure_set(v___f_2061_, 9, v_matcherName_2050_);
lean_closure_set(v___f_2061_, 10, v___x_2051_);
lean_closure_set(v___f_2061_, 11, v_matcherInfo_2052_);
lean_closure_set(v___f_2061_, 12, v___x_2053_);
lean_closure_set(v___f_2061_, 13, v_uElimPos_x3f_2054_);
v___x_2062_ = l_Lean_Level_param___override(v_a_2047_);
v___x_2063_ = l_Lean_Expr_sort___override(v___x_2062_);
v___x_2064_ = l_Lean_mkArrow(v_alpha_2055_, v___x_2063_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__1));
v___x_2067_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2066_, v_a_2065_, v___f_2061_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
return v___x_2067_;
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v___f_2061_);
v_a_2068_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2064_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2064_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed(lean_object** _args){
lean_object* v___x_2076_ = _args[0];
lean_object* v___x_2077_ = _args[1];
lean_object* v___x_2078_ = _args[2];
lean_object* v_numDiscrs_2079_ = _args[3];
lean_object* v___f_2080_ = _args[4];
lean_object* v_a_2081_ = _args[5];
lean_object* v_a_2082_ = _args[6];
lean_object* v_levelParams_2083_ = _args[7];
lean_object* v_matcherName_2084_ = _args[8];
lean_object* v___x_2085_ = _args[9];
lean_object* v_matcherInfo_2086_ = _args[10];
lean_object* v___x_2087_ = _args[11];
lean_object* v_uElimPos_x3f_2088_ = _args[12];
lean_object* v_alpha_2089_ = _args[13];
lean_object* v___y_2090_ = _args[14];
lean_object* v___y_2091_ = _args[15];
lean_object* v___y_2092_ = _args[16];
lean_object* v___y_2093_ = _args[17];
lean_object* v___y_2094_ = _args[18];
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(v___x_2076_, v___x_2077_, v___x_2078_, v_numDiscrs_2079_, v___f_2080_, v_a_2081_, v_a_2082_, v_levelParams_2083_, v_matcherName_2084_, v___x_2085_, v_matcherInfo_2086_, v___x_2087_, v_uElimPos_x3f_2088_, v_alpha_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(lean_object* v_numParams_2105_, lean_object* v___x_2106_, lean_object* v___x_2107_, lean_object* v_numDiscrs_2108_, lean_object* v___f_2109_, lean_object* v_levelParams_2110_, lean_object* v_matcherName_2111_, lean_object* v_matcherInfo_2112_, lean_object* v___x_2113_, lean_object* v_uElimPos_x3f_2114_, lean_object* v_xs_2115_, lean_object* v_x_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2122_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2105_);
lean_inc_ref(v_xs_2115_);
v___x_2123_ = l_Array_toSubarray___redArg(v_xs_2115_, v___x_2122_, v_numParams_2105_);
v___x_2124_ = lean_array_get(v___x_2106_, v_xs_2115_, v_numParams_2105_);
lean_dec(v_numParams_2105_);
lean_dec_ref(v_xs_2115_);
v___x_2125_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__1));
v___x_2126_ = l_Lean_Core_mkFreshUserName(v___x_2125_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__3));
v___x_2129_ = l_Lean_Core_mkFreshUserName(v___x_2128_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___f_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
lean_inc(v_a_2127_);
v___f_2131_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed), 19, 13);
lean_closure_set(v___f_2131_, 0, v___x_2122_);
lean_closure_set(v___f_2131_, 1, v___x_2124_);
lean_closure_set(v___f_2131_, 2, v___x_2107_);
lean_closure_set(v___f_2131_, 3, v_numDiscrs_2108_);
lean_closure_set(v___f_2131_, 4, v___f_2109_);
lean_closure_set(v___f_2131_, 5, v_a_2130_);
lean_closure_set(v___f_2131_, 6, v_a_2127_);
lean_closure_set(v___f_2131_, 7, v_levelParams_2110_);
lean_closure_set(v___f_2131_, 8, v_matcherName_2111_);
lean_closure_set(v___f_2131_, 9, v___x_2123_);
lean_closure_set(v___f_2131_, 10, v_matcherInfo_2112_);
lean_closure_set(v___f_2131_, 11, v___x_2113_);
lean_closure_set(v___f_2131_, 12, v_uElimPos_x3f_2114_);
v___x_2132_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__5));
v___x_2133_ = l_Lean_Level_param___override(v_a_2127_);
v___x_2134_ = l_Lean_Expr_sort___override(v___x_2133_);
v___x_2135_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2132_, v___x_2134_, v___f_2131_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
return v___x_2135_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_a_2127_);
lean_dec(v___x_2124_);
lean_dec_ref(v___x_2123_);
lean_dec(v_uElimPos_x3f_2114_);
lean_dec(v___x_2113_);
lean_dec_ref(v_matcherInfo_2112_);
lean_dec(v_matcherName_2111_);
lean_dec(v_levelParams_2110_);
lean_dec_ref(v___f_2109_);
lean_dec(v_numDiscrs_2108_);
lean_dec(v___x_2107_);
v_a_2136_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2129_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2129_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v___x_2124_);
lean_dec_ref(v___x_2123_);
lean_dec(v_uElimPos_x3f_2114_);
lean_dec(v___x_2113_);
lean_dec_ref(v_matcherInfo_2112_);
lean_dec(v_matcherName_2111_);
lean_dec(v_levelParams_2110_);
lean_dec_ref(v___f_2109_);
lean_dec(v_numDiscrs_2108_);
lean_dec(v___x_2107_);
v_a_2144_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2126_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2126_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed(lean_object** _args){
lean_object* v_numParams_2152_ = _args[0];
lean_object* v___x_2153_ = _args[1];
lean_object* v___x_2154_ = _args[2];
lean_object* v_numDiscrs_2155_ = _args[3];
lean_object* v___f_2156_ = _args[4];
lean_object* v_levelParams_2157_ = _args[5];
lean_object* v_matcherName_2158_ = _args[6];
lean_object* v_matcherInfo_2159_ = _args[7];
lean_object* v___x_2160_ = _args[8];
lean_object* v_uElimPos_x3f_2161_ = _args[9];
lean_object* v_xs_2162_ = _args[10];
lean_object* v_x_2163_ = _args[11];
lean_object* v___y_2164_ = _args[12];
lean_object* v___y_2165_ = _args[13];
lean_object* v___y_2166_ = _args[14];
lean_object* v___y_2167_ = _args[15];
lean_object* v___y_2168_ = _args[16];
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(v_numParams_2152_, v___x_2153_, v___x_2154_, v_numDiscrs_2155_, v___f_2156_, v_levelParams_2157_, v_matcherName_2158_, v_matcherInfo_2159_, v___x_2160_, v_uElimPos_x3f_2161_, v_xs_2162_, v_x_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec_ref(v_x_2163_);
lean_dec_ref(v___x_2153_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(lean_object* v_ref_2170_, lean_object* v_msg_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_toCold_2177_; lean_object* v_currRecDepth_2178_; lean_object* v_ref_2179_; uint16_t v_optionFlags_2180_; uint8_t v_suppressElabErrors_2181_; uint8_t v_isRecordingDeps_2182_; lean_object* v_ref_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v_toCold_2177_ = lean_ctor_get(v___y_2174_, 0);
v_currRecDepth_2178_ = lean_ctor_get(v___y_2174_, 1);
v_ref_2179_ = lean_ctor_get(v___y_2174_, 2);
v_optionFlags_2180_ = lean_ctor_get_uint16(v___y_2174_, sizeof(void*)*3);
v_suppressElabErrors_2181_ = lean_ctor_get_uint8(v___y_2174_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2182_ = lean_ctor_get_uint8(v___y_2174_, sizeof(void*)*3 + 3);
v_ref_2183_ = l_Lean_replaceRef(v_ref_2170_, v_ref_2179_);
lean_inc(v_currRecDepth_2178_);
lean_inc_ref(v_toCold_2177_);
v___x_2184_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2184_, 0, v_toCold_2177_);
lean_ctor_set(v___x_2184_, 1, v_currRecDepth_2178_);
lean_ctor_set(v___x_2184_, 2, v_ref_2183_);
lean_ctor_set_uint16(v___x_2184_, sizeof(void*)*3, v_optionFlags_2180_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*3 + 2, v_suppressElabErrors_2181_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*3 + 3, v_isRecordingDeps_2182_);
v___x_2185_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_2171_, v___y_2172_, v___y_2173_, v___x_2184_, v___y_2175_);
lean_dec_ref_known(v___x_2184_, 3);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2186_, lean_object* v_msg_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2186_, v_msg_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v_ref_2186_);
return v_res_2193_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2197_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2198_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
lean_ctor_set(v___x_2200_, 2, v___x_2199_);
lean_ctor_set(v___x_2200_, 3, v___x_2199_);
lean_ctor_set(v___x_2200_, 4, v___x_2198_);
lean_ctor_set(v___x_2200_, 5, v___x_2198_);
lean_ctor_set(v___x_2200_, 6, v___x_2198_);
lean_ctor_set(v___x_2200_, 7, v___x_2198_);
lean_ctor_set(v___x_2200_, 8, v___x_2198_);
lean_ctor_set(v___x_2200_, 9, v___x_2198_);
lean_ctor_set(v___x_2200_, 10, v___x_2197_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = lean_unsigned_to_nat(32u);
v___x_2202_ = lean_mk_empty_array_with_capacity(v___x_2201_);
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2204_ = ((size_t)5ULL);
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = lean_unsigned_to_nat(32u);
v___x_2207_ = lean_mk_empty_array_with_capacity(v___x_2206_);
v___x_2208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3);
v___x_2209_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2207_);
lean_ctor_set(v___x_2209_, 2, v___x_2205_);
lean_ctor_set(v___x_2209_, 3, v___x_2205_);
lean_ctor_set_usize(v___x_2209_, 4, v___x_2204_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2210_ = lean_box(1);
v___x_2211_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4);
v___x_2212_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v___x_2211_);
lean_ctor_set(v___x_2213_, 2, v___x_2210_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__6));
v___x_2216_ = l_Lean_stringToMessageData(v___x_2215_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__8));
v___x_2219_ = l_Lean_stringToMessageData(v___x_2218_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__10));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__12));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__14));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16));
v___x_2231_ = l_Lean_stringToMessageData(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18));
v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2235_, lean_object* v_declHint_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v_env_2241_; uint8_t v___x_2242_; 
v___x_2239_ = lean_box(0);
v___x_2240_ = lean_st_ref_get(v___y_2237_);
v_env_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc_ref(v_env_2241_);
lean_dec(v___x_2240_);
v___x_2242_ = l_Lean_Name_isAnonymous(v_declHint_2236_);
if (v___x_2242_ == 0)
{
uint8_t v_isExporting_2243_; 
v_isExporting_2243_ = lean_ctor_get_uint8(v_env_2241_, sizeof(void*)*13);
if (v_isExporting_2243_ == 0)
{
lean_object* v___x_2244_; 
lean_dec_ref(v_env_2241_);
lean_dec(v_declHint_2236_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v_msg_2235_);
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; uint8_t v___x_2246_; 
lean_inc_ref(v_env_2241_);
v___x_2245_ = l_Lean_Environment_setExporting(v_env_2241_, v___x_2242_);
lean_inc(v_declHint_2236_);
lean_inc_ref(v___x_2245_);
v___x_2246_ = l_Lean_Environment_contains(v___x_2245_, v_declHint_2236_, v_isExporting_2243_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; 
lean_dec_ref(v___x_2245_);
lean_dec_ref(v_env_2241_);
lean_dec(v_declHint_2236_);
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_msg_2235_);
return v___x_2247_;
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v_c_2253_; lean_object* v___x_2254_; 
v___x_2248_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2249_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2250_ = l_Lean_Options_empty;
v___x_2251_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2245_);
lean_ctor_set(v___x_2251_, 1, v___x_2248_);
lean_ctor_set(v___x_2251_, 2, v___x_2249_);
lean_ctor_set(v___x_2251_, 3, v___x_2250_);
lean_inc(v_declHint_2236_);
v___x_2252_ = l_Lean_MessageData_ofConstName(v_declHint_2236_, v___x_2242_);
v_c_2253_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2253_, 0, v___x_2251_);
lean_ctor_set(v_c_2253_, 1, v___x_2252_);
v___x_2254_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2241_, v_declHint_2236_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec_ref(v_env_2241_);
lean_dec(v_declHint_2236_);
v___x_2255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set(v___x_2256_, 1, v_c_2253_);
v___x_2257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = l_Lean_MessageData_note(v___x_2258_);
v___x_2260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2260_, 0, v_msg_2235_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
return v___x_2261_;
}
else
{
lean_object* v_val_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2296_; 
v_val_2262_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2264_ = v___x_2254_;
v_isShared_2265_ = v_isSharedCheck_2296_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_val_2262_);
lean_dec(v___x_2254_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2296_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v_moduleNames_2267_; lean_object* v_mod_2268_; uint8_t v___x_2269_; 
v___x_2266_ = l_Lean_Environment_header(v_env_2241_);
lean_dec_ref(v_env_2241_);
v_moduleNames_2267_ = lean_ctor_get(v___x_2266_, 4);
lean_inc_ref(v_moduleNames_2267_);
lean_dec_ref(v___x_2266_);
v_mod_2268_ = lean_array_get(v___x_2239_, v_moduleNames_2267_, v_val_2262_);
lean_dec(v_val_2262_);
lean_dec_ref(v_moduleNames_2267_);
v___x_2269_ = l_Lean_isPrivateName(v_declHint_2236_);
lean_dec(v_declHint_2236_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2270_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
lean_ctor_set(v___x_2271_, 1, v_c_2253_);
v___x_2272_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = l_Lean_MessageData_ofName(v_mod_2268_);
v___x_2275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2273_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = l_Lean_MessageData_note(v___x_2277_);
v___x_2279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2279_, 0, v_msg_2235_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set_tag(v___x_2264_, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2279_);
v___x_2281_ = v___x_2264_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set(v___x_2284_, 1, v_c_2253_);
v___x_2285_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = l_Lean_MessageData_ofName(v_mod_2268_);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = l_Lean_MessageData_note(v___x_2290_);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v_msg_2235_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set_tag(v___x_2264_, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2292_);
v___x_2294_ = v___x_2264_;
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
}
}
}
}
}
else
{
lean_object* v___x_2297_; 
lean_dec_ref(v_env_2241_);
lean_dec(v_declHint_2236_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v_msg_2235_);
return v___x_2297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2298_, lean_object* v_declHint_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2298_, v_declHint_2299_, v___y_2300_);
lean_dec(v___y_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(lean_object* v_msg_2303_, lean_object* v_declHint_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2320_; 
v___x_2310_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2303_, v_declHint_2304_, v___y_2308_);
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2320_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2320_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2315_ = l_Lean_unknownIdentifierMessageTag;
v___x_2316_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v_a_2311_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2316_);
v___x_2318_ = v___x_2313_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11___boxed(lean_object* v_msg_2321_, lean_object* v_declHint_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2321_, v_declHint_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_ref_2329_, lean_object* v_msg_2330_, lean_object* v_declHint_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; lean_object* v_a_2338_; lean_object* v___x_2339_; 
v___x_2337_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2330_, v_declHint_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2337_);
v___x_2339_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2329_, v_a_2338_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_ref_2340_, lean_object* v_msg_2341_, lean_object* v_declHint_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2340_, v_msg_2341_, v_declHint_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v_ref_2340_);
return v_res_2348_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_2351_ = l_Lean_stringToMessageData(v___x_2350_);
return v___x_2351_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_2354_ = l_Lean_stringToMessageData(v___x_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_2355_, lean_object* v_constName_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; uint8_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2362_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_2363_ = 0;
lean_inc(v_constName_2356_);
v___x_2364_ = l_Lean_MessageData_ofConstName(v_constName_2356_, v___x_2363_);
v___x_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2362_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2355_, v___x_2367_, v_constName_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_2369_, lean_object* v_constName_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2369_, v_constName_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v_ref_2369_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(lean_object* v_constName_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_ref_2383_; lean_object* v___x_2384_; 
v_ref_2383_ = lean_ctor_get(v___y_2380_, 2);
v___x_2384_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2383_, v_constName_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(lean_object* v_constName_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; lean_object* v_env_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; 
v___x_2398_ = lean_st_ref_get(v___y_2396_);
v_env_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc_ref(v_env_2399_);
lean_dec(v___x_2398_);
v___x_2400_ = 0;
lean_inc(v_constName_2392_);
v___x_2401_ = l_Lean_Environment_findConstVal_x3f(v_env_2399_, v_constName_2392_, v___x_2400_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2402_;
}
else
{
lean_object* v_val_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v_constName_2392_);
v_val_2403_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2401_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_val_2403_);
lean_dec(v___x_2401_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set_tag(v___x_2405_, 0);
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_val_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0___boxed(lean_object* v_constName_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_constName_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(lean_object* v_matcherName_2418_, lean_object* v_matcherInfo_2419_, lean_object* v___x_2420_, lean_object* v___f_2421_, lean_object* v___x_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; 
lean_inc(v_matcherName_2418_);
v___x_2428_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_matcherName_2418_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v_levelParams_2430_; lean_object* v_type_2431_; lean_object* v_numParams_2432_; lean_object* v_numDiscrs_2433_; lean_object* v_uElimPos_x3f_2434_; lean_object* v___x_2435_; lean_object* v___f_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2428_, 1);
v_levelParams_2430_ = lean_ctor_get(v_a_2429_, 1);
lean_inc(v_levelParams_2430_);
v_type_2431_ = lean_ctor_get(v_a_2429_, 2);
lean_inc_ref(v_type_2431_);
lean_dec(v_a_2429_);
v_numParams_2432_ = lean_ctor_get(v_matcherInfo_2419_, 0);
lean_inc_n(v_numParams_2432_, 2);
v_numDiscrs_2433_ = lean_ctor_get(v_matcherInfo_2419_, 1);
lean_inc(v_numDiscrs_2433_);
v_uElimPos_x3f_2434_ = lean_ctor_get(v_matcherInfo_2419_, 3);
lean_inc(v_uElimPos_x3f_2434_);
v___x_2435_ = lean_unsigned_to_nat(1u);
v___f_2436_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed), 17, 10);
lean_closure_set(v___f_2436_, 0, v_numParams_2432_);
lean_closure_set(v___f_2436_, 1, v___x_2420_);
lean_closure_set(v___f_2436_, 2, v___x_2435_);
lean_closure_set(v___f_2436_, 3, v_numDiscrs_2433_);
lean_closure_set(v___f_2436_, 4, v___f_2421_);
lean_closure_set(v___f_2436_, 5, v_levelParams_2430_);
lean_closure_set(v___f_2436_, 6, v_matcherName_2418_);
lean_closure_set(v___f_2436_, 7, v_matcherInfo_2419_);
lean_closure_set(v___f_2436_, 8, v___x_2422_);
lean_closure_set(v___f_2436_, 9, v_uElimPos_x3f_2434_);
v___x_2437_ = lean_nat_add(v_numParams_2432_, v___x_2435_);
lean_dec(v_numParams_2432_);
v___x_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
v___x_2439_ = 0;
v___x_2440_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_2431_, v___x_2438_, v___f_2436_, v___x_2439_, v___x_2439_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v___x_2440_;
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec(v___x_2422_);
lean_dec_ref(v___f_2421_);
lean_dec_ref(v___x_2420_);
lean_dec_ref(v_matcherInfo_2419_);
lean_dec(v_matcherName_2418_);
v_a_2441_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2428_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2428_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed(lean_object* v_matcherName_2449_, lean_object* v_matcherInfo_2450_, lean_object* v___x_2451_, lean_object* v___f_2452_, lean_object* v___x_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(v_matcherName_2449_, v_matcherInfo_2450_, v___x_2451_, v___f_2452_, v___x_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11(lean_object* v___x_2460_, lean_object* v_e_2461_){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = l_Lean_indentD(v_e_2461_);
v___x_2463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2460_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(lean_object* v___f_2464_, lean_object* v___f_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2464_, v___f_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
v_a_2480_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2471_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2471_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed(lean_object* v___f_2488_, lean_object* v___f_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(v___f_2488_, v___f_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
return v_res_2495_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__3));
v___x_2502_ = l_Lean_stringToMessageData(v___x_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(lean_object* v_matcherName_2503_, lean_object* v_matcherInfo_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v___f_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v_env_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___f_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___f_2521_; lean_object* v___f_2522_; lean_object* v___x_2523_; 
v___f_2510_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__0));
v___x_2511_ = l_Lean_instInhabitedExpr;
v___x_2512_ = lean_st_ref_get(v_a_2508_);
v_env_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc_ref(v_env_2513_);
lean_dec(v___x_2512_);
lean_inc_n(v_matcherName_2503_, 3);
v___x_2514_ = l_Lean_mkPrivateName(v_env_2513_, v_matcherName_2503_);
lean_dec_ref(v_env_2513_);
v___x_2515_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__2));
v___x_2516_ = l_Lean_Name_append(v___x_2514_, v___x_2515_);
lean_inc_n(v___x_2516_, 2);
v___f_2517_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed), 10, 5);
lean_closure_set(v___f_2517_, 0, v_matcherName_2503_);
lean_closure_set(v___f_2517_, 1, v_matcherInfo_2504_);
lean_closure_set(v___f_2517_, 2, v___x_2511_);
lean_closure_set(v___f_2517_, 3, v___f_2510_);
lean_closure_set(v___f_2517_, 4, v___x_2516_);
v___x_2518_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4);
v___x_2519_ = l_Lean_MessageData_ofName(v_matcherName_2503_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___f_2521_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_2521_, 0, v___x_2520_);
v___f_2522_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed), 7, 2);
lean_closure_set(v___f_2522_, 0, v___f_2517_);
lean_closure_set(v___f_2522_, 1, v___f_2521_);
v___x_2523_ = l_Lean_Meta_realizeConst(v_matcherName_2503_, v___x_2516_, v___f_2522_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v___x_2523_, 0);
lean_dec(v_unused_2531_);
v___x_2525_ = v___x_2523_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_dec(v___x_2523_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2516_);
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2516_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec(v___x_2516_);
v_a_2532_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2523_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2523_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___boxed(lean_object* v_matcherName_2540_, lean_object* v_matcherInfo_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_2540_, v_matcherInfo_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(lean_object* v_as_2548_, lean_object* v_as_x27_2549_, lean_object* v_b_2550_, lean_object* v_a_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_2549_, v_b_2550_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___boxed(lean_object* v_as_2558_, lean_object* v_as_x27_2559_, lean_object* v_b_2560_, lean_object* v_a_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(v_as_2558_, v_as_x27_2559_, v_b_2560_, v_a_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v_as_x27_2559_);
lean_dec(v_as_2558_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(lean_object* v_00_u03b1_2568_, lean_object* v_name_2569_, uint8_t v_bi_2570_, lean_object* v_type_2571_, lean_object* v_k_2572_, uint8_t v_kind_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_2569_, v_bi_2570_, v_type_2571_, v_k_2572_, v_kind_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2580_, lean_object* v_name_2581_, lean_object* v_bi_2582_, lean_object* v_type_2583_, lean_object* v_k_2584_, lean_object* v_kind_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
uint8_t v_bi_boxed_2591_; uint8_t v_kind_boxed_2592_; lean_object* v_res_2593_; 
v_bi_boxed_2591_ = lean_unbox(v_bi_2582_);
v_kind_boxed_2592_ = lean_unbox(v_kind_2585_);
v_res_2593_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(v_00_u03b1_2580_, v_name_2581_, v_bi_boxed_2591_, v_type_2583_, v_k_2584_, v_kind_boxed_2592_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(lean_object* v_00_u03b1_2594_, lean_object* v_name_2595_, lean_object* v_type_2596_, lean_object* v_k_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_2595_, v_type_2596_, v_k_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___boxed(lean_object* v_00_u03b1_2604_, lean_object* v_name_2605_, lean_object* v_type_2606_, lean_object* v_k_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(v_00_u03b1_2604_, v_name_2605_, v_type_2606_, v_k_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(lean_object* v_00_u03b1_2614_, lean_object* v_constName_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2622_, lean_object* v_constName_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(v_00_u03b1_2622_, v_constName_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2630_, lean_object* v_ref_2631_, lean_object* v_constName_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2631_, v_constName_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2639_, lean_object* v_ref_2640_, lean_object* v_constName_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(v_00_u03b1_2639_, v_ref_2640_, v_constName_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v_ref_2640_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b1_2648_, lean_object* v_ref_2649_, lean_object* v_msg_2650_, lean_object* v_declHint_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2649_, v_msg_2650_, v_declHint_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b1_2658_, lean_object* v_ref_2659_, lean_object* v_msg_2660_, lean_object* v_declHint_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(v_00_u03b1_2658_, v_ref_2659_, v_msg_2660_, v_declHint_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v_ref_2659_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(lean_object* v_msg_2668_, lean_object* v_declHint_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2668_, v_declHint_2669_, v___y_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_2676_, lean_object* v_declHint_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(v_msg_2676_, v_declHint_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_2684_, lean_object* v_ref_2685_, lean_object* v_msg_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2685_, v_msg_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_2693_, lean_object* v_ref_2694_, lean_object* v_msg_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(v_00_u03b1_2693_, v_ref_2694_, v_msg_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v_ref_2694_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(lean_object* v_msg_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___f_2712_; lean_object* v___x_34395__overap_2713_; lean_object* v___x_2714_; 
v___f_2712_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0));
v___x_34395__overap_2713_ = lean_panic_fn_borrowed(v___f_2712_, v_msg_2703_);
lean_inc(v___y_2710_);
lean_inc_ref(v___y_2709_);
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v___y_2704_);
v___x_2714_ = lean_apply_8(v___x_34395__overap_2713_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, lean_box(0));
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___boxed(lean_object* v_msg_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v_msg_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(lean_object* v_k_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v_b_2729_, lean_object* v_c_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v___x_2736_; 
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2728_);
lean_inc_ref(v___y_2727_);
lean_inc(v___y_2726_);
v___x_2736_ = lean_apply_10(v_k_2725_, v_b_2729_, v_c_2730_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed(lean_object* v_k_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v_b_2741_, lean_object* v_c_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(v_k_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v_b_2741_, v_c_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(lean_object* v_e_2749_, lean_object* v_k_2750_, uint8_t v_cleanupAnnotations_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___f_2760_; uint8_t v___x_2761_; uint8_t v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_inc(v___y_2754_);
lean_inc_ref(v___y_2753_);
lean_inc(v___y_2752_);
v___f_2760_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2760_, 0, v_k_2750_);
lean_closure_set(v___f_2760_, 1, v___y_2752_);
lean_closure_set(v___f_2760_, 2, v___y_2753_);
lean_closure_set(v___f_2760_, 3, v___y_2754_);
v___x_2761_ = 1;
v___x_2762_ = 0;
v___x_2763_ = lean_box(0);
v___x_2764_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2749_, v___x_2761_, v___x_2762_, v___x_2761_, v___x_2762_, v___x_2763_, v___f_2760_, v_cleanupAnnotations_2751_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2764_) == 0)
{
return v___x_2764_;
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___boxed(lean_object* v_e_2773_, lean_object* v_k_2774_, lean_object* v_cleanupAnnotations_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2784_; lean_object* v_res_2785_; 
v_cleanupAnnotations_boxed_2784_ = lean_unbox(v_cleanupAnnotations_2775_);
v_res_2785_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2773_, v_k_2774_, v_cleanupAnnotations_boxed_2784_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(lean_object* v_00_u03b1_2786_, lean_object* v_e_2787_, lean_object* v_k_2788_, uint8_t v_cleanupAnnotations_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2787_, v_k_2788_, v_cleanupAnnotations_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___boxed(lean_object* v_00_u03b1_2799_, lean_object* v_e_2800_, lean_object* v_k_2801_, lean_object* v_cleanupAnnotations_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2811_; lean_object* v_res_2812_; 
v_cleanupAnnotations_boxed_2811_ = lean_unbox(v_cleanupAnnotations_2802_);
v_res_2812_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(v_00_u03b1_2799_, v_e_2800_, v_k_2801_, v_cleanupAnnotations_boxed_2811_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(uint8_t v___x_2813_, uint8_t v___x_2814_, uint8_t v___x_2815_, lean_object* v_xs_2816_, lean_object* v_motiveBody_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; 
v___x_2826_ = l_Lean_Expr_bindingDomain_x21(v_motiveBody_2817_);
v___x_2827_ = l_Lean_Expr_bindingName_x21(v___x_2826_);
v___x_2828_ = l_Lean_Expr_bindingDomain_x21(v___x_2826_);
v___x_2829_ = l_Lean_Expr_bindingBody_x21(v___x_2826_);
lean_dec_ref(v___x_2826_);
v___x_2830_ = l_Lean_Expr_bindingDomain_x21(v___x_2829_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = l_Lean_Expr_lam___override(v___x_2827_, v___x_2828_, v___x_2830_, v___x_2813_);
v___x_2832_ = 1;
v___x_2833_ = l_Lean_Meta_mkLambdaFVars(v_xs_2816_, v___x_2831_, v___x_2814_, v___x_2815_, v___x_2814_, v___x_2815_, v___x_2832_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed(lean_object* v___x_2834_, lean_object* v___x_2835_, lean_object* v___x_2836_, lean_object* v_xs_2837_, lean_object* v_motiveBody_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
uint8_t v___x_41781__boxed_2847_; uint8_t v___x_41782__boxed_2848_; uint8_t v___x_41783__boxed_2849_; lean_object* v_res_2850_; 
v___x_41781__boxed_2847_ = lean_unbox(v___x_2834_);
v___x_41782__boxed_2848_ = lean_unbox(v___x_2835_);
v___x_41783__boxed_2849_ = lean_unbox(v___x_2836_);
v_res_2850_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(v___x_41781__boxed_2847_, v___x_41782__boxed_2848_, v___x_41783__boxed_2849_, v_xs_2837_, v_motiveBody_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v_motiveBody_2838_);
lean_dec_ref(v_xs_2837_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(size_t v_sz_2851_, size_t v_i_2852_, lean_object* v_bs_2853_){
_start:
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_usize_dec_lt(v_i_2852_, v_sz_2851_);
if (v___x_2854_ == 0)
{
return v_bs_2853_;
}
else
{
lean_object* v_v_2855_; lean_object* v___x_2856_; lean_object* v_bs_x27_2857_; lean_object* v___x_2858_; size_t v___x_2859_; size_t v___x_2860_; lean_object* v___x_2861_; 
v_v_2855_ = lean_array_uget(v_bs_2853_, v_i_2852_);
v___x_2856_ = lean_unsigned_to_nat(0u);
v_bs_x27_2857_ = lean_array_uset(v_bs_2853_, v_i_2852_, v___x_2856_);
v___x_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2858_, 0, v_v_2855_);
v___x_2859_ = ((size_t)1ULL);
v___x_2860_ = lean_usize_add(v_i_2852_, v___x_2859_);
v___x_2861_ = lean_array_uset(v_bs_x27_2857_, v_i_2852_, v___x_2858_);
v_i_2852_ = v___x_2860_;
v_bs_2853_ = v___x_2861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4___boxed(lean_object* v_sz_2863_, lean_object* v_i_2864_, lean_object* v_bs_2865_){
_start:
{
size_t v_sz_boxed_2866_; size_t v_i_boxed_2867_; lean_object* v_res_2868_; 
v_sz_boxed_2866_ = lean_unbox_usize(v_sz_2863_);
lean_dec(v_sz_2863_);
v_i_boxed_2867_ = lean_unbox_usize(v_i_2864_);
lean_dec(v_i_2864_);
v_res_2868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_boxed_2866_, v_i_boxed_2867_, v_bs_2865_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(lean_object* v_msg_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_ref_2875_; lean_object* v___x_2876_; lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2885_; 
v_ref_2875_ = lean_ctor_get(v___y_2872_, 2);
v___x_2876_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2885_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2885_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
lean_inc(v_ref_2875_);
v___x_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2881_, 0, v_ref_2875_);
lean_ctor_set(v___x_2881_, 1, v_a_2877_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set_tag(v___x_2879_, 1);
lean_ctor_set(v___x_2879_, 0, v___x_2881_);
v___x_2883_ = v___x_2879_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg___boxed(lean_object* v_msg_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(lean_object* v_declName_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; lean_object* v_env_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2896_ = lean_st_ref_get(v___y_2894_);
v_env_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc_ref(v_env_2897_);
lean_dec(v___x_2896_);
v___x_2898_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2897_, v_declName_2893_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg___boxed(lean_object* v_declName_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_2900_, v___y_2901_);
lean_dec(v___y_2901_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(lean_object* v_ref_2904_, lean_object* v_msg_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_toCold_2914_; lean_object* v_currRecDepth_2915_; lean_object* v_ref_2916_; uint16_t v_optionFlags_2917_; uint8_t v_suppressElabErrors_2918_; uint8_t v_isRecordingDeps_2919_; lean_object* v_ref_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v_toCold_2914_ = lean_ctor_get(v___y_2911_, 0);
v_currRecDepth_2915_ = lean_ctor_get(v___y_2911_, 1);
v_ref_2916_ = lean_ctor_get(v___y_2911_, 2);
v_optionFlags_2917_ = lean_ctor_get_uint16(v___y_2911_, sizeof(void*)*3);
v_suppressElabErrors_2918_ = lean_ctor_get_uint8(v___y_2911_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2919_ = lean_ctor_get_uint8(v___y_2911_, sizeof(void*)*3 + 3);
v_ref_2920_ = l_Lean_replaceRef(v_ref_2904_, v_ref_2916_);
lean_inc(v_currRecDepth_2915_);
lean_inc_ref(v_toCold_2914_);
v___x_2921_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2921_, 0, v_toCold_2914_);
lean_ctor_set(v___x_2921_, 1, v_currRecDepth_2915_);
lean_ctor_set(v___x_2921_, 2, v_ref_2920_);
lean_ctor_set_uint16(v___x_2921_, sizeof(void*)*3, v_optionFlags_2917_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*3 + 2, v_suppressElabErrors_2918_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*3 + 3, v_isRecordingDeps_2919_);
v___x_2922_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2905_, v___y_2909_, v___y_2910_, v___x_2921_, v___y_2912_);
lean_dec_ref_known(v___x_2921_, 3);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2923_, lean_object* v_msg_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_2923_, v_msg_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec(v_ref_2923_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2934_, lean_object* v_declHint_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v_env_2940_; uint8_t v___x_2941_; 
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_st_ref_get(v___y_2936_);
v_env_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc_ref(v_env_2940_);
lean_dec(v___x_2939_);
v___x_2941_ = l_Lean_Name_isAnonymous(v_declHint_2935_);
if (v___x_2941_ == 0)
{
uint8_t v_isExporting_2942_; 
v_isExporting_2942_ = lean_ctor_get_uint8(v_env_2940_, sizeof(void*)*13);
if (v_isExporting_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_dec_ref(v_env_2940_);
lean_dec(v_declHint_2935_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_msg_2934_);
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
lean_inc_ref(v_env_2940_);
v___x_2944_ = l_Lean_Environment_setExporting(v_env_2940_, v___x_2941_);
lean_inc(v_declHint_2935_);
lean_inc_ref(v___x_2944_);
v___x_2945_ = l_Lean_Environment_contains(v___x_2944_, v_declHint_2935_, v_isExporting_2942_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; 
lean_dec_ref(v___x_2944_);
lean_dec_ref(v_env_2940_);
lean_dec(v_declHint_2935_);
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v_msg_2934_);
return v___x_2946_;
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v_c_2954_; lean_object* v___x_2955_; 
v___x_2947_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2948_ = lean_unsigned_to_nat(32u);
v___x_2949_ = lean_mk_empty_array_with_capacity(v___x_2948_);
lean_dec_ref(v___x_2949_);
v___x_2950_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2951_ = l_Lean_Options_empty;
v___x_2952_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2944_);
lean_ctor_set(v___x_2952_, 1, v___x_2947_);
lean_ctor_set(v___x_2952_, 2, v___x_2950_);
lean_ctor_set(v___x_2952_, 3, v___x_2951_);
lean_inc(v_declHint_2935_);
v___x_2953_ = l_Lean_MessageData_ofConstName(v_declHint_2935_, v___x_2941_);
v_c_2954_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2954_, 0, v___x_2952_);
lean_ctor_set(v_c_2954_, 1, v___x_2953_);
v___x_2955_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2940_, v_declHint_2935_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
lean_dec_ref(v_env_2940_);
lean_dec(v_declHint_2935_);
v___x_2956_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
lean_ctor_set(v___x_2957_, 1, v_c_2954_);
v___x_2958_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = l_Lean_MessageData_note(v___x_2959_);
v___x_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2961_, 0, v_msg_2934_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
else
{
lean_object* v_val_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2997_; 
v_val_2963_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2965_ = v___x_2955_;
v_isShared_2966_ = v_isSharedCheck_2997_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_val_2963_);
lean_dec(v___x_2955_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2997_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v_moduleNames_2968_; lean_object* v_mod_2969_; uint8_t v___x_2970_; 
v___x_2967_ = l_Lean_Environment_header(v_env_2940_);
lean_dec_ref(v_env_2940_);
v_moduleNames_2968_ = lean_ctor_get(v___x_2967_, 4);
lean_inc_ref(v_moduleNames_2968_);
lean_dec_ref(v___x_2967_);
v_mod_2969_ = lean_array_get(v___x_2938_, v_moduleNames_2968_, v_val_2963_);
lean_dec(v_val_2963_);
lean_dec_ref(v_moduleNames_2968_);
v___x_2970_ = l_Lean_isPrivateName(v_declHint_2935_);
lean_dec(v_declHint_2935_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2971_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
lean_ctor_set(v___x_2972_, 1, v_c_2954_);
v___x_2973_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = l_Lean_MessageData_ofName(v_mod_2969_);
v___x_2976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2974_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2976_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = l_Lean_MessageData_note(v___x_2978_);
v___x_2980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2980_, 0, v_msg_2934_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set_tag(v___x_2965_, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2980_);
v___x_2982_ = v___x_2965_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2984_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
lean_ctor_set(v___x_2985_, 1, v_c_2954_);
v___x_2986_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_2987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = l_Lean_MessageData_ofName(v_mod_2969_);
v___x_2989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2987_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_2991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2989_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
v___x_2992_ = l_Lean_MessageData_note(v___x_2991_);
v___x_2993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2993_, 0, v_msg_2934_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set_tag(v___x_2965_, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2993_);
v___x_2995_ = v___x_2965_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2993_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2998_; 
lean_dec_ref(v_env_2940_);
lean_dec(v_declHint_2935_);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_msg_2934_);
return v___x_2998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2999_, lean_object* v_declHint_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_2999_, v_declHint_3000_, v___y_3001_);
lean_dec(v___y_3001_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(lean_object* v_msg_3004_, lean_object* v_declHint_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v___x_3014_; lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3024_; 
v___x_3014_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3004_, v_declHint_3005_, v___y_3012_);
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3017_ = v___x_3014_;
v_isShared_3018_ = v_isSharedCheck_3024_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3024_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3022_; 
v___x_3019_ = l_Lean_unknownIdentifierMessageTag;
v___x_3020_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v_a_3015_);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3020_);
v___x_3022_ = v___x_3017_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11___boxed(lean_object* v_msg_3025_, lean_object* v_declHint_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3025_, v_declHint_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object* v_ref_3036_, lean_object* v_msg_3037_, lean_object* v_declHint_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v___x_3047_; lean_object* v_a_3048_; lean_object* v___x_3049_; 
v___x_3047_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3037_, v_declHint_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3036_, v_a_3048_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_ref_3050_, lean_object* v_msg_3051_, lean_object* v_declHint_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3050_, v_msg_3051_, v_declHint_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec(v_ref_3050_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(lean_object* v_ref_3062_, lean_object* v_constName_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; uint8_t v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3072_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3073_ = 0;
lean_inc(v_constName_3063_);
v___x_3074_ = l_Lean_MessageData_ofConstName(v_constName_3063_, v___x_3073_);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3072_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3062_, v___x_3077_, v_constName_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_ref_3079_, lean_object* v_constName_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3079_, v_constName_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec(v_ref_3079_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_ref_3099_; lean_object* v___x_3100_; 
v_ref_3099_ = lean_ctor_get(v___y_3096_, 2);
v___x_3100_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3099_, v_constName_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(lean_object* v_constName_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v___x_3120_; lean_object* v_env_3121_; uint8_t v___x_3122_; lean_object* v___x_3123_; 
v___x_3120_ = lean_st_ref_get(v___y_3118_);
v_env_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc_ref(v_env_3121_);
lean_dec(v___x_3120_);
v___x_3122_ = 0;
lean_inc(v_constName_3111_);
v___x_3123_ = l_Lean_Environment_find_x3f(v_env_3121_, v_constName_3111_, v___x_3122_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
return v___x_3124_;
}
else
{
lean_object* v_val_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec(v_constName_3111_);
v_val_3125_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3123_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_val_3125_);
lean_dec(v___x_3123_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
lean_ctor_set_tag(v___x_3127_, 0);
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_val_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0___boxed(lean_object* v_constName_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_constName_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
return v_res_3142_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l_instMonadEIO___redArg();
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(lean_object* v_msg_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v_toApplicative_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3223_; 
v___x_3157_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0);
v___x_3158_ = l_StateRefT_x27_instMonad___redArg(v___x_3157_);
v_toApplicative_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3223_ == 0)
{
lean_object* v_unused_3224_; 
v_unused_3224_ = lean_ctor_get(v___x_3158_, 1);
lean_dec(v_unused_3224_);
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3223_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_toApplicative_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3223_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v_toFunctor_3163_; lean_object* v_toSeq_3164_; lean_object* v_toSeqLeft_3165_; lean_object* v_toSeqRight_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3221_; 
v_toFunctor_3163_ = lean_ctor_get(v_toApplicative_3159_, 0);
v_toSeq_3164_ = lean_ctor_get(v_toApplicative_3159_, 2);
v_toSeqLeft_3165_ = lean_ctor_get(v_toApplicative_3159_, 3);
v_toSeqRight_3166_ = lean_ctor_get(v_toApplicative_3159_, 4);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_toApplicative_3159_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v_toApplicative_3159_, 1);
lean_dec(v_unused_3222_);
v___x_3168_ = v_toApplicative_3159_;
v_isShared_3169_ = v_isSharedCheck_3221_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_toSeqRight_3166_);
lean_inc(v_toSeqLeft_3165_);
lean_inc(v_toSeq_3164_);
lean_inc(v_toFunctor_3163_);
lean_dec(v_toApplicative_3159_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3221_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___f_3170_; lean_object* v___f_3171_; lean_object* v___f_3172_; lean_object* v___f_3173_; lean_object* v___x_3174_; lean_object* v___f_3175_; lean_object* v___f_3176_; lean_object* v___f_3177_; lean_object* v___x_3179_; 
v___f_3170_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__1));
v___f_3171_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3163_);
v___f_3172_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3172_, 0, v_toFunctor_3163_);
v___f_3173_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3173_, 0, v_toFunctor_3163_);
v___x_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___f_3172_);
lean_ctor_set(v___x_3174_, 1, v___f_3173_);
v___f_3175_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3175_, 0, v_toSeqRight_3166_);
v___f_3176_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3176_, 0, v_toSeqLeft_3165_);
v___f_3177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3177_, 0, v_toSeq_3164_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 4, v___f_3175_);
lean_ctor_set(v___x_3168_, 3, v___f_3176_);
lean_ctor_set(v___x_3168_, 2, v___f_3177_);
lean_ctor_set(v___x_3168_, 1, v___f_3170_);
lean_ctor_set(v___x_3168_, 0, v___x_3174_);
v___x_3179_ = v___x_3168_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v___f_3170_);
lean_ctor_set(v_reuseFailAlloc_3220_, 2, v___f_3177_);
lean_ctor_set(v_reuseFailAlloc_3220_, 3, v___f_3176_);
lean_ctor_set(v_reuseFailAlloc_3220_, 4, v___f_3175_);
v___x_3179_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3181_; 
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 1, v___f_3171_);
lean_ctor_set(v___x_3161_, 0, v___x_3179_);
v___x_3181_ = v___x_3161_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v___f_3171_);
v___x_3181_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3182_; lean_object* v_toApplicative_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3217_; 
v___x_3182_ = l_StateRefT_x27_instMonad___redArg(v___x_3181_);
v_toApplicative_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v___x_3182_, 1);
lean_dec(v_unused_3218_);
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3217_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_toApplicative_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3217_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_toFunctor_3187_; lean_object* v_toSeq_3188_; lean_object* v_toSeqLeft_3189_; lean_object* v_toSeqRight_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3215_; 
v_toFunctor_3187_ = lean_ctor_get(v_toApplicative_3183_, 0);
v_toSeq_3188_ = lean_ctor_get(v_toApplicative_3183_, 2);
v_toSeqLeft_3189_ = lean_ctor_get(v_toApplicative_3183_, 3);
v_toSeqRight_3190_ = lean_ctor_get(v_toApplicative_3183_, 4);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_toApplicative_3183_);
if (v_isSharedCheck_3215_ == 0)
{
lean_object* v_unused_3216_; 
v_unused_3216_ = lean_ctor_get(v_toApplicative_3183_, 1);
lean_dec(v_unused_3216_);
v___x_3192_ = v_toApplicative_3183_;
v_isShared_3193_ = v_isSharedCheck_3215_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_toSeqRight_3190_);
lean_inc(v_toSeqLeft_3189_);
lean_inc(v_toSeq_3188_);
lean_inc(v_toFunctor_3187_);
lean_dec(v_toApplicative_3183_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3215_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___f_3194_; lean_object* v___f_3195_; lean_object* v___f_3196_; lean_object* v___f_3197_; lean_object* v___x_3198_; lean_object* v___f_3199_; lean_object* v___f_3200_; lean_object* v___f_3201_; lean_object* v___x_3203_; 
v___f_3194_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__3));
v___f_3195_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3187_);
v___f_3196_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3196_, 0, v_toFunctor_3187_);
v___f_3197_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3197_, 0, v_toFunctor_3187_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___f_3196_);
lean_ctor_set(v___x_3198_, 1, v___f_3197_);
v___f_3199_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3199_, 0, v_toSeqRight_3190_);
v___f_3200_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3200_, 0, v_toSeqLeft_3189_);
v___f_3201_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3201_, 0, v_toSeq_3188_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 4, v___f_3199_);
lean_ctor_set(v___x_3192_, 3, v___f_3200_);
lean_ctor_set(v___x_3192_, 2, v___f_3201_);
lean_ctor_set(v___x_3192_, 1, v___f_3194_);
lean_ctor_set(v___x_3192_, 0, v___x_3198_);
v___x_3203_ = v___x_3192_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v___f_3194_);
lean_ctor_set(v_reuseFailAlloc_3214_, 2, v___f_3201_);
lean_ctor_set(v_reuseFailAlloc_3214_, 3, v___f_3200_);
lean_ctor_set(v_reuseFailAlloc_3214_, 4, v___f_3199_);
v___x_3203_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3205_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 1, v___f_3195_);
lean_ctor_set(v___x_3185_, 0, v___x_3203_);
v___x_3205_ = v___x_3185_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v___f_3195_);
v___x_3205_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_36468__overap_3211_; lean_object* v___x_3212_; 
v___x_3206_ = l_StateRefT_x27_instMonad___redArg(v___x_3205_);
v___x_3207_ = l_ReaderT_instMonad___redArg(v___x_3206_);
v___x_3208_ = l_ReaderT_instMonad___redArg(v___x_3207_);
v___x_3209_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3210_ = l_instInhabitedOfMonad___redArg(v___x_3208_, v___x_3209_);
v___x_36468__overap_3211_ = lean_panic_fn_borrowed(v___x_3210_, v_msg_3148_);
lean_dec(v___x_3210_);
lean_inc(v___y_3155_);
lean_inc_ref(v___y_3154_);
lean_inc(v___y_3153_);
lean_inc_ref(v___y_3152_);
lean_inc(v___y_3151_);
lean_inc_ref(v___y_3150_);
lean_inc(v___y_3149_);
v___x_3212_ = lean_apply_8(v___x_36468__overap_3211_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, lean_box(0));
return v___x_3212_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___boxed(lean_object* v_msg_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v_msg_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
return v_res_3234_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__2));
v___x_3239_ = lean_unsigned_to_nat(53u);
v___x_3240_ = lean_unsigned_to_nat(62u);
v___x_3241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__1));
v___x_3242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__0));
v___x_3243_ = l_mkPanicMessageWithDecl(v___x_3242_, v___x_3241_, v___x_3240_, v___x_3239_, v___x_3238_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(size_t v_sz_3244_, size_t v_i_3245_, lean_object* v_bs_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
uint8_t v___x_3255_; 
v___x_3255_ = lean_usize_dec_lt(v_i_3245_, v_sz_3244_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3256_, 0, v_bs_3246_);
return v___x_3256_;
}
else
{
lean_object* v_v_3257_; lean_object* v___x_3258_; lean_object* v_bs_x27_3259_; lean_object* v_a_3261_; lean_object* v___x_3266_; 
v_v_3257_ = lean_array_uget(v_bs_3246_, v_i_3245_);
v___x_3258_ = lean_unsigned_to_nat(0u);
v_bs_x27_3259_ = lean_array_uset(v_bs_3246_, v_i_3245_, v___x_3258_);
v___x_3266_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_v_3257_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3266_, 1);
if (lean_obj_tag(v_a_3267_) == 6)
{
lean_object* v_val_3268_; lean_object* v_numFields_3269_; uint8_t v___x_3270_; lean_object* v___x_3271_; 
v_val_3268_ = lean_ctor_get(v_a_3267_, 0);
lean_inc_ref(v_val_3268_);
lean_dec_ref_known(v_a_3267_, 1);
v_numFields_3269_ = lean_ctor_get(v_val_3268_, 4);
lean_inc(v_numFields_3269_);
lean_dec_ref(v_val_3268_);
v___x_3270_ = 0;
v___x_3271_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3271_, 0, v_numFields_3269_);
lean_ctor_set(v___x_3271_, 1, v___x_3258_);
lean_ctor_set_uint8(v___x_3271_, sizeof(void*)*2, v___x_3270_);
v_a_3261_ = v___x_3271_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_dec(v_a_3267_);
v___x_3272_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3);
v___x_3273_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v___x_3272_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
v_a_3261_ = v_a_3274_;
goto v___jp_3260_;
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec_ref(v_bs_x27_3259_);
v_a_3275_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3273_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3273_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec_ref(v_bs_x27_3259_);
v_a_3283_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3266_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3266_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
v___jp_3260_:
{
size_t v___x_3262_; size_t v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = ((size_t)1ULL);
v___x_3263_ = lean_usize_add(v_i_3245_, v___x_3262_);
v___x_3264_ = lean_array_uset(v_bs_x27_3259_, v_i_3245_, v_a_3261_);
v_i_3245_ = v___x_3263_;
v_bs_3246_ = v___x_3264_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___boxed(lean_object* v_sz_3291_, lean_object* v_i_3292_, lean_object* v_bs_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
size_t v_sz_boxed_3302_; size_t v_i_boxed_3303_; lean_object* v_res_3304_; 
v_sz_boxed_3302_ = lean_unbox_usize(v_sz_3291_);
lean_dec(v_sz_3291_);
v_i_boxed_3303_ = lean_unbox_usize(v_i_3292_);
lean_dec(v_i_3292_);
v_res_3304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_boxed_3302_, v_i_boxed_3303_, v_bs_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
return v_res_3304_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_unsigned_to_nat(16u);
v___x_3307_ = lean_mk_array(v___x_3306_, v___x_3305_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0);
v___x_3309_ = lean_unsigned_to_nat(0u);
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
lean_ctor_set(v___x_3310_, 1, v___x_3308_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(lean_object* v_e_3313_, uint8_t v_alsoCasesOn_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
uint8_t v___x_3326_; 
v___x_3326_ = l_Lean_Expr_isApp(v_e_3313_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_dec_ref(v_e_3313_);
v___x_3327_ = lean_box(0);
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
return v___x_3328_;
}
else
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Lean_Expr_getAppFn(v_e_3313_);
if (lean_obj_tag(v___x_3329_) == 4)
{
lean_object* v_declName_3330_; lean_object* v_us_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3486_; 
v_declName_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc_n(v_declName_3330_, 2);
v_us_3331_ = lean_ctor_get(v___x_3329_, 1);
lean_inc(v_us_3331_);
lean_dec_ref_known(v___x_3329_, 2);
v___x_3332_ = l_Lean_instInhabitedExpr;
v___x_3333_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3330_, v___y_3321_);
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3486_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3486_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
if (lean_obj_tag(v_a_3334_) == 1)
{
lean_object* v_val_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3379_; 
v_val_3338_ = lean_ctor_get(v_a_3334_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_a_3334_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3340_ = v_a_3334_;
v_isShared_3341_ = v_isSharedCheck_3379_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_val_3338_);
lean_dec(v_a_3334_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3379_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v_dummy_3342_; lean_object* v_nargs_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v_args_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; 
v_dummy_3342_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_3343_ = l_Lean_Expr_getAppNumArgs(v_e_3313_);
lean_inc(v_nargs_3343_);
v___x_3344_ = lean_mk_array(v_nargs_3343_, v_dummy_3342_);
v___x_3345_ = lean_unsigned_to_nat(1u);
v___x_3346_ = lean_nat_sub(v_nargs_3343_, v___x_3345_);
lean_dec(v_nargs_3343_);
v_args_3347_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3313_, v___x_3344_, v___x_3346_);
v___x_3348_ = lean_array_get_size(v_args_3347_);
v___x_3349_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_3338_);
v___x_3350_ = lean_nat_dec_lt(v___x_3348_, v___x_3349_);
lean_dec(v___x_3349_);
if (v___x_3350_ == 0)
{
lean_object* v_numParams_3351_; lean_object* v_numDiscrs_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3370_; 
v_numParams_3351_ = lean_ctor_get(v_val_3338_, 0);
v_numDiscrs_3352_ = lean_ctor_get(v_val_3338_, 1);
v___x_3353_ = lean_array_mk(v_us_3331_);
v___x_3354_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3351_);
v___x_3355_ = l_Array_extract___redArg(v_args_3347_, v___x_3354_, v_numParams_3351_);
v___x_3356_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3338_);
v___x_3357_ = lean_array_get(v___x_3332_, v_args_3347_, v___x_3356_);
lean_dec(v___x_3356_);
v___x_3358_ = lean_nat_add(v_numParams_3351_, v___x_3345_);
v___x_3359_ = lean_nat_add(v___x_3358_, v_numDiscrs_3352_);
lean_inc(v___x_3359_);
lean_inc_ref_n(v_args_3347_, 2);
v___x_3360_ = l_Array_toSubarray___redArg(v_args_3347_, v___x_3358_, v___x_3359_);
v___x_3361_ = l_Subarray_copy___redArg(v___x_3360_);
v___x_3362_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3338_);
v___x_3363_ = lean_nat_add(v___x_3359_, v___x_3362_);
lean_dec(v___x_3362_);
lean_inc(v___x_3363_);
v___x_3364_ = l_Array_toSubarray___redArg(v_args_3347_, v___x_3359_, v___x_3363_);
v___x_3365_ = l_Subarray_copy___redArg(v___x_3364_);
v___x_3366_ = l_Array_toSubarray___redArg(v_args_3347_, v___x_3363_, v___x_3348_);
v___x_3367_ = l_Subarray_copy___redArg(v___x_3366_);
v___x_3368_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3368_, 0, v_val_3338_);
lean_ctor_set(v___x_3368_, 1, v_declName_3330_);
lean_ctor_set(v___x_3368_, 2, v___x_3353_);
lean_ctor_set(v___x_3368_, 3, v___x_3355_);
lean_ctor_set(v___x_3368_, 4, v___x_3357_);
lean_ctor_set(v___x_3368_, 5, v___x_3361_);
lean_ctor_set(v___x_3368_, 6, v___x_3365_);
lean_ctor_set(v___x_3368_, 7, v___x_3367_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3368_);
v___x_3370_ = v___x_3340_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3372_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3370_);
v___x_3372_ = v___x_3336_;
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
else
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
lean_dec_ref(v_args_3347_);
lean_del_object(v___x_3340_);
lean_dec(v_val_3338_);
lean_dec(v_us_3331_);
lean_dec(v_declName_3330_);
v___x_3375_ = lean_box(0);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3375_);
v___x_3377_ = v___x_3336_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
else
{
lean_object* v___x_3380_; 
lean_del_object(v___x_3336_);
lean_dec(v_a_3334_);
v___x_3380_ = lean_st_ref_get(v___y_3321_);
if (v_alsoCasesOn_3314_ == 0)
{
lean_dec(v___x_3380_);
lean_dec(v_us_3331_);
lean_dec(v_declName_3330_);
lean_dec_ref(v_e_3313_);
goto v___jp_3323_;
}
else
{
lean_object* v_env_3381_; uint8_t v___x_3382_; 
v_env_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc_ref(v_env_3381_);
lean_dec(v___x_3380_);
lean_inc(v_declName_3330_);
v___x_3382_ = l_Lean_isCasesOnRecursor(v_env_3381_, v_declName_3330_);
if (v___x_3382_ == 0)
{
lean_dec(v_us_3331_);
lean_dec(v_declName_3330_);
lean_dec_ref(v_e_3313_);
goto v___jp_3323_;
}
else
{
lean_object* v_indName_3383_; lean_object* v___x_3384_; 
v_indName_3383_ = l_Lean_Name_getPrefix(v_declName_3330_);
v___x_3384_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_indName_3383_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3477_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3477_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3477_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
if (lean_obj_tag(v_a_3385_) == 5)
{
lean_object* v_val_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3472_; 
v_val_3389_ = lean_ctor_get(v_a_3385_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_a_3385_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3391_ = v_a_3385_;
v_isShared_3392_ = v_isSharedCheck_3472_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_val_3389_);
lean_dec(v_a_3385_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3472_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_toConstantVal_3393_; lean_object* v_numParams_3394_; lean_object* v_numIndices_3395_; lean_object* v_ctors_3396_; lean_object* v_nargs_3397_; lean_object* v_dummy_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v_args_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v_toConstantVal_3393_ = lean_ctor_get(v_val_3389_, 0);
lean_inc_ref(v_toConstantVal_3393_);
v_numParams_3394_ = lean_ctor_get(v_val_3389_, 1);
lean_inc(v_numParams_3394_);
v_numIndices_3395_ = lean_ctor_get(v_val_3389_, 2);
lean_inc(v_numIndices_3395_);
v_ctors_3396_ = lean_ctor_get(v_val_3389_, 4);
lean_inc(v_ctors_3396_);
v_nargs_3397_ = l_Lean_Expr_getAppNumArgs(v_e_3313_);
v_dummy_3398_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_3397_);
v___x_3399_ = lean_mk_array(v_nargs_3397_, v_dummy_3398_);
v___x_3400_ = lean_unsigned_to_nat(1u);
v___x_3401_ = lean_nat_sub(v_nargs_3397_, v___x_3400_);
lean_dec(v_nargs_3397_);
v_args_3402_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3313_, v___x_3399_, v___x_3401_);
v___x_3403_ = lean_nat_add(v_numParams_3394_, v___x_3400_);
v___x_3404_ = lean_nat_add(v___x_3403_, v_numIndices_3395_);
v___x_3405_ = lean_nat_add(v___x_3404_, v___x_3400_);
lean_dec(v___x_3404_);
v___x_3406_ = l_Lean_InductiveVal_numCtors(v_val_3389_);
lean_dec_ref(v_val_3389_);
v___x_3407_ = lean_nat_add(v___x_3405_, v___x_3406_);
lean_dec(v___x_3406_);
v___x_3408_ = lean_array_get_size(v_args_3402_);
v___x_3409_ = lean_nat_dec_le(v___x_3407_, v___x_3408_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3412_; 
lean_dec(v___x_3407_);
lean_dec(v___x_3405_);
lean_dec(v___x_3403_);
lean_dec_ref(v_args_3402_);
lean_dec(v_ctors_3396_);
lean_dec(v_numIndices_3395_);
lean_dec(v_numParams_3394_);
lean_dec_ref(v_toConstantVal_3393_);
lean_del_object(v___x_3391_);
lean_dec(v_us_3331_);
lean_dec(v_declName_3330_);
v___x_3410_ = lean_box(0);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3410_);
v___x_3412_ = v___x_3387_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
else
{
lean_object* v___x_3414_; lean_object* v_params_3415_; lean_object* v_motive_3416_; lean_object* v_discrs_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v_discrInfos_3420_; lean_object* v_alts_3421_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v_lower_3463_; lean_object* v_upper_3464_; uint8_t v___x_3471_; 
lean_del_object(v___x_3387_);
v___x_3414_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3394_);
lean_inc_ref_n(v_args_3402_, 3);
v_params_3415_ = l_Array_toSubarray___redArg(v_args_3402_, v___x_3414_, v_numParams_3394_);
v_motive_3416_ = lean_array_get(v___x_3332_, v_args_3402_, v_numParams_3394_);
lean_dec(v_numParams_3394_);
lean_inc(v___x_3405_);
v_discrs_3417_ = l_Array_toSubarray___redArg(v_args_3402_, v___x_3403_, v___x_3405_);
v___x_3418_ = lean_nat_add(v_numIndices_3395_, v___x_3400_);
lean_dec(v_numIndices_3395_);
v___x_3419_ = lean_box(0);
v_discrInfos_3420_ = lean_mk_array(v___x_3418_, v___x_3419_);
lean_inc(v___x_3407_);
v_alts_3421_ = l_Array_toSubarray___redArg(v_args_3402_, v___x_3405_, v___x_3407_);
v___x_3471_ = lean_nat_dec_le(v___x_3407_, v___x_3414_);
if (v___x_3471_ == 0)
{
v_lower_3463_ = v___x_3407_;
v_upper_3464_ = v___x_3408_;
goto v___jp_3462_;
}
else
{
lean_dec(v___x_3407_);
v_lower_3463_ = v___x_3414_;
v_upper_3464_ = v___x_3408_;
goto v___jp_3462_;
}
v___jp_3422_:
{
lean_object* v___x_3425_; size_t v_sz_3426_; size_t v___x_3427_; lean_object* v___x_3428_; 
v___x_3425_ = lean_array_mk(v_ctors_3396_);
v_sz_3426_ = lean_array_size(v___x_3425_);
v___x_3427_ = ((size_t)0ULL);
v___x_3428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_3426_, v___x_3427_, v___x_3425_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3453_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3431_ = v___x_3428_;
v_isShared_3432_ = v_isSharedCheck_3453_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3453_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_start_3433_; lean_object* v_stop_3434_; lean_object* v_start_3435_; lean_object* v_stop_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
v_start_3433_ = lean_ctor_get(v_params_3415_, 1);
v_stop_3434_ = lean_ctor_get(v_params_3415_, 2);
v_start_3435_ = lean_ctor_get(v_discrs_3417_, 1);
v_stop_3436_ = lean_ctor_get(v_discrs_3417_, 2);
v___x_3437_ = lean_nat_sub(v_stop_3434_, v_start_3433_);
v___x_3438_ = lean_nat_sub(v_stop_3436_, v_start_3435_);
v___x_3439_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1);
v___x_3440_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3437_);
lean_ctor_set(v___x_3440_, 1, v___x_3438_);
lean_ctor_set(v___x_3440_, 2, v_a_3429_);
lean_ctor_set(v___x_3440_, 3, v___y_3424_);
lean_ctor_set(v___x_3440_, 4, v_discrInfos_3420_);
lean_ctor_set(v___x_3440_, 5, v___x_3439_);
v___x_3441_ = lean_array_mk(v_us_3331_);
v___x_3442_ = l_Subarray_copy___redArg(v_params_3415_);
v___x_3443_ = l_Subarray_copy___redArg(v_discrs_3417_);
v___x_3444_ = l_Subarray_copy___redArg(v_alts_3421_);
v___x_3445_ = l_Subarray_copy___redArg(v___y_3423_);
v___x_3446_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3440_);
lean_ctor_set(v___x_3446_, 1, v_declName_3330_);
lean_ctor_set(v___x_3446_, 2, v___x_3441_);
lean_ctor_set(v___x_3446_, 3, v___x_3442_);
lean_ctor_set(v___x_3446_, 4, v_motive_3416_);
lean_ctor_set(v___x_3446_, 5, v___x_3443_);
lean_ctor_set(v___x_3446_, 6, v___x_3444_);
lean_ctor_set(v___x_3446_, 7, v___x_3445_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set_tag(v___x_3391_, 1);
lean_ctor_set(v___x_3391_, 0, v___x_3446_);
v___x_3448_ = v___x_3391_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3450_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3448_);
v___x_3450_ = v___x_3431_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec_ref(v_alts_3421_);
lean_dec_ref(v_discrInfos_3420_);
lean_dec_ref(v_discrs_3417_);
lean_dec(v_motive_3416_);
lean_dec_ref(v_params_3415_);
lean_del_object(v___x_3391_);
lean_dec(v_us_3331_);
lean_dec(v_declName_3330_);
v_a_3454_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3428_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3428_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
v___jp_3462_:
{
lean_object* v_levelParams_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v_levelParams_3465_ = lean_ctor_get(v_toConstantVal_3393_, 1);
lean_inc(v_levelParams_3465_);
lean_dec_ref(v_toConstantVal_3393_);
v___x_3466_ = l_Array_toSubarray___redArg(v_args_3402_, v_lower_3463_, v_upper_3464_);
v___x_3467_ = l_List_lengthTR___redArg(v_levelParams_3465_);
lean_dec(v_levelParams_3465_);
v___x_3468_ = l_List_lengthTR___redArg(v_us_3331_);
v___x_3469_ = lean_nat_dec_eq(v___x_3467_, v___x_3468_);
lean_dec(v___x_3468_);
lean_dec(v___x_3467_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; 
v___x_3470_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__2));
v___y_3423_ = v___x_3466_;
v___y_3424_ = v___x_3470_;
goto v___jp_3422_;
}
else
{
v___y_3423_ = v___x_3466_;
v___y_3424_ = v___x_3419_;
goto v___jp_3422_;
}
}
}
}
}
else
{
lean_object* v___x_3473_; lean_object* v___x_3475_; 
lean_dec(v_a_3385_);
lean_dec(v_us_3331_);
lean_dec(v_declName_3330_);
lean_dec_ref(v_e_3313_);
v___x_3473_ = lean_box(0);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3473_);
v___x_3475_ = v___x_3387_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec(v_us_3331_);
lean_dec(v_declName_3330_);
lean_dec_ref(v_e_3313_);
v_a_3478_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3384_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3384_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
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
lean_dec_ref(v___x_3329_);
lean_dec_ref(v_e_3313_);
goto v___jp_3323_;
}
}
v___jp_3323_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = lean_box(0);
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
return v___x_3325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___boxed(lean_object* v_e_3487_, lean_object* v_alsoCasesOn_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
uint8_t v_alsoCasesOn_boxed_3497_; lean_object* v_res_3498_; 
v_alsoCasesOn_boxed_3497_ = lean_unbox(v_alsoCasesOn_3488_);
v_res_3498_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3487_, v_alsoCasesOn_boxed_3497_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
return v_res_3498_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__1));
v___x_3503_ = l_Lean_stringToMessageData(v___x_3502_);
return v___x_3503_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_unsigned_to_nat(1u);
v___x_3505_ = l_Lean_Expr_bvar___override(v___x_3504_);
return v___x_3505_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__5));
v___x_3509_ = lean_unsigned_to_nat(2u);
v___x_3510_ = lean_unsigned_to_nat(182u);
v___x_3511_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__4));
v___x_3512_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_3513_ = l_mkPanicMessageWithDecl(v___x_3512_, v___x_3511_, v___x_3510_, v___x_3509_, v___x_3508_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(lean_object* v_e_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_e_3523_; uint8_t v___x_3524_; lean_object* v___x_3525_; 
v_e_3523_ = l_Lean_Expr_headBeta(v_e_3514_);
v___x_3524_ = 1;
v___x_3525_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3523_, v___x_3524_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3775_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3528_ = v___x_3525_;
v_isShared_3529_ = v_isSharedCheck_3775_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3525_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3775_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
if (lean_obj_tag(v_a_3526_) == 1)
{
lean_object* v_val_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3770_; 
v_val_3530_ = lean_ctor_get(v_a_3526_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v_a_3526_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3532_ = v_a_3526_;
v_isShared_3533_ = v_isSharedCheck_3770_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_val_3530_);
lean_dec(v_a_3526_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3770_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v_toMatcherInfo_3534_; lean_object* v_matcherName_3535_; lean_object* v_params_3536_; lean_object* v_motive_3537_; lean_object* v_discrs_3538_; lean_object* v_alts_3539_; lean_object* v_remaining_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v_toMatcherInfo_3534_ = lean_ctor_get(v_val_3530_, 0);
lean_inc_ref(v_toMatcherInfo_3534_);
v_matcherName_3535_ = lean_ctor_get(v_val_3530_, 1);
lean_inc(v_matcherName_3535_);
v_params_3536_ = lean_ctor_get(v_val_3530_, 3);
lean_inc_ref(v_params_3536_);
v_motive_3537_ = lean_ctor_get(v_val_3530_, 4);
lean_inc_ref(v_motive_3537_);
v_discrs_3538_ = lean_ctor_get(v_val_3530_, 5);
lean_inc_ref(v_discrs_3538_);
v_alts_3539_ = lean_ctor_get(v_val_3530_, 6);
lean_inc_ref(v_alts_3539_);
v_remaining_3540_ = lean_ctor_get(v_val_3530_, 7);
lean_inc_ref(v_remaining_3540_);
v___x_3541_ = lean_unsigned_to_nat(0u);
v___x_3542_ = lean_array_get_size(v_remaining_3540_);
v___x_3543_ = lean_nat_dec_lt(v___x_3541_, v___x_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
lean_dec(v_val_3530_);
v___x_3544_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3544_);
v___x_3546_ = v___x_3528_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
else
{
lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3548_ = lean_array_fget_borrowed(v_remaining_3540_, v___x_3541_);
v___x_3549_ = l_Lean_Expr_isLambda(v___x_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; lean_object* v___x_3552_; 
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
lean_dec(v_val_3530_);
v___x_3550_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3550_);
v___x_3552_ = v___x_3528_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
else
{
lean_object* v___x_3554_; uint8_t v___x_3555_; 
v___x_3554_ = l_Lean_Expr_bindingBody_x21(v___x_3548_);
v___x_3555_ = l_Lean_Expr_isLambda(v___x_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; lean_object* v___x_3558_; 
lean_dec_ref(v___x_3554_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
lean_dec(v_val_3530_);
v___x_3556_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3556_);
v___x_3558_ = v___x_3528_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
else
{
lean_object* v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = l_Lean_Expr_bindingBody_x21(v___x_3554_);
lean_dec_ref(v___x_3554_);
v___x_3561_ = l_Lean_Expr_isApp(v___x_3560_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; lean_object* v___x_3564_; 
lean_dec_ref(v___x_3560_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
lean_dec(v_val_3530_);
v___x_3562_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3562_);
v___x_3564_ = v___x_3528_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
else
{
uint8_t v___x_3566_; 
v___x_3566_ = lean_expr_has_loose_bvar(v___x_3560_, v___x_3541_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___y_3570_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3567_ = l_Lean_Expr_appArg_x21(v___x_3560_);
v___x_3568_ = lean_unsigned_to_nat(1u);
v___x_3633_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3);
v___x_3634_ = lean_expr_eqv(v___x_3567_, v___x_3633_);
lean_dec_ref(v___x_3567_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3637_; 
lean_dec_ref(v___x_3560_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
lean_dec(v_val_3530_);
v___x_3635_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3635_);
v___x_3637_ = v___x_3528_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
else
{
lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3639_ = l_Lean_Expr_appFn_x21(v___x_3560_);
lean_dec_ref(v___x_3560_);
v___x_3640_ = lean_expr_has_loose_bvar(v___x_3639_, v___x_3568_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; 
lean_del_object(v___x_3528_);
lean_inc(v_a_3521_);
lean_inc_ref(v_a_3520_);
lean_inc(v_a_3519_);
lean_inc_ref(v_a_3518_);
lean_inc_ref(v___x_3639_);
v___x_3641_ = lean_infer_type(v___x_3639_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3643_; uint8_t v_transparency_3644_; uint8_t v___x_3645_; lean_object* v___y_3647_; uint8_t v___x_3738_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___x_3641_, 1);
v___x_3643_ = l_Lean_Meta_Context_config(v_a_3518_);
v_transparency_3644_ = lean_ctor_get_uint8(v___x_3643_, 9);
v___x_3645_ = 0;
v___x_3738_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3644_, v___x_3645_);
if (v___x_3738_ == 0)
{
lean_object* v_keyedConfig_3739_; uint8_t v_trackZetaDelta_3740_; lean_object* v_zetaDeltaSet_3741_; lean_object* v_lctx_3742_; lean_object* v_localInstances_3743_; lean_object* v_defEqCtx_x3f_3744_; lean_object* v_synthPendingDepth_3745_; lean_object* v_customCanUnfoldPredicate_x3f_3746_; uint8_t v_univApprox_3747_; uint8_t v_inTypeClassResolution_3748_; uint8_t v_cacheInferType_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v_keyedConfig_3739_ = lean_ctor_get(v_a_3518_, 0);
v_trackZetaDelta_3740_ = lean_ctor_get_uint8(v_a_3518_, sizeof(void*)*7);
v_zetaDeltaSet_3741_ = lean_ctor_get(v_a_3518_, 1);
v_lctx_3742_ = lean_ctor_get(v_a_3518_, 2);
v_localInstances_3743_ = lean_ctor_get(v_a_3518_, 3);
v_defEqCtx_x3f_3744_ = lean_ctor_get(v_a_3518_, 4);
v_synthPendingDepth_3745_ = lean_ctor_get(v_a_3518_, 5);
v_customCanUnfoldPredicate_x3f_3746_ = lean_ctor_get(v_a_3518_, 6);
v_univApprox_3747_ = lean_ctor_get_uint8(v_a_3518_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3748_ = lean_ctor_get_uint8(v_a_3518_, sizeof(void*)*7 + 2);
v_cacheInferType_3749_ = lean_ctor_get_uint8(v_a_3518_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3739_);
v___x_3750_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3645_, v_keyedConfig_3739_);
lean_inc(v_customCanUnfoldPredicate_x3f_3746_);
lean_inc(v_synthPendingDepth_3745_);
lean_inc(v_defEqCtx_x3f_3744_);
lean_inc_ref(v_localInstances_3743_);
lean_inc_ref(v_lctx_3742_);
lean_inc(v_zetaDeltaSet_3741_);
v___x_3751_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_ctor_set(v___x_3751_, 1, v_zetaDeltaSet_3741_);
lean_ctor_set(v___x_3751_, 2, v_lctx_3742_);
lean_ctor_set(v___x_3751_, 3, v_localInstances_3743_);
lean_ctor_set(v___x_3751_, 4, v_defEqCtx_x3f_3744_);
lean_ctor_set(v___x_3751_, 5, v_synthPendingDepth_3745_);
lean_ctor_set(v___x_3751_, 6, v_customCanUnfoldPredicate_x3f_3746_);
lean_ctor_set_uint8(v___x_3751_, sizeof(void*)*7, v_trackZetaDelta_3740_);
lean_ctor_set_uint8(v___x_3751_, sizeof(void*)*7 + 1, v_univApprox_3747_);
lean_ctor_set_uint8(v___x_3751_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3748_);
lean_ctor_set_uint8(v___x_3751_, sizeof(void*)*7 + 3, v_cacheInferType_3749_);
v___x_3752_ = l_Lean_Meta_whnfForall(v_a_3642_, v___x_3751_, v_a_3519_, v_a_3520_, v_a_3521_);
lean_dec_ref_known(v___x_3751_, 7);
v___y_3647_ = v___x_3752_;
goto v___jp_3646_;
}
else
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Lean_Meta_whnfForall(v_a_3642_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
v___y_3647_ = v___x_3753_;
goto v___jp_3646_;
}
v___jp_3646_:
{
if (lean_obj_tag(v___y_3647_) == 0)
{
lean_object* v_a_3648_; uint8_t v___x_3649_; 
v_a_3648_ = lean_ctor_get(v___y_3647_, 0);
lean_inc(v_a_3648_);
lean_dec_ref_known(v___y_3647_, 1);
v___x_3649_ = l_Lean_Expr_isForall(v_a_3648_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_dec(v_a_3648_);
lean_dec_ref(v___x_3643_);
lean_dec_ref(v___x_3639_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
lean_dec(v_val_3530_);
v___x_3650_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6);
v___x_3651_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v___x_3650_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
return v___x_3651_;
}
else
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3652_ = l_Lean_Expr_bindingDomain_x21(v_a_3648_);
v___x_3653_ = l_Lean_Expr_bindingName_x21(v_a_3648_);
v___x_3654_ = l_Lean_Expr_bindingBody_x21(v_a_3648_);
lean_dec(v_a_3648_);
v___x_3655_ = 0;
v___x_3656_ = lean_box(v___x_3655_);
v___x_3657_ = lean_box(v___x_3640_);
v___x_3658_ = lean_box(v___x_3524_);
v___f_3659_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3659_, 0, v___x_3656_);
lean_closure_set(v___f_3659_, 1, v___x_3657_);
lean_closure_set(v___f_3659_, 2, v___x_3658_);
lean_inc_ref(v___x_3652_);
v___x_3660_ = l_Lean_Expr_lam___override(v___x_3653_, v___x_3652_, v___x_3654_, v___x_3655_);
v___x_3661_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_val_3530_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3721_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3721_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3721_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
if (lean_obj_tag(v_a_3662_) == 1)
{
lean_object* v_val_3666_; lean_object* v___x_3667_; 
lean_del_object(v___x_3664_);
v_val_3666_ = lean_ctor_get(v_a_3662_, 0);
lean_inc(v_val_3666_);
lean_dec_ref_known(v_a_3662_, 1);
v___x_3667_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_motive_3537_, v___f_3659_, v___x_3640_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3669_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref_known(v___x_3667_, 1);
v___x_3669_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_3535_, v_toMatcherInfo_3534_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; uint8_t v_transparency_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; size_t v_sz_3682_; size_t v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3669_, 1);
v_transparency_3671_ = lean_ctor_get_uint8(v___x_3643_, 9);
lean_dec_ref(v___x_3643_);
v___x_3672_ = lean_unsigned_to_nat(5u);
v___x_3673_ = lean_mk_empty_array_with_capacity(v___x_3672_);
v___x_3674_ = lean_array_push(v___x_3673_, v_val_3666_);
v___x_3675_ = lean_array_push(v___x_3674_, v___x_3652_);
v___x_3676_ = lean_array_push(v___x_3675_, v___x_3660_);
v___x_3677_ = lean_array_push(v___x_3676_, v___x_3639_);
v___x_3678_ = lean_array_push(v___x_3677_, v_a_3668_);
v___x_3679_ = l_Array_append___redArg(v_params_3536_, v___x_3678_);
lean_dec_ref(v___x_3678_);
v___x_3680_ = l_Array_append___redArg(v___x_3679_, v_discrs_3538_);
lean_dec_ref(v_discrs_3538_);
v___x_3681_ = l_Array_append___redArg(v___x_3680_, v_alts_3539_);
lean_dec_ref(v_alts_3539_);
v_sz_3682_ = lean_array_size(v___x_3681_);
v___x_3683_ = ((size_t)0ULL);
v___x_3684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_3682_, v___x_3683_, v___x_3681_);
v___x_3685_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3671_, v___x_3645_);
if (v___x_3685_ == 0)
{
lean_object* v_keyedConfig_3686_; uint8_t v_trackZetaDelta_3687_; lean_object* v_zetaDeltaSet_3688_; lean_object* v_lctx_3689_; lean_object* v_localInstances_3690_; lean_object* v_defEqCtx_x3f_3691_; lean_object* v_synthPendingDepth_3692_; lean_object* v_customCanUnfoldPredicate_x3f_3693_; uint8_t v_univApprox_3694_; uint8_t v_inTypeClassResolution_3695_; uint8_t v_cacheInferType_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v_keyedConfig_3686_ = lean_ctor_get(v_a_3518_, 0);
v_trackZetaDelta_3687_ = lean_ctor_get_uint8(v_a_3518_, sizeof(void*)*7);
v_zetaDeltaSet_3688_ = lean_ctor_get(v_a_3518_, 1);
v_lctx_3689_ = lean_ctor_get(v_a_3518_, 2);
v_localInstances_3690_ = lean_ctor_get(v_a_3518_, 3);
v_defEqCtx_x3f_3691_ = lean_ctor_get(v_a_3518_, 4);
v_synthPendingDepth_3692_ = lean_ctor_get(v_a_3518_, 5);
v_customCanUnfoldPredicate_x3f_3693_ = lean_ctor_get(v_a_3518_, 6);
v_univApprox_3694_ = lean_ctor_get_uint8(v_a_3518_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3695_ = lean_ctor_get_uint8(v_a_3518_, sizeof(void*)*7 + 2);
v_cacheInferType_3696_ = lean_ctor_get_uint8(v_a_3518_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3686_);
v___x_3697_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3645_, v_keyedConfig_3686_);
lean_inc(v_customCanUnfoldPredicate_x3f_3693_);
lean_inc(v_synthPendingDepth_3692_);
lean_inc(v_defEqCtx_x3f_3691_);
lean_inc_ref(v_localInstances_3690_);
lean_inc_ref(v_lctx_3689_);
lean_inc(v_zetaDeltaSet_3688_);
v___x_3698_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
lean_ctor_set(v___x_3698_, 1, v_zetaDeltaSet_3688_);
lean_ctor_set(v___x_3698_, 2, v_lctx_3689_);
lean_ctor_set(v___x_3698_, 3, v_localInstances_3690_);
lean_ctor_set(v___x_3698_, 4, v_defEqCtx_x3f_3691_);
lean_ctor_set(v___x_3698_, 5, v_synthPendingDepth_3692_);
lean_ctor_set(v___x_3698_, 6, v_customCanUnfoldPredicate_x3f_3693_);
lean_ctor_set_uint8(v___x_3698_, sizeof(void*)*7, v_trackZetaDelta_3687_);
lean_ctor_set_uint8(v___x_3698_, sizeof(void*)*7 + 1, v_univApprox_3694_);
lean_ctor_set_uint8(v___x_3698_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3695_);
lean_ctor_set_uint8(v___x_3698_, sizeof(void*)*7 + 3, v_cacheInferType_3696_);
v___x_3699_ = l_Lean_Meta_mkAppOptM(v_a_3670_, v___x_3684_, v___x_3698_, v_a_3519_, v_a_3520_, v_a_3521_);
lean_dec_ref_known(v___x_3698_, 7);
v___y_3570_ = v___x_3699_;
goto v___jp_3569_;
}
else
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_Meta_mkAppOptM(v_a_3670_, v___x_3684_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
v___y_3570_ = v___x_3700_;
goto v___jp_3569_;
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec(v_a_3668_);
lean_dec(v_val_3666_);
lean_dec_ref(v___x_3660_);
lean_dec_ref(v___x_3652_);
lean_dec_ref(v___x_3643_);
lean_dec_ref(v___x_3639_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_params_3536_);
lean_del_object(v___x_3532_);
v_a_3701_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3669_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3669_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec(v_val_3666_);
lean_dec_ref(v___x_3660_);
lean_dec_ref(v___x_3652_);
lean_dec_ref(v___x_3643_);
lean_dec_ref(v___x_3639_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
v_a_3709_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3667_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3667_);
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
else
{
lean_object* v___x_3717_; lean_object* v___x_3719_; 
lean_dec(v_a_3662_);
lean_dec_ref(v___x_3660_);
lean_dec_ref(v___f_3659_);
lean_dec_ref(v___x_3652_);
lean_dec_ref(v___x_3643_);
lean_dec_ref(v___x_3639_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
v___x_3717_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3717_);
v___x_3719_ = v___x_3664_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3717_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec_ref(v___x_3660_);
lean_dec_ref(v___f_3659_);
lean_dec_ref(v___x_3652_);
lean_dec_ref(v___x_3643_);
lean_dec_ref(v___x_3639_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
v_a_3722_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3661_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3661_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v___x_3643_);
lean_dec_ref(v___x_3639_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
lean_dec(v_val_3530_);
v_a_3730_ = lean_ctor_get(v___y_3647_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___y_3647_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___y_3647_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___y_3647_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
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
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec_ref(v___x_3639_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
lean_dec(v_val_3530_);
v_a_3754_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3641_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3641_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3764_; 
lean_dec_ref(v___x_3639_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
lean_dec(v_val_3530_);
v___x_3762_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3762_);
v___x_3764_ = v___x_3528_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
v___jp_3569_:
{
if (lean_obj_tag(v___y_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3572_; 
v_a_3571_ = lean_ctor_get(v___y_3570_, 0);
lean_inc_n(v_a_3571_, 2);
lean_dec_ref_known(v___y_3570_, 1);
lean_inc(v_a_3521_);
lean_inc_ref(v_a_3520_);
lean_inc(v_a_3519_);
lean_inc_ref(v_a_3518_);
v___x_3572_ = lean_infer_type(v_a_3571_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v___x_3572_, 1);
v___x_3574_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_3575_ = lean_unsigned_to_nat(3u);
v___x_3576_ = l_Lean_Expr_isAppOfArity(v_a_3573_, v___x_3574_, v___x_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; 
lean_dec(v_a_3573_);
lean_dec_ref(v_remaining_3540_);
lean_del_object(v___x_3532_);
lean_inc(v_a_3521_);
lean_inc_ref(v_a_3520_);
lean_inc(v_a_3519_);
lean_inc_ref(v_a_3518_);
v___x_3577_ = lean_infer_type(v_a_3571_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v___x_3579_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2);
v___x_3580_ = l_Lean_indentExpr(v_a_3578_);
v___x_3581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3579_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v___x_3581_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
return v___x_3582_;
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
v_a_3583_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3577_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3577_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3591_ = l_Lean_Expr_appArg_x21(v_a_3573_);
lean_dec(v_a_3573_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v_a_3571_);
v___x_3593_ = v___x_3532_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3571_);
v___x_3593_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3594_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3594_, 0, v___x_3591_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
lean_ctor_set_uint8(v___x_3594_, sizeof(void*)*2, v___x_3524_);
v___x_3595_ = l_Array_toSubarray___redArg(v_remaining_3540_, v___x_3568_, v___x_3542_);
v___x_3596_ = l_Subarray_copy___redArg(v___x_3595_);
v___x_3597_ = l_Lean_Meta_Simp_Result_addExtraArgs(v___x_3594_, v___x_3596_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
lean_dec_ref(v___x_3596_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3607_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3607_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3607_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3602_, 0, v_a_3598_);
v___x_3603_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3603_);
v___x_3605_ = v___x_3600_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
v_a_3608_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3597_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3597_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec(v_a_3571_);
lean_dec_ref(v_remaining_3540_);
lean_del_object(v___x_3532_);
v_a_3617_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3572_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3572_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec_ref(v_remaining_3540_);
lean_del_object(v___x_3532_);
v_a_3625_ = lean_ctor_get(v___y_3570_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___y_3570_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___y_3570_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___y_3570_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
lean_dec_ref(v___x_3560_);
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_alts_3539_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec(v_matcherName_3535_);
lean_dec_ref(v_toMatcherInfo_3534_);
lean_del_object(v___x_3532_);
lean_dec(v_val_3530_);
v___x_3766_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3766_);
v___x_3768_ = v___x_3528_;
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
}
}
}
}
else
{
lean_object* v___x_3771_; lean_object* v___x_3773_; 
lean_dec(v_a_3526_);
v___x_3771_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3771_);
v___x_3773_ = v___x_3528_;
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
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
v_a_3776_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3525_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3525_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed(lean_object* v_e_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(v_e_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
lean_dec(v_a_3791_);
lean_dec_ref(v_a_3790_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
lean_dec(v_a_3787_);
lean_dec_ref(v_a_3786_);
lean_dec(v_a_3785_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(lean_object* v_declName_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3794_, v___y_3801_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___boxed(lean_object* v_declName_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(v_declName_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(lean_object* v_00_u03b1_3814_, lean_object* v_msg_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_3815_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___boxed(lean_object* v_00_u03b1_3825_, lean_object* v_msg_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(v_00_u03b1_3825_, v_msg_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3836_, lean_object* v_constName_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3847_, lean_object* v_constName_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(v_00_u03b1_3847_, v_constName_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b1_3858_, lean_object* v_ref_3859_, lean_object* v_constName_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v___x_3869_; 
v___x_3869_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3859_, v_constName_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b1_3870_, lean_object* v_ref_3871_, lean_object* v_constName_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(v_00_u03b1_3870_, v_ref_3871_, v_constName_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec(v_ref_3871_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3882_, lean_object* v_ref_3883_, lean_object* v_msg_3884_, lean_object* v_declHint_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3883_, v_msg_3884_, v_declHint_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3895_, lean_object* v_ref_3896_, lean_object* v_msg_3897_, lean_object* v_declHint_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_3895_, v_ref_3896_, v_msg_3897_, v_declHint_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec(v_ref_3896_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_3908_, lean_object* v_declHint_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3908_, v_declHint_3909_, v___y_3916_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_3919_, lean_object* v_declHint_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(v_msg_3919_, v_declHint_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(lean_object* v_00_u03b1_3930_, lean_object* v_ref_3931_, lean_object* v_msg_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v___x_3941_; 
v___x_3941_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3931_, v_msg_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___boxed(lean_object* v_00_u03b1_3942_, lean_object* v_ref_3943_, lean_object* v_msg_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(v_00_u03b1_3942_, v_ref_3943_, v_msg_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec(v_ref_3943_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_3999_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4000_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4001_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed), 9, 0);
v___x_4002_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3999_, v___x_4000_, v___x_4001_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10____boxed(lean_object* v_a_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_();
return v_res_4004_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0(void){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
return v___x_4006_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4007_ = lean_unsigned_to_nat(32u);
v___x_4008_ = lean_mk_empty_array_with_capacity(v___x_4007_);
v___x_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
return v___x_4009_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2));
v___x_4012_ = l_Lean_stringToMessageData(v___x_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(lean_object* v___x_4013_, lean_object* v___x_4014_, lean_object* v___x_4015_, lean_object* v___x_4016_, lean_object* v___x_4017_, uint8_t v___x_4018_, lean_object* v_mvarId_4019_, uint8_t v___x_4020_, lean_object* v_declName_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_4013_, v___x_4014_, v___x_4015_, v___x_4016_, v___y_4022_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref_known(v___x_4027_, 1);
v___x_4029_ = lean_mk_empty_array_with_capacity(v___x_4017_);
v___x_4030_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4031_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4032_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4033_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
lean_inc(v___x_4017_);
v___x_4034_ = l_Lean_Name_num___override(v___x_4033_, v___x_4017_);
v___x_4035_ = l_Lean_Name_str___override(v___x_4034_, v___x_4030_);
v___x_4036_ = l_Lean_Name_str___override(v___x_4035_, v___x_4031_);
v___x_4037_ = l_Lean_Name_str___override(v___x_4036_, v___x_4032_);
v___x_4038_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4039_ = l_Lean_Name_str___override(v___x_4037_, v___x_4038_);
v___x_4040_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_4029_, v___x_4039_, v___x_4018_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; size_t v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___x_4040_, 1);
v___x_4042_ = lean_box(0);
v___x_4043_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0);
lean_inc_n(v___x_4017_, 2);
v___x_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
lean_ctor_set(v___x_4044_, 1, v___x_4017_);
v___x_4045_ = lean_unsigned_to_nat(32u);
v___x_4046_ = lean_mk_empty_array_with_capacity(v___x_4045_);
v___x_4047_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1);
v___x_4048_ = ((size_t)5ULL);
v___x_4049_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4049_, 0, v___x_4047_);
lean_ctor_set(v___x_4049_, 1, v___x_4046_);
lean_ctor_set(v___x_4049_, 2, v___x_4017_);
lean_ctor_set(v___x_4049_, 3, v___x_4017_);
lean_ctor_set_usize(v___x_4049_, 4, v___x_4048_);
v___x_4050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4043_);
lean_ctor_set(v___x_4050_, 1, v___x_4043_);
lean_ctor_set(v___x_4050_, 2, v___x_4043_);
lean_ctor_set(v___x_4050_, 3, v___x_4049_);
v___x_4051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4044_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = l_Lean_Meta_simpTarget(v_mvarId_4019_, v_a_4028_, v_a_4041_, v___x_4042_, v___x_4020_, v___x_4051_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4095_; 
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4055_ = v___x_4052_;
v_isShared_4056_ = v_isSharedCheck_4095_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4095_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v_fst_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4093_; 
v_fst_4057_ = lean_ctor_get(v_a_4053_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_a_4053_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; 
v_unused_4094_ = lean_ctor_get(v_a_4053_, 1);
lean_dec(v_unused_4094_);
v___x_4059_ = v_a_4053_;
v_isShared_4060_ = v_isSharedCheck_4093_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_fst_4057_);
lean_dec(v_a_4053_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4093_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
if (lean_obj_tag(v_fst_4057_) == 0)
{
lean_object* v___x_4061_; lean_object* v___x_4063_; 
lean_del_object(v___x_4059_);
lean_dec(v_declName_4021_);
v___x_4061_ = lean_box(0);
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 0, v___x_4061_);
v___x_4063_ = v___x_4055_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
else
{
lean_object* v_val_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4069_; 
lean_del_object(v___x_4055_);
v_val_4065_ = lean_ctor_get(v_fst_4057_, 0);
lean_inc(v_val_4065_);
lean_dec_ref_known(v_fst_4057_, 1);
v___x_4066_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3);
v___x_4067_ = l_Lean_MessageData_ofConstName(v_declName_4021_, v___x_4018_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set_tag(v___x_4059_, 7);
lean_ctor_set(v___x_4059_, 1, v___x_4067_);
lean_ctor_set(v___x_4059_, 0, v___x_4066_);
v___x_4069_ = v___x_4059_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4066_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v___x_4067_);
v___x_4069_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___f_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4070_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_4071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4069_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
v___f_4072_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4072_, 0, v___x_4071_);
v___x_4073_ = lean_box(v___x_4020_);
v___x_4074_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___boxed), 7, 2);
lean_closure_set(v___x_4074_, 0, v_val_4065_);
lean_closure_set(v___x_4074_, 1, v___x_4073_);
v___x_4075_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4074_, v___f_4072_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4075_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
v_a_4084_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4075_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4075_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
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
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec(v_declName_4021_);
v_a_4096_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4052_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4052_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec(v_a_4028_);
lean_dec(v_declName_4021_);
lean_dec(v_mvarId_4019_);
lean_dec(v___x_4017_);
v_a_4104_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4040_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4040_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
lean_dec(v_declName_4021_);
lean_dec(v_mvarId_4019_);
lean_dec(v___x_4017_);
v_a_4112_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4027_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4027_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___boxed(lean_object* v___x_4120_, lean_object* v___x_4121_, lean_object* v___x_4122_, lean_object* v___x_4123_, lean_object* v___x_4124_, lean_object* v___x_4125_, lean_object* v_mvarId_4126_, lean_object* v___x_4127_, lean_object* v_declName_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
uint8_t v___x_1412__boxed_4134_; uint8_t v___x_1413__boxed_4135_; lean_object* v_res_4136_; 
v___x_1412__boxed_4134_ = lean_unbox(v___x_4125_);
v___x_1413__boxed_4135_ = lean_unbox(v___x_4127_);
v_res_4136_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4120_, v___x_4121_, v___x_4122_, v___x_4123_, v___x_4124_, v___x_1412__boxed_4134_, v_mvarId_4126_, v___x_1413__boxed_4135_, v_declName_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
return v_res_4136_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2(void){
_start:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4146_ = lean_box(0);
v___x_4147_ = lean_unsigned_to_nat(16u);
v___x_4148_ = lean_mk_array(v___x_4147_, v___x_4146_);
return v___x_4148_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3(void){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2);
v___x_4150_ = lean_unsigned_to_nat(0u);
v___x_4151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
lean_ctor_set(v___x_4151_, 1, v___x_4149_);
return v___x_4151_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4(void){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4152_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
return v___x_4153_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5(void){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; lean_object* v___x_4157_; 
v___x_4154_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4);
v___x_4155_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3);
v___x_4156_ = 1;
v___x_4157_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4157_, 0, v___x_4155_);
lean_ctor_set(v___x_4157_, 1, v___x_4154_);
lean_ctor_set_uint8(v___x_4157_, sizeof(void*)*2, v___x_4156_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object* v_declName_4158_, lean_object* v_mvarId_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v___y_4166_; uint8_t v___x_4183_; uint8_t v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; uint8_t v_transparency_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
v___x_4183_ = 0;
v___x_4184_ = 1;
v___x_4185_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0));
v___x_4186_ = l_Lean_Meta_Context_config(v_a_4160_);
v_transparency_4187_ = lean_ctor_get_uint8(v___x_4186_, 9);
lean_dec_ref(v___x_4186_);
v___x_4188_ = lean_unsigned_to_nat(0u);
v___x_4189_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1));
v___x_4190_ = 0;
v___x_4191_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4192_ = l_Lean_Options_empty;
v___x_4193_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4187_, v___x_4190_);
if (v___x_4193_ == 0)
{
lean_object* v_keyedConfig_4194_; uint8_t v_trackZetaDelta_4195_; lean_object* v_zetaDeltaSet_4196_; lean_object* v_lctx_4197_; lean_object* v_localInstances_4198_; lean_object* v_defEqCtx_x3f_4199_; lean_object* v_synthPendingDepth_4200_; lean_object* v_customCanUnfoldPredicate_x3f_4201_; uint8_t v_univApprox_4202_; uint8_t v_inTypeClassResolution_4203_; uint8_t v_cacheInferType_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_keyedConfig_4194_ = lean_ctor_get(v_a_4160_, 0);
v_trackZetaDelta_4195_ = lean_ctor_get_uint8(v_a_4160_, sizeof(void*)*7);
v_zetaDeltaSet_4196_ = lean_ctor_get(v_a_4160_, 1);
v_lctx_4197_ = lean_ctor_get(v_a_4160_, 2);
v_localInstances_4198_ = lean_ctor_get(v_a_4160_, 3);
v_defEqCtx_x3f_4199_ = lean_ctor_get(v_a_4160_, 4);
v_synthPendingDepth_4200_ = lean_ctor_get(v_a_4160_, 5);
v_customCanUnfoldPredicate_x3f_4201_ = lean_ctor_get(v_a_4160_, 6);
v_univApprox_4202_ = lean_ctor_get_uint8(v_a_4160_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4203_ = lean_ctor_get_uint8(v_a_4160_, sizeof(void*)*7 + 2);
v_cacheInferType_4204_ = lean_ctor_get_uint8(v_a_4160_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4194_);
v___x_4205_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4190_, v_keyedConfig_4194_);
lean_inc(v_customCanUnfoldPredicate_x3f_4201_);
lean_inc(v_synthPendingDepth_4200_);
lean_inc(v_defEqCtx_x3f_4199_);
lean_inc_ref(v_localInstances_4198_);
lean_inc_ref(v_lctx_4197_);
lean_inc(v_zetaDeltaSet_4196_);
v___x_4206_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
lean_ctor_set(v___x_4206_, 1, v_zetaDeltaSet_4196_);
lean_ctor_set(v___x_4206_, 2, v_lctx_4197_);
lean_ctor_set(v___x_4206_, 3, v_localInstances_4198_);
lean_ctor_set(v___x_4206_, 4, v_defEqCtx_x3f_4199_);
lean_ctor_set(v___x_4206_, 5, v_synthPendingDepth_4200_);
lean_ctor_set(v___x_4206_, 6, v_customCanUnfoldPredicate_x3f_4201_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*7, v_trackZetaDelta_4195_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*7 + 1, v_univApprox_4202_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4203_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*7 + 3, v_cacheInferType_4204_);
v___x_4207_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4185_, v___x_4189_, v___x_4191_, v___x_4192_, v___x_4188_, v___x_4183_, v_mvarId_4159_, v___x_4184_, v_declName_4158_, v___x_4206_, v_a_4161_, v_a_4162_, v_a_4163_);
lean_dec_ref_known(v___x_4206_, 7);
v___y_4166_ = v___x_4207_;
goto v___jp_4165_;
}
else
{
lean_object* v___x_4208_; 
v___x_4208_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4185_, v___x_4189_, v___x_4191_, v___x_4192_, v___x_4188_, v___x_4183_, v_mvarId_4159_, v___x_4184_, v_declName_4158_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
v___y_4166_ = v___x_4208_;
goto v___jp_4165_;
}
v___jp_4165_:
{
if (lean_obj_tag(v___y_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
v_a_4167_ = lean_ctor_get(v___y_4166_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___y_4166_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___y_4166_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___y_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
v_a_4175_ = lean_ctor_get(v___y_4166_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___y_4166_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___y_4166_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___y_4166_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___boxed(lean_object* v_declName_4209_, lean_object* v_mvarId_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4209_, v_mvarId_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(lean_object* v_e_4217_, lean_object* v_k_4218_, uint8_t v_cleanupAnnotations_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v___f_4225_; uint8_t v___x_4226_; uint8_t v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___f_4225_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4225_, 0, v_k_4218_);
v___x_4226_ = 1;
v___x_4227_ = 0;
v___x_4228_ = lean_box(0);
v___x_4229_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4217_, v___x_4226_, v___x_4227_, v___x_4226_, v___x_4227_, v___x_4228_, v___f_4225_, v_cleanupAnnotations_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4229_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
v_a_4238_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_4229_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4229_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg___boxed(lean_object* v_e_4246_, lean_object* v_k_4247_, lean_object* v_cleanupAnnotations_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4254_; lean_object* v_res_4255_; 
v_cleanupAnnotations_boxed_4254_ = lean_unbox(v_cleanupAnnotations_4248_);
v_res_4255_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4246_, v_k_4247_, v_cleanupAnnotations_boxed_4254_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_object* v_00_u03b1_4256_, lean_object* v_e_4257_, lean_object* v_k_4258_, uint8_t v_cleanupAnnotations_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4257_, v_k_4258_, v_cleanupAnnotations_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed(lean_object* v_00_u03b1_4266_, lean_object* v_e_4267_, lean_object* v_k_4268_, lean_object* v_cleanupAnnotations_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4275_; lean_object* v_res_4276_; 
v_cleanupAnnotations_boxed_4275_ = lean_unbox(v_cleanupAnnotations_4269_);
v_res_4276_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(v_00_u03b1_4266_, v_e_4267_, v_k_4268_, v_cleanupAnnotations_boxed_4275_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(lean_object* v_opts_4277_, lean_object* v_opt_4278_){
_start:
{
lean_object* v_name_4279_; lean_object* v_defValue_4280_; lean_object* v_map_4281_; lean_object* v___x_4282_; 
v_name_4279_ = lean_ctor_get(v_opt_4278_, 0);
v_defValue_4280_ = lean_ctor_get(v_opt_4278_, 1);
v_map_4281_ = lean_ctor_get(v_opts_4277_, 0);
v___x_4282_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4281_, v_name_4279_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_inc(v_defValue_4280_);
return v_defValue_4280_;
}
else
{
lean_object* v_val_4283_; 
v_val_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_val_4283_);
lean_dec_ref_known(v___x_4282_, 1);
if (lean_obj_tag(v_val_4283_) == 3)
{
lean_object* v_v_4284_; 
v_v_4284_ = lean_ctor_get(v_val_4283_, 0);
lean_inc(v_v_4284_);
lean_dec_ref_known(v_val_4283_, 1);
return v_v_4284_;
}
else
{
lean_dec(v_val_4283_);
lean_inc(v_defValue_4280_);
return v_defValue_4280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed(lean_object* v_opts_4285_, lean_object* v_opt_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_opts_4285_, v_opt_4286_);
lean_dec_ref(v_opt_4286_);
lean_dec_ref(v_opts_4285_);
return v_res_4287_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4288_; double v___x_4289_; 
v___x_4288_ = lean_unsigned_to_nat(0u);
v___x_4289_ = lean_float_of_nat(v___x_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(lean_object* v_cls_4293_, lean_object* v_msg_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v_ref_4300_; lean_object* v___x_4301_; lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4347_; 
v_ref_4300_ = lean_ctor_get(v___y_4297_, 2);
v___x_4301_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4304_ = v___x_4301_;
v_isShared_4305_ = v_isSharedCheck_4347_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4301_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4347_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4306_; lean_object* v_traceState_4307_; lean_object* v_env_4308_; lean_object* v_nextMacroScope_4309_; lean_object* v_ngen_4310_; lean_object* v_auxDeclNGen_4311_; lean_object* v_cache_4312_; lean_object* v_recordedDeps_4313_; lean_object* v_messages_4314_; lean_object* v_infoState_4315_; lean_object* v_snapshotTasks_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4346_; 
v___x_4306_ = lean_st_ref_take(v___y_4298_);
v_traceState_4307_ = lean_ctor_get(v___x_4306_, 4);
v_env_4308_ = lean_ctor_get(v___x_4306_, 0);
v_nextMacroScope_4309_ = lean_ctor_get(v___x_4306_, 1);
v_ngen_4310_ = lean_ctor_get(v___x_4306_, 2);
v_auxDeclNGen_4311_ = lean_ctor_get(v___x_4306_, 3);
v_cache_4312_ = lean_ctor_get(v___x_4306_, 5);
v_recordedDeps_4313_ = lean_ctor_get(v___x_4306_, 6);
v_messages_4314_ = lean_ctor_get(v___x_4306_, 7);
v_infoState_4315_ = lean_ctor_get(v___x_4306_, 8);
v_snapshotTasks_4316_ = lean_ctor_get(v___x_4306_, 9);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4318_ = v___x_4306_;
v_isShared_4319_ = v_isSharedCheck_4346_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_snapshotTasks_4316_);
lean_inc(v_infoState_4315_);
lean_inc(v_messages_4314_);
lean_inc(v_recordedDeps_4313_);
lean_inc(v_cache_4312_);
lean_inc(v_traceState_4307_);
lean_inc(v_auxDeclNGen_4311_);
lean_inc(v_ngen_4310_);
lean_inc(v_nextMacroScope_4309_);
lean_inc(v_env_4308_);
lean_dec(v___x_4306_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4346_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
uint64_t v_tid_4320_; lean_object* v_traces_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4345_; 
v_tid_4320_ = lean_ctor_get_uint64(v_traceState_4307_, sizeof(void*)*1);
v_traces_4321_ = lean_ctor_get(v_traceState_4307_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v_traceState_4307_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4323_ = v_traceState_4307_;
v_isShared_4324_ = v_isSharedCheck_4345_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_traces_4321_);
lean_dec(v_traceState_4307_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4345_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; double v___x_4327_; uint8_t v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4336_; 
v___x_4325_ = lean_box(0);
v___x_4326_ = lean_box(0);
v___x_4327_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0);
v___x_4328_ = 0;
v___x_4329_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__1));
v___x_4330_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4330_, 0, v_cls_4293_);
lean_ctor_set(v___x_4330_, 1, v___x_4326_);
lean_ctor_set(v___x_4330_, 2, v___x_4329_);
lean_ctor_set_float(v___x_4330_, sizeof(void*)*3, v___x_4327_);
lean_ctor_set_float(v___x_4330_, sizeof(void*)*3 + 8, v___x_4327_);
lean_ctor_set_uint8(v___x_4330_, sizeof(void*)*3 + 16, v___x_4328_);
v___x_4331_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__2));
v___x_4332_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4330_);
lean_ctor_set(v___x_4332_, 1, v_a_4302_);
lean_ctor_set(v___x_4332_, 2, v___x_4331_);
lean_inc(v_ref_4300_);
v___x_4333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4333_, 0, v_ref_4300_);
lean_ctor_set(v___x_4333_, 1, v___x_4332_);
v___x_4334_ = l_Lean_PersistentArray_push___redArg(v_traces_4321_, v___x_4333_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 0, v___x_4334_);
v___x_4336_ = v___x_4323_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4334_);
lean_ctor_set_uint64(v_reuseFailAlloc_4344_, sizeof(void*)*1, v_tid_4320_);
v___x_4336_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
lean_object* v___x_4338_; 
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 4, v___x_4336_);
v___x_4338_ = v___x_4318_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_env_4308_);
lean_ctor_set(v_reuseFailAlloc_4343_, 1, v_nextMacroScope_4309_);
lean_ctor_set(v_reuseFailAlloc_4343_, 2, v_ngen_4310_);
lean_ctor_set(v_reuseFailAlloc_4343_, 3, v_auxDeclNGen_4311_);
lean_ctor_set(v_reuseFailAlloc_4343_, 4, v___x_4336_);
lean_ctor_set(v_reuseFailAlloc_4343_, 5, v_cache_4312_);
lean_ctor_set(v_reuseFailAlloc_4343_, 6, v_recordedDeps_4313_);
lean_ctor_set(v_reuseFailAlloc_4343_, 7, v_messages_4314_);
lean_ctor_set(v_reuseFailAlloc_4343_, 8, v_infoState_4315_);
lean_ctor_set(v_reuseFailAlloc_4343_, 9, v_snapshotTasks_4316_);
v___x_4338_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
lean_object* v___x_4339_; lean_object* v___x_4341_; 
v___x_4339_ = lean_st_ref_put(v___y_4298_, v___x_4338_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v___x_4325_);
v___x_4341_ = v___x_4304_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4325_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___boxed(lean_object* v_cls_4348_, lean_object* v_msg_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v_cls_4348_, v_msg_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
return v_res_4355_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4365_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4366_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4367_ = l_Lean_Name_append(v___x_4366_, v___x_4365_);
return v___x_4367_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4369_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__6));
v___x_4370_ = l_Lean_stringToMessageData(v___x_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object* v_levelParams_4371_, lean_object* v_declName_4372_, lean_object* v_wfPreprocessProof_4373_, lean_object* v___x_4374_, lean_object* v_unaryPreDefName_4375_, lean_object* v_xs_4376_, lean_object* v_body_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4386_ = lean_box(0);
lean_inc(v_levelParams_4371_);
v___x_4387_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4371_, v___x_4386_);
lean_inc(v_declName_4372_);
v___x_4388_ = l_Lean_mkConst(v_declName_4372_, v___x_4387_);
v___x_4389_ = l_Lean_mkAppN(v___x_4388_, v_xs_4376_);
v___x_4390_ = l_Lean_Meta_mkEq(v___x_4389_, v_body_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc_n(v_a_4391_, 2);
lean_dec_ref_known(v___x_4390_, 1);
v___x_4392_ = lean_box(0);
v___x_4393_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4391_, v___x_4392_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc(v_a_4394_);
lean_dec_ref_known(v___x_4393_, 1);
v___x_4395_ = l_Lean_Expr_mvarId_x21(v_a_4394_);
v___x_4396_ = l_Lean_Meta_Simp_Result_addExtraArgs(v_wfPreprocessProof_4373_, v_xs_4376_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; uint8_t v___x_4400_; lean_object* v_mvarId_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_a_4397_);
lean_dec_ref_known(v___x_4396_, 1);
v___x_4398_ = l_Lean_Expr_appFn_x21(v_a_4391_);
v___x_4399_ = lean_box(0);
v___x_4400_ = 1;
v___x_4475_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4475_, 0, v___x_4398_);
lean_ctor_set(v___x_4475_, 1, v___x_4399_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*2, v___x_4400_);
v___x_4476_ = l_Lean_Meta_Simp_mkCongr(v___x_4475_, v_a_4397_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4478_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref_known(v___x_4476_, 1);
v___x_4478_ = l_Lean_Meta_applySimpResultToTarget(v___x_4395_, v_a_4391_, v_a_4477_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v_a_4479_; uint8_t v___x_4480_; 
v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4479_);
lean_dec_ref_known(v___x_4478_, 1);
v___x_4480_ = lean_name_eq(v_declName_4372_, v_unaryPreDefName_4375_);
if (v___x_4480_ == 0)
{
lean_object* v___x_4481_; 
v___x_4481_ = l_Lean_Elab_Eqns_deltaLHS(v_a_4479_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v___x_4481_, 1);
v_mvarId_4402_ = v_a_4482_;
v___y_4403_ = v___y_4378_;
v___y_4404_ = v___y_4379_;
v___y_4405_ = v___y_4380_;
v___y_4406_ = v___y_4381_;
goto v___jp_4401_;
}
else
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4490_; 
lean_dec(v_a_4394_);
lean_dec(v_a_4391_);
lean_dec(v___x_4374_);
lean_dec(v_declName_4372_);
lean_dec(v_levelParams_4371_);
v_a_4483_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4485_ = v___x_4481_;
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v___x_4481_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4488_; 
if (v_isShared_4486_ == 0)
{
v___x_4488_ = v___x_4485_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4483_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
}
}
else
{
v_mvarId_4402_ = v_a_4479_;
v___y_4403_ = v___y_4378_;
v___y_4404_ = v___y_4379_;
v___y_4405_ = v___y_4380_;
v___y_4406_ = v___y_4381_;
goto v___jp_4401_;
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
lean_dec(v_a_4394_);
lean_dec(v_a_4391_);
lean_dec(v___x_4374_);
lean_dec(v_declName_4372_);
lean_dec(v_levelParams_4371_);
v_a_4491_ = lean_ctor_get(v___x_4478_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4478_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4478_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
lean_dec(v___x_4395_);
lean_dec(v_a_4394_);
lean_dec(v_a_4391_);
lean_dec(v___x_4374_);
lean_dec(v_declName_4372_);
lean_dec(v_levelParams_4371_);
v_a_4499_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4476_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4476_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4499_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
v___jp_4401_:
{
lean_object* v___x_4407_; 
v___x_4407_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4409_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_a_4408_);
lean_dec_ref_known(v___x_4407_, 1);
v___x_4409_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4372_, v_a_4408_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v___x_4410_; lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4466_; 
lean_dec_ref_known(v___x_4409_, 1);
v___x_4410_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4394_, v___y_4404_);
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4413_ = v___x_4410_;
v_isShared_4414_ = v_isSharedCheck_4466_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4410_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4466_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
uint8_t v___x_4415_; uint8_t v___x_4416_; lean_object* v___x_4417_; 
v___x_4415_ = 0;
v___x_4416_ = 1;
v___x_4417_ = l_Lean_Meta_mkForallFVars(v_xs_4376_, v_a_4391_, v___x_4415_, v___x_4400_, v___x_4400_, v___x_4416_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v___x_4419_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4417_, 1);
v___x_4419_ = l_Lean_Meta_letToHave(v_a_4418_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v___x_4421_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___x_4419_, 1);
v___x_4421_ = l_Lean_Meta_mkLambdaFVars(v_xs_4376_, v_a_4411_, v___x_4415_, v___x_4400_, v___x_4415_, v___x_4400_, v___x_4416_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4427_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v___x_4421_, 1);
lean_inc_n(v___x_4374_, 2);
v___x_4423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4374_);
lean_ctor_set(v___x_4423_, 1, v_levelParams_4371_);
lean_ctor_set(v___x_4423_, 2, v_a_4420_);
v___x_4424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4374_);
lean_ctor_set(v___x_4424_, 1, v___x_4386_);
v___x_4425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4423_);
lean_ctor_set(v___x_4425_, 1, v_a_4422_);
lean_ctor_set(v___x_4425_, 2, v___x_4424_);
if (v_isShared_4414_ == 0)
{
lean_ctor_set_tag(v___x_4413_, 2);
lean_ctor_set(v___x_4413_, 0, v___x_4425_);
v___x_4427_ = v___x_4413_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4425_);
v___x_4427_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
lean_object* v___x_4428_; 
v___x_4428_ = l_Lean_addDecl(v___x_4427_, v___x_4415_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v___x_4429_; 
lean_dec_ref_known(v___x_4428_, 1);
lean_inc(v___x_4374_);
v___x_4429_ = l_Lean_inferDefEqAttr(v___x_4374_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_toCold_4430_; lean_object* v_options_4431_; uint8_t v_hasTrace_4432_; 
lean_dec_ref_known(v___x_4429_, 1);
v_toCold_4430_ = lean_ctor_get(v___y_4405_, 0);
v_options_4431_ = lean_ctor_get(v_toCold_4430_, 2);
v_hasTrace_4432_ = lean_ctor_get_uint8(v_options_4431_, sizeof(void*)*1);
if (v_hasTrace_4432_ == 0)
{
lean_dec(v___x_4374_);
goto v___jp_4383_;
}
else
{
lean_object* v_inheritedTraceOptions_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; 
v_inheritedTraceOptions_4433_ = lean_ctor_get(v_toCold_4430_, 11);
v___x_4434_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4435_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_4436_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4433_, v_options_4431_, v___x_4435_);
if (v___x_4436_ == 0)
{
lean_dec(v___x_4374_);
goto v___jp_4383_;
}
else
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4437_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7);
v___x_4438_ = l_Lean_MessageData_ofConstName(v___x_4374_, v___x_4415_);
v___x_4439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4437_);
lean_ctor_set(v___x_4439_, 1, v___x_4438_);
v___x_4440_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_4434_, v___x_4439_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
return v___x_4440_;
}
}
}
else
{
lean_dec(v___x_4374_);
return v___x_4429_;
}
}
else
{
lean_dec(v___x_4374_);
return v___x_4428_;
}
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_dec(v_a_4420_);
lean_del_object(v___x_4413_);
lean_dec(v___x_4374_);
lean_dec(v_levelParams_4371_);
v_a_4442_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4421_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4421_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_del_object(v___x_4413_);
lean_dec(v_a_4411_);
lean_dec(v___x_4374_);
lean_dec(v_levelParams_4371_);
v_a_4450_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4419_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4419_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
else
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_del_object(v___x_4413_);
lean_dec(v_a_4411_);
lean_dec(v___x_4374_);
lean_dec(v_levelParams_4371_);
v_a_4458_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4417_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4417_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
else
{
lean_dec(v_a_4394_);
lean_dec(v_a_4391_);
lean_dec(v___x_4374_);
lean_dec(v_levelParams_4371_);
return v___x_4409_;
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_dec(v_a_4394_);
lean_dec(v_a_4391_);
lean_dec(v___x_4374_);
lean_dec(v_declName_4372_);
lean_dec(v_levelParams_4371_);
v_a_4467_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4407_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4407_);
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
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
lean_dec(v___x_4395_);
lean_dec(v_a_4394_);
lean_dec(v_a_4391_);
lean_dec(v___x_4374_);
lean_dec(v_declName_4372_);
lean_dec(v_levelParams_4371_);
v_a_4507_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4396_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4396_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
lean_dec(v_a_4391_);
lean_dec(v___x_4374_);
lean_dec_ref(v_wfPreprocessProof_4373_);
lean_dec(v_declName_4372_);
lean_dec(v_levelParams_4371_);
v_a_4515_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4393_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4393_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
lean_dec(v___x_4374_);
lean_dec_ref(v_wfPreprocessProof_4373_);
lean_dec(v_declName_4372_);
lean_dec(v_levelParams_4371_);
v_a_4523_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4390_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4390_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
v___jp_4383_:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4384_ = lean_box(0);
v___x_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
return v___x_4385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object* v_levelParams_4531_, lean_object* v_declName_4532_, lean_object* v_wfPreprocessProof_4533_, lean_object* v___x_4534_, lean_object* v_unaryPreDefName_4535_, lean_object* v_xs_4536_, lean_object* v_body_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l_Lean_Elab_WF_mkUnfoldEq___lam__0(v_levelParams_4531_, v_declName_4532_, v_wfPreprocessProof_4533_, v___x_4534_, v_unaryPreDefName_4535_, v_xs_4536_, v_body_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec_ref(v_xs_4536_);
lean_dec(v_unaryPreDefName_4535_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(lean_object* v___y_4544_, uint8_t v_isExporting_4545_, lean_object* v___x_4546_, lean_object* v___y_4547_, lean_object* v___x_4548_, lean_object* v_a_x3f_4549_){
_start:
{
lean_object* v___x_4551_; lean_object* v_env_4552_; lean_object* v_nextMacroScope_4553_; lean_object* v_ngen_4554_; lean_object* v_auxDeclNGen_4555_; lean_object* v_traceState_4556_; lean_object* v_recordedDeps_4557_; lean_object* v_messages_4558_; lean_object* v_infoState_4559_; lean_object* v_snapshotTasks_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4585_; 
v___x_4551_ = lean_st_ref_take(v___y_4544_);
v_env_4552_ = lean_ctor_get(v___x_4551_, 0);
v_nextMacroScope_4553_ = lean_ctor_get(v___x_4551_, 1);
v_ngen_4554_ = lean_ctor_get(v___x_4551_, 2);
v_auxDeclNGen_4555_ = lean_ctor_get(v___x_4551_, 3);
v_traceState_4556_ = lean_ctor_get(v___x_4551_, 4);
v_recordedDeps_4557_ = lean_ctor_get(v___x_4551_, 6);
v_messages_4558_ = lean_ctor_get(v___x_4551_, 7);
v_infoState_4559_ = lean_ctor_get(v___x_4551_, 8);
v_snapshotTasks_4560_ = lean_ctor_get(v___x_4551_, 9);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4585_ == 0)
{
lean_object* v_unused_4586_; 
v_unused_4586_ = lean_ctor_get(v___x_4551_, 5);
lean_dec(v_unused_4586_);
v___x_4562_ = v___x_4551_;
v_isShared_4563_ = v_isSharedCheck_4585_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_snapshotTasks_4560_);
lean_inc(v_infoState_4559_);
lean_inc(v_messages_4558_);
lean_inc(v_recordedDeps_4557_);
lean_inc(v_traceState_4556_);
lean_inc(v_auxDeclNGen_4555_);
lean_inc(v_ngen_4554_);
lean_inc(v_nextMacroScope_4553_);
lean_inc(v_env_4552_);
lean_dec(v___x_4551_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4585_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4564_; lean_object* v___x_4566_; 
v___x_4564_ = l_Lean_Environment_setExporting(v_env_4552_, v_isExporting_4545_);
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 5, v___x_4546_);
lean_ctor_set(v___x_4562_, 0, v___x_4564_);
v___x_4566_ = v___x_4562_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4564_);
lean_ctor_set(v_reuseFailAlloc_4584_, 1, v_nextMacroScope_4553_);
lean_ctor_set(v_reuseFailAlloc_4584_, 2, v_ngen_4554_);
lean_ctor_set(v_reuseFailAlloc_4584_, 3, v_auxDeclNGen_4555_);
lean_ctor_set(v_reuseFailAlloc_4584_, 4, v_traceState_4556_);
lean_ctor_set(v_reuseFailAlloc_4584_, 5, v___x_4546_);
lean_ctor_set(v_reuseFailAlloc_4584_, 6, v_recordedDeps_4557_);
lean_ctor_set(v_reuseFailAlloc_4584_, 7, v_messages_4558_);
lean_ctor_set(v_reuseFailAlloc_4584_, 8, v_infoState_4559_);
lean_ctor_set(v_reuseFailAlloc_4584_, 9, v_snapshotTasks_4560_);
v___x_4566_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v_mctx_4569_; lean_object* v_zetaDeltaFVarIds_4570_; lean_object* v_postponed_4571_; lean_object* v_diag_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4582_; 
v___x_4567_ = lean_st_ref_put(v___y_4544_, v___x_4566_);
v___x_4568_ = lean_st_ref_take(v___y_4547_);
v_mctx_4569_ = lean_ctor_get(v___x_4568_, 0);
v_zetaDeltaFVarIds_4570_ = lean_ctor_get(v___x_4568_, 2);
v_postponed_4571_ = lean_ctor_get(v___x_4568_, 3);
v_diag_4572_ = lean_ctor_get(v___x_4568_, 4);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4582_ == 0)
{
lean_object* v_unused_4583_; 
v_unused_4583_ = lean_ctor_get(v___x_4568_, 1);
lean_dec(v_unused_4583_);
v___x_4574_ = v___x_4568_;
v_isShared_4575_ = v_isSharedCheck_4582_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_diag_4572_);
lean_inc(v_postponed_4571_);
lean_inc(v_zetaDeltaFVarIds_4570_);
lean_inc(v_mctx_4569_);
lean_dec(v___x_4568_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4582_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4576_; lean_object* v___x_4578_; 
v___x_4576_ = lean_box(0);
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 1, v___x_4548_);
v___x_4578_ = v___x_4574_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_mctx_4569_);
lean_ctor_set(v_reuseFailAlloc_4581_, 1, v___x_4548_);
lean_ctor_set(v_reuseFailAlloc_4581_, 2, v_zetaDeltaFVarIds_4570_);
lean_ctor_set(v_reuseFailAlloc_4581_, 3, v_postponed_4571_);
lean_ctor_set(v_reuseFailAlloc_4581_, 4, v_diag_4572_);
v___x_4578_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4579_ = lean_st_ref_put(v___y_4547_, v___x_4578_);
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4576_);
return v___x_4580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v___y_4587_, lean_object* v_isExporting_4588_, lean_object* v___x_4589_, lean_object* v___y_4590_, lean_object* v___x_4591_, lean_object* v_a_x3f_4592_, lean_object* v___y_4593_){
_start:
{
uint8_t v_isExporting_boxed_4594_; lean_object* v_res_4595_; 
v_isExporting_boxed_4594_ = lean_unbox(v_isExporting_4588_);
v_res_4595_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(v___y_4587_, v_isExporting_boxed_4594_, v___x_4589_, v___y_4590_, v___x_4591_, v_a_x3f_4592_);
lean_dec(v_a_x3f_4592_);
lean_dec(v___y_4590_);
lean_dec(v___y_4587_);
return v_res_4595_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
return v___x_4597_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0);
v___x_4599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
return v___x_4599_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4600_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0);
v___x_4601_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
lean_ctor_set(v___x_4601_, 2, v___x_4600_);
lean_ctor_set(v___x_4601_, 3, v___x_4600_);
lean_ctor_set(v___x_4601_, 4, v___x_4600_);
lean_ctor_set(v___x_4601_, 5, v___x_4600_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(lean_object* v_x_4602_, uint8_t v_isExporting_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_){
_start:
{
lean_object* v___x_4609_; lean_object* v_env_4610_; lean_object* v___x_4611_; uint8_t v_isModule_4612_; 
v___x_4609_ = lean_st_ref_get(v___y_4607_);
v_env_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc_ref(v_env_4610_);
lean_dec(v___x_4609_);
v___x_4611_ = l_Lean_Environment_header(v_env_4610_);
v_isModule_4612_ = lean_ctor_get_uint8(v___x_4611_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4611_);
if (v_isModule_4612_ == 0)
{
lean_object* v___x_4613_; 
lean_dec_ref(v_env_4610_);
lean_inc(v___y_4607_);
lean_inc_ref(v___y_4606_);
lean_inc(v___y_4605_);
lean_inc_ref(v___y_4604_);
v___x_4613_ = lean_apply_5(v_x_4602_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, lean_box(0));
return v___x_4613_;
}
else
{
uint8_t v_isExporting_4614_; 
v_isExporting_4614_ = lean_ctor_get_uint8(v_env_4610_, sizeof(void*)*13);
lean_dec_ref(v_env_4610_);
if (v_isExporting_4603_ == 0)
{
if (v_isExporting_4614_ == 0)
{
lean_object* v___x_4681_; 
lean_inc(v___y_4607_);
lean_inc_ref(v___y_4606_);
lean_inc(v___y_4605_);
lean_inc_ref(v___y_4604_);
v___x_4681_ = lean_apply_5(v_x_4602_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, lean_box(0));
return v___x_4681_;
}
else
{
goto v___jp_4615_;
}
}
else
{
if (v_isExporting_4614_ == 0)
{
goto v___jp_4615_;
}
else
{
lean_object* v___x_4682_; 
lean_inc(v___y_4607_);
lean_inc_ref(v___y_4606_);
lean_inc(v___y_4605_);
lean_inc_ref(v___y_4604_);
v___x_4682_ = lean_apply_5(v_x_4602_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, lean_box(0));
return v___x_4682_;
}
}
v___jp_4615_:
{
lean_object* v___x_4616_; lean_object* v_env_4617_; lean_object* v_nextMacroScope_4618_; lean_object* v_ngen_4619_; lean_object* v_auxDeclNGen_4620_; lean_object* v_traceState_4621_; lean_object* v_recordedDeps_4622_; lean_object* v_messages_4623_; lean_object* v_infoState_4624_; lean_object* v_snapshotTasks_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4679_; 
v___x_4616_ = lean_st_ref_take(v___y_4607_);
v_env_4617_ = lean_ctor_get(v___x_4616_, 0);
v_nextMacroScope_4618_ = lean_ctor_get(v___x_4616_, 1);
v_ngen_4619_ = lean_ctor_get(v___x_4616_, 2);
v_auxDeclNGen_4620_ = lean_ctor_get(v___x_4616_, 3);
v_traceState_4621_ = lean_ctor_get(v___x_4616_, 4);
v_recordedDeps_4622_ = lean_ctor_get(v___x_4616_, 6);
v_messages_4623_ = lean_ctor_get(v___x_4616_, 7);
v_infoState_4624_ = lean_ctor_get(v___x_4616_, 8);
v_snapshotTasks_4625_ = lean_ctor_get(v___x_4616_, 9);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4679_ == 0)
{
lean_object* v_unused_4680_; 
v_unused_4680_ = lean_ctor_get(v___x_4616_, 5);
lean_dec(v_unused_4680_);
v___x_4627_ = v___x_4616_;
v_isShared_4628_ = v_isSharedCheck_4679_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_snapshotTasks_4625_);
lean_inc(v_infoState_4624_);
lean_inc(v_messages_4623_);
lean_inc(v_recordedDeps_4622_);
lean_inc(v_traceState_4621_);
lean_inc(v_auxDeclNGen_4620_);
lean_inc(v_ngen_4619_);
lean_inc(v_nextMacroScope_4618_);
lean_inc(v_env_4617_);
lean_dec(v___x_4616_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4679_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4632_; 
v___x_4629_ = l_Lean_Environment_setExporting(v_env_4617_, v_isExporting_4603_);
v___x_4630_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1);
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 5, v___x_4630_);
lean_ctor_set(v___x_4627_, 0, v___x_4629_);
v___x_4632_ = v___x_4627_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v___x_4629_);
lean_ctor_set(v_reuseFailAlloc_4678_, 1, v_nextMacroScope_4618_);
lean_ctor_set(v_reuseFailAlloc_4678_, 2, v_ngen_4619_);
lean_ctor_set(v_reuseFailAlloc_4678_, 3, v_auxDeclNGen_4620_);
lean_ctor_set(v_reuseFailAlloc_4678_, 4, v_traceState_4621_);
lean_ctor_set(v_reuseFailAlloc_4678_, 5, v___x_4630_);
lean_ctor_set(v_reuseFailAlloc_4678_, 6, v_recordedDeps_4622_);
lean_ctor_set(v_reuseFailAlloc_4678_, 7, v_messages_4623_);
lean_ctor_set(v_reuseFailAlloc_4678_, 8, v_infoState_4624_);
lean_ctor_set(v_reuseFailAlloc_4678_, 9, v_snapshotTasks_4625_);
v___x_4632_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v_mctx_4635_; lean_object* v_zetaDeltaFVarIds_4636_; lean_object* v_postponed_4637_; lean_object* v_diag_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4676_; 
v___x_4633_ = lean_st_ref_put(v___y_4607_, v___x_4632_);
v___x_4634_ = lean_st_ref_take(v___y_4605_);
v_mctx_4635_ = lean_ctor_get(v___x_4634_, 0);
v_zetaDeltaFVarIds_4636_ = lean_ctor_get(v___x_4634_, 2);
v_postponed_4637_ = lean_ctor_get(v___x_4634_, 3);
v_diag_4638_ = lean_ctor_get(v___x_4634_, 4);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4676_ == 0)
{
lean_object* v_unused_4677_; 
v_unused_4677_ = lean_ctor_get(v___x_4634_, 1);
lean_dec(v_unused_4677_);
v___x_4640_ = v___x_4634_;
v_isShared_4641_ = v_isSharedCheck_4676_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_diag_4638_);
lean_inc(v_postponed_4637_);
lean_inc(v_zetaDeltaFVarIds_4636_);
lean_inc(v_mctx_4635_);
lean_dec(v___x_4634_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4676_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4642_; lean_object* v___x_4644_; 
v___x_4642_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 1, v___x_4642_);
v___x_4644_ = v___x_4640_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_mctx_4635_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v___x_4642_);
lean_ctor_set(v_reuseFailAlloc_4675_, 2, v_zetaDeltaFVarIds_4636_);
lean_ctor_set(v_reuseFailAlloc_4675_, 3, v_postponed_4637_);
lean_ctor_set(v_reuseFailAlloc_4675_, 4, v_diag_4638_);
v___x_4644_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; lean_object* v_r_4646_; 
v___x_4645_ = lean_st_ref_put(v___y_4605_, v___x_4644_);
lean_inc(v___y_4607_);
lean_inc_ref(v___y_4606_);
lean_inc(v___y_4605_);
lean_inc_ref(v___y_4604_);
v_r_4646_ = lean_apply_5(v_x_4602_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, lean_box(0));
if (lean_obj_tag(v_r_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4663_; 
v_a_4647_ = lean_ctor_get(v_r_4646_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v_r_4646_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4649_ = v_r_4646_;
v_isShared_4650_ = v_isSharedCheck_4663_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v_r_4646_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4663_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
lean_inc(v_a_4647_);
if (v_isShared_4650_ == 0)
{
lean_ctor_set_tag(v___x_4649_, 1);
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_a_4647_);
v___x_4652_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
lean_object* v___x_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4660_; 
v___x_4653_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(v___y_4607_, v_isExporting_4614_, v___x_4630_, v___y_4605_, v___x_4642_, v___x_4652_);
lean_dec_ref(v___x_4652_);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4660_ == 0)
{
lean_object* v_unused_4661_; 
v_unused_4661_ = lean_ctor_get(v___x_4653_, 0);
lean_dec(v_unused_4661_);
v___x_4655_ = v___x_4653_;
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
else
{
lean_dec(v___x_4653_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4658_; 
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 0, v_a_4647_);
v___x_4658_ = v___x_4655_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_a_4647_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
}
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
v_a_4664_ = lean_ctor_get(v_r_4646_, 0);
lean_inc(v_a_4664_);
lean_dec_ref_known(v_r_4646_, 1);
v___x_4665_ = lean_box(0);
v___x_4666_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(v___y_4607_, v_isExporting_4614_, v___x_4630_, v___y_4605_, v___x_4642_, v___x_4665_);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4673_ == 0)
{
lean_object* v_unused_4674_; 
v_unused_4674_ = lean_ctor_get(v___x_4666_, 0);
lean_dec(v_unused_4674_);
v___x_4668_ = v___x_4666_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_dec(v___x_4666_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
lean_ctor_set_tag(v___x_4668_, 1);
lean_ctor_set(v___x_4668_, 0, v_a_4664_);
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4664_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___boxed(lean_object* v_x_4683_, lean_object* v_isExporting_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
uint8_t v_isExporting_boxed_4690_; lean_object* v_res_4691_; 
v_isExporting_boxed_4690_ = lean_unbox(v_isExporting_4684_);
v_res_4691_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(v_x_4683_, v_isExporting_boxed_4690_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(lean_object* v_x_4692_, uint8_t v_when_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
if (v_when_4693_ == 0)
{
lean_object* v___x_4699_; 
lean_inc(v___y_4697_);
lean_inc_ref(v___y_4696_);
lean_inc(v___y_4695_);
lean_inc_ref(v___y_4694_);
v___x_4699_ = lean_apply_5(v_x_4692_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, lean_box(0));
return v___x_4699_;
}
else
{
uint8_t v___x_4700_; lean_object* v___x_4701_; 
v___x_4700_ = 0;
v___x_4701_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(v_x_4692_, v___x_4700_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
return v___x_4701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg___boxed(lean_object* v_x_4702_, lean_object* v_when_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
uint8_t v_when_boxed_4709_; lean_object* v_res_4710_; 
v_when_boxed_4709_ = lean_unbox(v_when_4703_);
v_res_4710_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(v_x_4702_, v_when_boxed_4709_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5(lean_object* v_o_4711_, lean_object* v_k_4712_, uint8_t v_v_4713_){
_start:
{
lean_object* v_map_4714_; uint8_t v_hasTrace_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4729_; 
v_map_4714_ = lean_ctor_get(v_o_4711_, 0);
v_hasTrace_4715_ = lean_ctor_get_uint8(v_o_4711_, sizeof(void*)*1);
v_isSharedCheck_4729_ = !lean_is_exclusive(v_o_4711_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4717_ = v_o_4711_;
v_isShared_4718_ = v_isSharedCheck_4729_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_map_4714_);
lean_dec(v_o_4711_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4729_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4719_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4719_, 0, v_v_4713_);
lean_inc(v_k_4712_);
v___x_4720_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4712_, v___x_4719_, v_map_4714_);
if (v_hasTrace_4715_ == 0)
{
lean_object* v___x_4721_; uint8_t v___x_4722_; lean_object* v___x_4724_; 
v___x_4721_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4722_ = l_Lean_Name_isPrefixOf(v___x_4721_, v_k_4712_);
lean_dec(v_k_4712_);
if (v_isShared_4718_ == 0)
{
lean_ctor_set(v___x_4717_, 0, v___x_4720_);
v___x_4724_ = v___x_4717_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4720_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_ctor_set_uint8(v___x_4724_, sizeof(void*)*1, v___x_4722_);
return v___x_4724_;
}
}
else
{
lean_object* v___x_4727_; 
lean_dec(v_k_4712_);
if (v_isShared_4718_ == 0)
{
lean_ctor_set(v___x_4717_, 0, v___x_4720_);
v___x_4727_ = v___x_4717_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4720_);
lean_ctor_set_uint8(v_reuseFailAlloc_4728_, sizeof(void*)*1, v_hasTrace_4715_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5___boxed(lean_object* v_o_4730_, lean_object* v_k_4731_, lean_object* v_v_4732_){
_start:
{
uint8_t v_v_boxed_4733_; lean_object* v_res_4734_; 
v_v_boxed_4733_ = lean_unbox(v_v_4732_);
v_res_4734_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5(v_o_4730_, v_k_4731_, v_v_boxed_4733_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(lean_object* v_opts_4735_, lean_object* v_opt_4736_, uint8_t v_val_4737_){
_start:
{
lean_object* v_name_4738_; lean_object* v___x_4739_; 
v_name_4738_ = lean_ctor_get(v_opt_4736_, 0);
lean_inc(v_name_4738_);
lean_dec_ref(v_opt_4736_);
v___x_4739_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5(v_opts_4735_, v_name_4738_, v_val_4737_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4___boxed(lean_object* v_opts_4740_, lean_object* v_opt_4741_, lean_object* v_val_4742_){
_start:
{
uint8_t v_val_boxed_4743_; lean_object* v_res_4744_; 
v_val_boxed_4743_ = lean_unbox(v_val_4742_);
v_res_4744_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_opts_4740_, v_opt_4741_, v_val_boxed_4743_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(lean_object* v___x_4745_, uint8_t v___x_4746_, uint8_t v___x_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v___y_4754_; uint16_t v___y_4755_; lean_object* v_fileName_4756_; lean_object* v_fileMap_4757_; lean_object* v_currNamespace_4758_; lean_object* v_openDecls_4759_; lean_object* v_initHeartbeats_4760_; lean_object* v_maxHeartbeats_4761_; lean_object* v_quotContext_4762_; lean_object* v_currMacroScope_4763_; lean_object* v_cancelTk_x3f_4764_; lean_object* v_inheritedTraceOptions_4765_; lean_object* v_currRecDepth_4766_; lean_object* v_ref_4767_; uint8_t v_suppressElabErrors_4768_; uint8_t v_isRecordingDeps_4769_; lean_object* v___y_4770_; lean_object* v_toCold_4776_; lean_object* v_currRecDepth_4777_; lean_object* v_ref_4778_; uint8_t v_suppressElabErrors_4779_; uint8_t v_isRecordingDeps_4780_; lean_object* v_fileName_4781_; lean_object* v_fileMap_4782_; lean_object* v_options_4783_; lean_object* v_currNamespace_4784_; lean_object* v_openDecls_4785_; lean_object* v_initHeartbeats_4786_; lean_object* v_maxHeartbeats_4787_; lean_object* v_quotContext_4788_; lean_object* v_currMacroScope_4789_; lean_object* v_cancelTk_x3f_4790_; lean_object* v_inheritedTraceOptions_4791_; uint8_t v___y_4793_; lean_object* v___y_4794_; uint16_t v___y_4795_; lean_object* v___y_4818_; 
v_toCold_4776_ = lean_ctor_get(v___y_4750_, 0);
v_currRecDepth_4777_ = lean_ctor_get(v___y_4750_, 1);
v_ref_4778_ = lean_ctor_get(v___y_4750_, 2);
v_suppressElabErrors_4779_ = lean_ctor_get_uint8(v___y_4750_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4780_ = lean_ctor_get_uint8(v___y_4750_, sizeof(void*)*3 + 3);
v_fileName_4781_ = lean_ctor_get(v_toCold_4776_, 0);
v_fileMap_4782_ = lean_ctor_get(v_toCold_4776_, 1);
v_options_4783_ = lean_ctor_get(v_toCold_4776_, 2);
v_currNamespace_4784_ = lean_ctor_get(v_toCold_4776_, 4);
v_openDecls_4785_ = lean_ctor_get(v_toCold_4776_, 5);
v_initHeartbeats_4786_ = lean_ctor_get(v_toCold_4776_, 6);
v_maxHeartbeats_4787_ = lean_ctor_get(v_toCold_4776_, 7);
v_quotContext_4788_ = lean_ctor_get(v_toCold_4776_, 8);
v_currMacroScope_4789_ = lean_ctor_get(v_toCold_4776_, 9);
v_cancelTk_x3f_4790_ = lean_ctor_get(v_toCold_4776_, 10);
v_inheritedTraceOptions_4791_ = lean_ctor_get(v_toCold_4776_, 11);
if (v_isRecordingDeps_4780_ == 0)
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_4783_);
v___x_4828_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_options_4783_, v___x_4827_, v_isRecordingDeps_4780_);
v___y_4818_ = v___x_4828_;
goto v___jp_4817_;
}
else
{
lean_object* v___x_4829_; 
lean_inc_ref(v_options_4783_);
v___x_4829_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_4783_);
v___y_4818_ = v___x_4829_;
goto v___jp_4817_;
}
v___jp_4753_:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4771_ = l_Lean_maxRecDepth;
v___x_4772_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v___y_4754_, v___x_4771_);
v___x_4773_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4773_, 0, v_fileName_4756_);
lean_ctor_set(v___x_4773_, 1, v_fileMap_4757_);
lean_ctor_set(v___x_4773_, 2, v___y_4754_);
lean_ctor_set(v___x_4773_, 3, v___x_4772_);
lean_ctor_set(v___x_4773_, 4, v_currNamespace_4758_);
lean_ctor_set(v___x_4773_, 5, v_openDecls_4759_);
lean_ctor_set(v___x_4773_, 6, v_initHeartbeats_4760_);
lean_ctor_set(v___x_4773_, 7, v_maxHeartbeats_4761_);
lean_ctor_set(v___x_4773_, 8, v_quotContext_4762_);
lean_ctor_set(v___x_4773_, 9, v_currMacroScope_4763_);
lean_ctor_set(v___x_4773_, 10, v_cancelTk_x3f_4764_);
lean_ctor_set(v___x_4773_, 11, v_inheritedTraceOptions_4765_);
lean_inc(v_ref_4767_);
lean_inc(v_currRecDepth_4766_);
v___x_4774_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
lean_ctor_set(v___x_4774_, 1, v_currRecDepth_4766_);
lean_ctor_set(v___x_4774_, 2, v_ref_4767_);
lean_ctor_set_uint16(v___x_4774_, sizeof(void*)*3, v___y_4755_);
lean_ctor_set_uint8(v___x_4774_, sizeof(void*)*3 + 2, v_suppressElabErrors_4768_);
lean_ctor_set_uint8(v___x_4774_, sizeof(void*)*3 + 3, v_isRecordingDeps_4769_);
v___x_4775_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(v___x_4745_, v___x_4746_, v___y_4748_, v___y_4749_, v___x_4774_, v___y_4770_);
lean_dec_ref_known(v___x_4774_, 3);
return v___x_4775_;
}
v___jp_4792_:
{
lean_object* v___x_4796_; lean_object* v_env_4797_; lean_object* v_nextMacroScope_4798_; lean_object* v_ngen_4799_; lean_object* v_auxDeclNGen_4800_; lean_object* v_traceState_4801_; lean_object* v_recordedDeps_4802_; lean_object* v_messages_4803_; lean_object* v_infoState_4804_; lean_object* v_snapshotTasks_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4815_; 
v___x_4796_ = lean_st_ref_take(v___y_4751_);
v_env_4797_ = lean_ctor_get(v___x_4796_, 0);
v_nextMacroScope_4798_ = lean_ctor_get(v___x_4796_, 1);
v_ngen_4799_ = lean_ctor_get(v___x_4796_, 2);
v_auxDeclNGen_4800_ = lean_ctor_get(v___x_4796_, 3);
v_traceState_4801_ = lean_ctor_get(v___x_4796_, 4);
v_recordedDeps_4802_ = lean_ctor_get(v___x_4796_, 6);
v_messages_4803_ = lean_ctor_get(v___x_4796_, 7);
v_infoState_4804_ = lean_ctor_get(v___x_4796_, 8);
v_snapshotTasks_4805_ = lean_ctor_get(v___x_4796_, 9);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4815_ == 0)
{
lean_object* v_unused_4816_; 
v_unused_4816_ = lean_ctor_get(v___x_4796_, 5);
lean_dec(v_unused_4816_);
v___x_4807_ = v___x_4796_;
v_isShared_4808_ = v_isSharedCheck_4815_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_snapshotTasks_4805_);
lean_inc(v_infoState_4804_);
lean_inc(v_messages_4803_);
lean_inc(v_recordedDeps_4802_);
lean_inc(v_traceState_4801_);
lean_inc(v_auxDeclNGen_4800_);
lean_inc(v_ngen_4799_);
lean_inc(v_nextMacroScope_4798_);
lean_inc(v_env_4797_);
lean_dec(v___x_4796_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4815_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4812_; 
v___x_4809_ = l_Lean_Kernel_enableDiag(v_env_4797_, v___y_4793_);
v___x_4810_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 5, v___x_4810_);
lean_ctor_set(v___x_4807_, 0, v___x_4809_);
v___x_4812_ = v___x_4807_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4809_);
lean_ctor_set(v_reuseFailAlloc_4814_, 1, v_nextMacroScope_4798_);
lean_ctor_set(v_reuseFailAlloc_4814_, 2, v_ngen_4799_);
lean_ctor_set(v_reuseFailAlloc_4814_, 3, v_auxDeclNGen_4800_);
lean_ctor_set(v_reuseFailAlloc_4814_, 4, v_traceState_4801_);
lean_ctor_set(v_reuseFailAlloc_4814_, 5, v___x_4810_);
lean_ctor_set(v_reuseFailAlloc_4814_, 6, v_recordedDeps_4802_);
lean_ctor_set(v_reuseFailAlloc_4814_, 7, v_messages_4803_);
lean_ctor_set(v_reuseFailAlloc_4814_, 8, v_infoState_4804_);
lean_ctor_set(v_reuseFailAlloc_4814_, 9, v_snapshotTasks_4805_);
v___x_4812_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
lean_object* v___x_4813_; 
v___x_4813_ = lean_st_ref_put(v___y_4751_, v___x_4812_);
lean_inc_ref(v_inheritedTraceOptions_4791_);
lean_inc(v_cancelTk_x3f_4790_);
lean_inc(v_currMacroScope_4789_);
lean_inc(v_quotContext_4788_);
lean_inc(v_maxHeartbeats_4787_);
lean_inc(v_initHeartbeats_4786_);
lean_inc(v_openDecls_4785_);
lean_inc(v_currNamespace_4784_);
lean_inc_ref(v_fileMap_4782_);
lean_inc_ref(v_fileName_4781_);
v___y_4754_ = v___y_4794_;
v___y_4755_ = v___y_4795_;
v_fileName_4756_ = v_fileName_4781_;
v_fileMap_4757_ = v_fileMap_4782_;
v_currNamespace_4758_ = v_currNamespace_4784_;
v_openDecls_4759_ = v_openDecls_4785_;
v_initHeartbeats_4760_ = v_initHeartbeats_4786_;
v_maxHeartbeats_4761_ = v_maxHeartbeats_4787_;
v_quotContext_4762_ = v_quotContext_4788_;
v_currMacroScope_4763_ = v_currMacroScope_4789_;
v_cancelTk_x3f_4764_ = v_cancelTk_x3f_4790_;
v_inheritedTraceOptions_4765_ = v_inheritedTraceOptions_4791_;
v_currRecDepth_4766_ = v_currRecDepth_4777_;
v_ref_4767_ = v_ref_4778_;
v_suppressElabErrors_4768_ = v_suppressElabErrors_4779_;
v_isRecordingDeps_4769_ = v_isRecordingDeps_4780_;
v___y_4770_ = v___y_4751_;
goto v___jp_4753_;
}
}
}
v___jp_4817_:
{
uint16_t v___x_4819_; lean_object* v___x_4820_; lean_object* v_env_4821_; uint8_t v___x_4822_; uint16_t v___x_4823_; uint16_t v___x_4824_; uint16_t v___x_4825_; uint8_t v___x_4826_; 
v___x_4819_ = l_Lean_OptionFlags_ofOptions(v___y_4818_);
v___x_4820_ = lean_st_ref_get(v___y_4751_);
v_env_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc_ref(v_env_4821_);
lean_dec(v___x_4820_);
v___x_4822_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4821_);
lean_dec_ref(v_env_4821_);
v___x_4823_ = 1024;
v___x_4824_ = lean_uint16_land(v___x_4819_, v___x_4823_);
v___x_4825_ = 0;
v___x_4826_ = lean_uint16_dec_eq(v___x_4824_, v___x_4825_);
if (v___x_4826_ == 0)
{
if (v___x_4822_ == 0)
{
v___y_4793_ = v___x_4746_;
v___y_4794_ = v___y_4818_;
v___y_4795_ = v___x_4819_;
goto v___jp_4792_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_4791_);
lean_inc(v_cancelTk_x3f_4790_);
lean_inc(v_currMacroScope_4789_);
lean_inc(v_quotContext_4788_);
lean_inc(v_maxHeartbeats_4787_);
lean_inc(v_initHeartbeats_4786_);
lean_inc(v_openDecls_4785_);
lean_inc(v_currNamespace_4784_);
lean_inc_ref(v_fileMap_4782_);
lean_inc_ref(v_fileName_4781_);
v___y_4754_ = v___y_4818_;
v___y_4755_ = v___x_4819_;
v_fileName_4756_ = v_fileName_4781_;
v_fileMap_4757_ = v_fileMap_4782_;
v_currNamespace_4758_ = v_currNamespace_4784_;
v_openDecls_4759_ = v_openDecls_4785_;
v_initHeartbeats_4760_ = v_initHeartbeats_4786_;
v_maxHeartbeats_4761_ = v_maxHeartbeats_4787_;
v_quotContext_4762_ = v_quotContext_4788_;
v_currMacroScope_4763_ = v_currMacroScope_4789_;
v_cancelTk_x3f_4764_ = v_cancelTk_x3f_4790_;
v_inheritedTraceOptions_4765_ = v_inheritedTraceOptions_4791_;
v_currRecDepth_4766_ = v_currRecDepth_4777_;
v_ref_4767_ = v_ref_4778_;
v_suppressElabErrors_4768_ = v_suppressElabErrors_4779_;
v_isRecordingDeps_4769_ = v_isRecordingDeps_4780_;
v___y_4770_ = v___y_4751_;
goto v___jp_4753_;
}
}
else
{
if (v___x_4822_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_4791_);
lean_inc(v_cancelTk_x3f_4790_);
lean_inc(v_currMacroScope_4789_);
lean_inc(v_quotContext_4788_);
lean_inc(v_maxHeartbeats_4787_);
lean_inc(v_initHeartbeats_4786_);
lean_inc(v_openDecls_4785_);
lean_inc(v_currNamespace_4784_);
lean_inc_ref(v_fileMap_4782_);
lean_inc_ref(v_fileName_4781_);
v___y_4754_ = v___y_4818_;
v___y_4755_ = v___x_4819_;
v_fileName_4756_ = v_fileName_4781_;
v_fileMap_4757_ = v_fileMap_4782_;
v_currNamespace_4758_ = v_currNamespace_4784_;
v_openDecls_4759_ = v_openDecls_4785_;
v_initHeartbeats_4760_ = v_initHeartbeats_4786_;
v_maxHeartbeats_4761_ = v_maxHeartbeats_4787_;
v_quotContext_4762_ = v_quotContext_4788_;
v_currMacroScope_4763_ = v_currMacroScope_4789_;
v_cancelTk_x3f_4764_ = v_cancelTk_x3f_4790_;
v_inheritedTraceOptions_4765_ = v_inheritedTraceOptions_4791_;
v_currRecDepth_4766_ = v_currRecDepth_4777_;
v_ref_4767_ = v_ref_4778_;
v_suppressElabErrors_4768_ = v_suppressElabErrors_4779_;
v_isRecordingDeps_4769_ = v_isRecordingDeps_4780_;
v___y_4770_ = v___y_4751_;
goto v___jp_4753_;
}
else
{
v___y_4793_ = v___x_4747_;
v___y_4794_ = v___y_4818_;
v___y_4795_ = v___x_4819_;
goto v___jp_4792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object* v___x_4830_, lean_object* v___x_4831_, lean_object* v___x_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_){
_start:
{
uint8_t v___x_9822__boxed_4838_; uint8_t v___x_9823__boxed_4839_; lean_object* v_res_4840_; 
v___x_9822__boxed_4838_ = lean_unbox(v___x_4831_);
v___x_9823__boxed_4839_ = lean_unbox(v___x_4832_);
v_res_4840_ = l_Lean_Elab_WF_mkUnfoldEq___lam__2(v___x_4830_, v___x_9822__boxed_4838_, v___x_9823__boxed_4839_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
lean_dec(v___y_4834_);
lean_dec_ref(v___y_4833_);
return v_res_4840_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4842_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___closed__0));
v___x_4843_ = l_Lean_stringToMessageData(v___x_4842_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object* v_preDef_4844_, lean_object* v_unaryPreDefName_4845_, lean_object* v_wfPreprocessProof_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_){
_start:
{
lean_object* v___x_4852_; lean_object* v_env_4853_; lean_object* v_levelParams_4854_; lean_object* v_declName_4855_; lean_object* v_value_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___f_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___f_4863_; uint8_t v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; uint8_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___f_4870_; lean_object* v___x_4871_; 
v___x_4852_ = lean_st_ref_get(v_a_4850_);
v_env_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc_ref(v_env_4853_);
lean_dec(v___x_4852_);
v_levelParams_4854_ = lean_ctor_get(v_preDef_4844_, 1);
lean_inc(v_levelParams_4854_);
v_declName_4855_ = lean_ctor_get(v_preDef_4844_, 3);
lean_inc_n(v_declName_4855_, 2);
v_value_4856_ = lean_ctor_get(v_preDef_4844_, 7);
lean_inc_ref(v_value_4856_);
lean_dec_ref(v_preDef_4844_);
v___x_4857_ = l_Lean_Meta_unfoldThmSuffix;
v___x_4858_ = l_Lean_Meta_mkEqLikeNameFor(v_env_4853_, v_declName_4855_, v___x_4857_);
lean_inc(v___x_4858_);
v___f_4859_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4859_, 0, v_levelParams_4854_);
lean_closure_set(v___f_4859_, 1, v_declName_4855_);
lean_closure_set(v___f_4859_, 2, v_wfPreprocessProof_4846_);
lean_closure_set(v___f_4859_, 3, v___x_4858_);
lean_closure_set(v___f_4859_, 4, v_unaryPreDefName_4845_);
v___x_4860_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___closed__1, &l_Lean_Elab_WF_mkUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1);
v___x_4861_ = l_Lean_MessageData_ofName(v___x_4858_);
v___x_4862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4860_);
lean_ctor_set(v___x_4862_, 1, v___x_4861_);
v___f_4863_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4863_, 0, v___x_4862_);
v___x_4864_ = 0;
v___x_4865_ = lean_box(v___x_4864_);
v___x_4866_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed), 9, 4);
lean_closure_set(v___x_4866_, 0, lean_box(0));
lean_closure_set(v___x_4866_, 1, v_value_4856_);
lean_closure_set(v___x_4866_, 2, v___f_4859_);
lean_closure_set(v___x_4866_, 3, v___x_4865_);
v___x_4867_ = 1;
v___x_4868_ = lean_box(v___x_4867_);
v___x_4869_ = lean_box(v___x_4864_);
v___f_4870_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_4870_, 0, v___x_4866_);
lean_closure_set(v___f_4870_, 1, v___x_4868_);
lean_closure_set(v___f_4870_, 2, v___x_4869_);
v___x_4871_ = l_Lean_Meta_mapErrorImp___redArg(v___f_4870_, v___f_4863_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4871_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4871_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
else
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
v_a_4880_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4871_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4871_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___boxed(lean_object* v_preDef_4888_, lean_object* v_unaryPreDefName_4889_, lean_object* v_wfPreprocessProof_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_){
_start:
{
lean_object* v_res_4896_; 
v_res_4896_ = l_Lean_Elab_WF_mkUnfoldEq(v_preDef_4888_, v_unaryPreDefName_4889_, v_wfPreprocessProof_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
lean_dec(v_a_4894_);
lean_dec_ref(v_a_4893_);
lean_dec(v_a_4892_);
lean_dec_ref(v_a_4891_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(lean_object* v_00_u03b1_4897_, lean_object* v_x_4898_, uint8_t v_isExporting_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_){
_start:
{
lean_object* v___x_4905_; 
v___x_4905_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(v_x_4898_, v_isExporting_4899_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___boxed(lean_object* v_00_u03b1_4906_, lean_object* v_x_4907_, lean_object* v_isExporting_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
uint8_t v_isExporting_boxed_4914_; lean_object* v_res_4915_; 
v_isExporting_boxed_4914_ = lean_unbox(v_isExporting_4908_);
v_res_4915_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(v_00_u03b1_4906_, v_x_4907_, v_isExporting_boxed_4914_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object* v_00_u03b1_4916_, lean_object* v_x_4917_, uint8_t v_when_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_){
_start:
{
lean_object* v___x_4924_; 
v___x_4924_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(v_x_4917_, v_when_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object* v_00_u03b1_4925_, lean_object* v_x_4926_, lean_object* v_when_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_){
_start:
{
uint8_t v_when_boxed_4933_; lean_object* v_res_4934_; 
v_when_boxed_4933_ = lean_unbox(v_when_4927_);
v_res_4934_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v_00_u03b1_4925_, v_x_4926_, v_when_boxed_4933_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
return v_res_4934_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4936_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0));
v___x_4937_ = l_Lean_stringToMessageData(v___x_4936_);
return v___x_4937_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4943_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3));
v___x_4944_ = l_Lean_stringToMessageData(v___x_4943_);
return v___x_4944_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4946_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5));
v___x_4947_ = l_Lean_stringToMessageData(v___x_4946_);
return v___x_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object* v_levelParams_4948_, lean_object* v_declName_4949_, lean_object* v___x_4950_, lean_object* v___x_4951_, lean_object* v___x_4952_, lean_object* v_xs_4953_, lean_object* v_body_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_){
_start:
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4963_ = lean_box(0);
lean_inc(v_levelParams_4948_);
v___x_4964_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4948_, v___x_4963_);
v___x_4965_ = l_Lean_mkConst(v_declName_4949_, v___x_4964_);
v___x_4966_ = l_Lean_mkAppN(v___x_4965_, v_xs_4953_);
v___x_4967_ = l_Lean_Meta_mkEq(v___x_4966_, v_body_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc_n(v_a_4968_, 2);
lean_dec_ref_known(v___x_4967_, 1);
v___x_4969_ = lean_box(0);
v___x_4970_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4968_, v___x_4969_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_object* v_a_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
lean_inc(v_a_4971_);
lean_dec_ref_known(v___x_4970_, 1);
v___x_4972_ = l_Lean_Expr_mvarId_x21(v_a_4971_);
v___x_4973_ = l_Lean_Elab_Eqns_deltaLHS(v___x_4972_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v_a_4974_; uint8_t v___x_4975_; uint8_t v___x_4976_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
v_a_4974_ = lean_ctor_get(v___x_4973_, 0);
lean_inc_n(v_a_4974_, 2);
lean_dec_ref_known(v___x_4973_, 1);
v___x_4975_ = 1;
v___x_4976_ = 0;
v___x_5038_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2));
v___x_5039_ = l_Lean_MVarId_applyConst(v_a_4974_, v___x_4951_, v___x_5038_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
if (lean_obj_tag(v___x_5039_) == 0)
{
lean_object* v_a_5040_; uint8_t v___x_5041_; 
v_a_5040_ = lean_ctor_get(v___x_5039_, 0);
lean_inc(v_a_5040_);
lean_dec_ref_known(v___x_5039_, 1);
v___x_5041_ = l_List_isEmpty___redArg(v_a_5040_);
lean_dec(v_a_5040_);
if (v___x_5041_ == 0)
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
lean_dec(v_a_4971_);
lean_dec(v_a_4968_);
lean_dec(v___x_4950_);
lean_dec(v_levelParams_4948_);
v___x_5042_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4);
v___x_5043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5042_);
lean_ctor_set(v___x_5043_, 1, v___x_4952_);
v___x_5044_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6);
v___x_5045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5043_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
v___x_5046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5046_, 0, v_a_4974_);
v___x_5047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5047_, 0, v___x_5045_);
lean_ctor_set(v___x_5047_, 1, v___x_5046_);
v___x_5048_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5049_, 0, v___x_5047_);
lean_ctor_set(v___x_5049_, 1, v___x_5048_);
v___x_5050_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_5049_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
return v___x_5050_;
}
else
{
lean_dec(v_a_4974_);
lean_dec_ref(v___x_4952_);
v___y_4978_ = v___y_4955_;
v___y_4979_ = v___y_4956_;
v___y_4980_ = v___y_4957_;
v___y_4981_ = v___y_4958_;
goto v___jp_4977_;
}
}
else
{
lean_object* v_a_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5058_; 
lean_dec(v_a_4974_);
lean_dec(v_a_4971_);
lean_dec(v_a_4968_);
lean_dec_ref(v___x_4952_);
lean_dec(v___x_4950_);
lean_dec(v_levelParams_4948_);
v_a_5051_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5058_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5058_ == 0)
{
v___x_5053_ = v___x_5039_;
v_isShared_5054_ = v_isSharedCheck_5058_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_a_5051_);
lean_dec(v___x_5039_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5058_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v___x_5056_; 
if (v_isShared_5054_ == 0)
{
v___x_5056_ = v___x_5053_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_a_5051_);
v___x_5056_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
return v___x_5056_;
}
}
}
v___jp_4977_:
{
lean_object* v___x_4982_; lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_5037_; 
v___x_4982_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4971_, v___y_4979_);
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_4985_ = v___x_4982_;
v_isShared_4986_ = v_isSharedCheck_5037_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v___x_4982_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_5037_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
uint8_t v___x_4987_; lean_object* v___x_4988_; 
v___x_4987_ = 1;
v___x_4988_ = l_Lean_Meta_mkForallFVars(v_xs_4953_, v_a_4968_, v___x_4976_, v___x_4975_, v___x_4975_, v___x_4987_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v_a_4989_; lean_object* v___x_4990_; 
v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
lean_inc(v_a_4989_);
lean_dec_ref_known(v___x_4988_, 1);
v___x_4990_ = l_Lean_Meta_letToHave(v_a_4989_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v_a_4991_; lean_object* v___x_4992_; 
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
lean_inc(v_a_4991_);
lean_dec_ref_known(v___x_4990_, 1);
v___x_4992_ = l_Lean_Meta_mkLambdaFVars(v_xs_4953_, v_a_4983_, v___x_4976_, v___x_4975_, v___x_4976_, v___x_4975_, v___x_4987_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v_a_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4998_; 
v_a_4993_ = lean_ctor_get(v___x_4992_, 0);
lean_inc(v_a_4993_);
lean_dec_ref_known(v___x_4992_, 1);
lean_inc_n(v___x_4950_, 2);
v___x_4994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4950_);
lean_ctor_set(v___x_4994_, 1, v_levelParams_4948_);
lean_ctor_set(v___x_4994_, 2, v_a_4991_);
v___x_4995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4950_);
lean_ctor_set(v___x_4995_, 1, v___x_4963_);
v___x_4996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4994_);
lean_ctor_set(v___x_4996_, 1, v_a_4993_);
lean_ctor_set(v___x_4996_, 2, v___x_4995_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set_tag(v___x_4985_, 2);
lean_ctor_set(v___x_4985_, 0, v___x_4996_);
v___x_4998_ = v___x_4985_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v___x_4996_);
v___x_4998_ = v_reuseFailAlloc_5012_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
lean_object* v___x_4999_; 
v___x_4999_ = l_Lean_addDecl(v___x_4998_, v___x_4976_, v___y_4980_, v___y_4981_);
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_object* v___x_5000_; 
lean_dec_ref_known(v___x_4999_, 1);
lean_inc(v___x_4950_);
v___x_5000_ = l_Lean_inferDefEqAttr(v___x_4950_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v_toCold_5001_; lean_object* v_options_5002_; uint8_t v_hasTrace_5003_; 
lean_dec_ref_known(v___x_5000_, 1);
v_toCold_5001_ = lean_ctor_get(v___y_4980_, 0);
v_options_5002_ = lean_ctor_get(v_toCold_5001_, 2);
v_hasTrace_5003_ = lean_ctor_get_uint8(v_options_5002_, sizeof(void*)*1);
if (v_hasTrace_5003_ == 0)
{
lean_dec(v___x_4950_);
goto v___jp_4960_;
}
else
{
lean_object* v_inheritedTraceOptions_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; uint8_t v___x_5007_; 
v_inheritedTraceOptions_5004_ = lean_ctor_get(v_toCold_5001_, 11);
v___x_5005_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_5006_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_5007_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5004_, v_options_5002_, v___x_5006_);
if (v___x_5007_ == 0)
{
lean_dec(v___x_4950_);
goto v___jp_4960_;
}
else
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5008_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1);
v___x_5009_ = l_Lean_MessageData_ofConstName(v___x_4950_, v___x_4976_);
v___x_5010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5008_);
lean_ctor_set(v___x_5010_, 1, v___x_5009_);
v___x_5011_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_5005_, v___x_5010_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
return v___x_5011_;
}
}
}
else
{
lean_dec(v___x_4950_);
return v___x_5000_;
}
}
else
{
lean_dec(v___x_4950_);
return v___x_4999_;
}
}
}
else
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5020_; 
lean_dec(v_a_4991_);
lean_del_object(v___x_4985_);
lean_dec(v___x_4950_);
lean_dec(v_levelParams_4948_);
v_a_5013_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5015_ = v___x_4992_;
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_4992_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5018_; 
if (v_isShared_5016_ == 0)
{
v___x_5018_ = v___x_5015_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_a_5013_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
}
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_del_object(v___x_4985_);
lean_dec(v_a_4983_);
lean_dec(v___x_4950_);
lean_dec(v_levelParams_4948_);
v_a_5021_ = lean_ctor_get(v___x_4990_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_4990_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_4990_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5026_; 
if (v_isShared_5024_ == 0)
{
v___x_5026_ = v___x_5023_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
else
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
lean_del_object(v___x_4985_);
lean_dec(v_a_4983_);
lean_dec(v___x_4950_);
lean_dec(v_levelParams_4948_);
v_a_5029_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_4988_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_4988_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5034_; 
if (v_isShared_5032_ == 0)
{
v___x_5034_ = v___x_5031_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
}
}
else
{
lean_object* v_a_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5066_; 
lean_dec(v_a_4971_);
lean_dec(v_a_4968_);
lean_dec_ref(v___x_4952_);
lean_dec(v___x_4951_);
lean_dec(v___x_4950_);
lean_dec(v_levelParams_4948_);
v_a_5059_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_5061_ = v___x_4973_;
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_a_5059_);
lean_dec(v___x_4973_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v___x_5064_; 
if (v_isShared_5062_ == 0)
{
v___x_5064_ = v___x_5061_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5059_);
v___x_5064_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
return v___x_5064_;
}
}
}
}
else
{
lean_object* v_a_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5074_; 
lean_dec(v_a_4968_);
lean_dec_ref(v___x_4952_);
lean_dec(v___x_4951_);
lean_dec(v___x_4950_);
lean_dec(v_levelParams_4948_);
v_a_5067_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5069_ = v___x_4970_;
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_a_5067_);
lean_dec(v___x_4970_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5072_; 
if (v_isShared_5070_ == 0)
{
v___x_5072_ = v___x_5069_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v_a_5067_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
return v___x_5072_;
}
}
}
}
else
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5082_; 
lean_dec_ref(v___x_4952_);
lean_dec(v___x_4951_);
lean_dec(v___x_4950_);
lean_dec(v_levelParams_4948_);
v_a_5075_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5077_ = v___x_4967_;
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_4967_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5080_; 
if (v_isShared_5078_ == 0)
{
v___x_5080_ = v___x_5077_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
v___jp_4960_:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4961_ = lean_box(0);
v___x_4962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4961_);
return v___x_4962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed(lean_object* v_levelParams_5083_, lean_object* v_declName_5084_, lean_object* v___x_5085_, lean_object* v___x_5086_, lean_object* v___x_5087_, lean_object* v_xs_5088_, lean_object* v_body_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(v_levelParams_5083_, v_declName_5084_, v___x_5085_, v___x_5086_, v___x_5087_, v_xs_5088_, v_body_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
lean_dec_ref(v_xs_5088_);
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(lean_object* v_value_5096_, lean_object* v___f_5097_, uint8_t v___x_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_){
_start:
{
uint16_t v___y_5105_; lean_object* v___y_5106_; lean_object* v_fileName_5107_; lean_object* v_fileMap_5108_; lean_object* v_currNamespace_5109_; lean_object* v_openDecls_5110_; lean_object* v_initHeartbeats_5111_; lean_object* v_maxHeartbeats_5112_; lean_object* v_quotContext_5113_; lean_object* v_currMacroScope_5114_; lean_object* v_cancelTk_x3f_5115_; lean_object* v_inheritedTraceOptions_5116_; lean_object* v_currRecDepth_5117_; lean_object* v_ref_5118_; uint8_t v_suppressElabErrors_5119_; uint8_t v_isRecordingDeps_5120_; lean_object* v___y_5121_; lean_object* v_toCold_5127_; lean_object* v_currRecDepth_5128_; lean_object* v_ref_5129_; uint8_t v_suppressElabErrors_5130_; uint8_t v_isRecordingDeps_5131_; lean_object* v_fileName_5132_; lean_object* v_fileMap_5133_; lean_object* v_options_5134_; lean_object* v_currNamespace_5135_; lean_object* v_openDecls_5136_; lean_object* v_initHeartbeats_5137_; lean_object* v_maxHeartbeats_5138_; lean_object* v_quotContext_5139_; lean_object* v_currMacroScope_5140_; lean_object* v_cancelTk_x3f_5141_; lean_object* v_inheritedTraceOptions_5142_; uint16_t v___y_5144_; uint8_t v___y_5145_; lean_object* v___y_5146_; lean_object* v___y_5169_; 
v_toCold_5127_ = lean_ctor_get(v___y_5101_, 0);
v_currRecDepth_5128_ = lean_ctor_get(v___y_5101_, 1);
v_ref_5129_ = lean_ctor_get(v___y_5101_, 2);
v_suppressElabErrors_5130_ = lean_ctor_get_uint8(v___y_5101_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5131_ = lean_ctor_get_uint8(v___y_5101_, sizeof(void*)*3 + 3);
v_fileName_5132_ = lean_ctor_get(v_toCold_5127_, 0);
v_fileMap_5133_ = lean_ctor_get(v_toCold_5127_, 1);
v_options_5134_ = lean_ctor_get(v_toCold_5127_, 2);
v_currNamespace_5135_ = lean_ctor_get(v_toCold_5127_, 4);
v_openDecls_5136_ = lean_ctor_get(v_toCold_5127_, 5);
v_initHeartbeats_5137_ = lean_ctor_get(v_toCold_5127_, 6);
v_maxHeartbeats_5138_ = lean_ctor_get(v_toCold_5127_, 7);
v_quotContext_5139_ = lean_ctor_get(v_toCold_5127_, 8);
v_currMacroScope_5140_ = lean_ctor_get(v_toCold_5127_, 9);
v_cancelTk_x3f_5141_ = lean_ctor_get(v_toCold_5127_, 10);
v_inheritedTraceOptions_5142_ = lean_ctor_get(v_toCold_5127_, 11);
if (v_isRecordingDeps_5131_ == 0)
{
lean_object* v___x_5179_; lean_object* v___x_5180_; 
v___x_5179_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_5134_);
v___x_5180_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_options_5134_, v___x_5179_, v_isRecordingDeps_5131_);
v___y_5169_ = v___x_5180_;
goto v___jp_5168_;
}
else
{
lean_object* v___x_5181_; 
lean_inc_ref(v_options_5134_);
v___x_5181_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_5134_);
v___y_5169_ = v___x_5181_;
goto v___jp_5168_;
}
v___jp_5104_:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___x_5122_ = l_Lean_maxRecDepth;
v___x_5123_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v___y_5106_, v___x_5122_);
v___x_5124_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_5124_, 0, v_fileName_5107_);
lean_ctor_set(v___x_5124_, 1, v_fileMap_5108_);
lean_ctor_set(v___x_5124_, 2, v___y_5106_);
lean_ctor_set(v___x_5124_, 3, v___x_5123_);
lean_ctor_set(v___x_5124_, 4, v_currNamespace_5109_);
lean_ctor_set(v___x_5124_, 5, v_openDecls_5110_);
lean_ctor_set(v___x_5124_, 6, v_initHeartbeats_5111_);
lean_ctor_set(v___x_5124_, 7, v_maxHeartbeats_5112_);
lean_ctor_set(v___x_5124_, 8, v_quotContext_5113_);
lean_ctor_set(v___x_5124_, 9, v_currMacroScope_5114_);
lean_ctor_set(v___x_5124_, 10, v_cancelTk_x3f_5115_);
lean_ctor_set(v___x_5124_, 11, v_inheritedTraceOptions_5116_);
lean_inc(v_ref_5118_);
lean_inc(v_currRecDepth_5117_);
v___x_5125_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5125_, 0, v___x_5124_);
lean_ctor_set(v___x_5125_, 1, v_currRecDepth_5117_);
lean_ctor_set(v___x_5125_, 2, v_ref_5118_);
lean_ctor_set_uint16(v___x_5125_, sizeof(void*)*3, v___y_5105_);
lean_ctor_set_uint8(v___x_5125_, sizeof(void*)*3 + 2, v_suppressElabErrors_5119_);
lean_ctor_set_uint8(v___x_5125_, sizeof(void*)*3 + 3, v_isRecordingDeps_5120_);
v___x_5126_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_value_5096_, v___f_5097_, v___x_5098_, v___y_5099_, v___y_5100_, v___x_5125_, v___y_5121_);
lean_dec_ref_known(v___x_5125_, 3);
return v___x_5126_;
}
v___jp_5143_:
{
lean_object* v___x_5147_; lean_object* v_env_5148_; lean_object* v_nextMacroScope_5149_; lean_object* v_ngen_5150_; lean_object* v_auxDeclNGen_5151_; lean_object* v_traceState_5152_; lean_object* v_recordedDeps_5153_; lean_object* v_messages_5154_; lean_object* v_infoState_5155_; lean_object* v_snapshotTasks_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5166_; 
v___x_5147_ = lean_st_ref_take(v___y_5102_);
v_env_5148_ = lean_ctor_get(v___x_5147_, 0);
v_nextMacroScope_5149_ = lean_ctor_get(v___x_5147_, 1);
v_ngen_5150_ = lean_ctor_get(v___x_5147_, 2);
v_auxDeclNGen_5151_ = lean_ctor_get(v___x_5147_, 3);
v_traceState_5152_ = lean_ctor_get(v___x_5147_, 4);
v_recordedDeps_5153_ = lean_ctor_get(v___x_5147_, 6);
v_messages_5154_ = lean_ctor_get(v___x_5147_, 7);
v_infoState_5155_ = lean_ctor_get(v___x_5147_, 8);
v_snapshotTasks_5156_ = lean_ctor_get(v___x_5147_, 9);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5166_ == 0)
{
lean_object* v_unused_5167_; 
v_unused_5167_ = lean_ctor_get(v___x_5147_, 5);
lean_dec(v_unused_5167_);
v___x_5158_ = v___x_5147_;
v_isShared_5159_ = v_isSharedCheck_5166_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_snapshotTasks_5156_);
lean_inc(v_infoState_5155_);
lean_inc(v_messages_5154_);
lean_inc(v_recordedDeps_5153_);
lean_inc(v_traceState_5152_);
lean_inc(v_auxDeclNGen_5151_);
lean_inc(v_ngen_5150_);
lean_inc(v_nextMacroScope_5149_);
lean_inc(v_env_5148_);
lean_dec(v___x_5147_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5166_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5163_; 
v___x_5160_ = l_Lean_Kernel_enableDiag(v_env_5148_, v___y_5145_);
v___x_5161_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1);
if (v_isShared_5159_ == 0)
{
lean_ctor_set(v___x_5158_, 5, v___x_5161_);
lean_ctor_set(v___x_5158_, 0, v___x_5160_);
v___x_5163_ = v___x_5158_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v___x_5160_);
lean_ctor_set(v_reuseFailAlloc_5165_, 1, v_nextMacroScope_5149_);
lean_ctor_set(v_reuseFailAlloc_5165_, 2, v_ngen_5150_);
lean_ctor_set(v_reuseFailAlloc_5165_, 3, v_auxDeclNGen_5151_);
lean_ctor_set(v_reuseFailAlloc_5165_, 4, v_traceState_5152_);
lean_ctor_set(v_reuseFailAlloc_5165_, 5, v___x_5161_);
lean_ctor_set(v_reuseFailAlloc_5165_, 6, v_recordedDeps_5153_);
lean_ctor_set(v_reuseFailAlloc_5165_, 7, v_messages_5154_);
lean_ctor_set(v_reuseFailAlloc_5165_, 8, v_infoState_5155_);
lean_ctor_set(v_reuseFailAlloc_5165_, 9, v_snapshotTasks_5156_);
v___x_5163_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
lean_object* v___x_5164_; 
v___x_5164_ = lean_st_ref_put(v___y_5102_, v___x_5163_);
lean_inc_ref(v_inheritedTraceOptions_5142_);
lean_inc(v_cancelTk_x3f_5141_);
lean_inc(v_currMacroScope_5140_);
lean_inc(v_quotContext_5139_);
lean_inc(v_maxHeartbeats_5138_);
lean_inc(v_initHeartbeats_5137_);
lean_inc(v_openDecls_5136_);
lean_inc(v_currNamespace_5135_);
lean_inc_ref(v_fileMap_5133_);
lean_inc_ref(v_fileName_5132_);
v___y_5105_ = v___y_5144_;
v___y_5106_ = v___y_5146_;
v_fileName_5107_ = v_fileName_5132_;
v_fileMap_5108_ = v_fileMap_5133_;
v_currNamespace_5109_ = v_currNamespace_5135_;
v_openDecls_5110_ = v_openDecls_5136_;
v_initHeartbeats_5111_ = v_initHeartbeats_5137_;
v_maxHeartbeats_5112_ = v_maxHeartbeats_5138_;
v_quotContext_5113_ = v_quotContext_5139_;
v_currMacroScope_5114_ = v_currMacroScope_5140_;
v_cancelTk_x3f_5115_ = v_cancelTk_x3f_5141_;
v_inheritedTraceOptions_5116_ = v_inheritedTraceOptions_5142_;
v_currRecDepth_5117_ = v_currRecDepth_5128_;
v_ref_5118_ = v_ref_5129_;
v_suppressElabErrors_5119_ = v_suppressElabErrors_5130_;
v_isRecordingDeps_5120_ = v_isRecordingDeps_5131_;
v___y_5121_ = v___y_5102_;
goto v___jp_5104_;
}
}
}
v___jp_5168_:
{
uint16_t v___x_5170_; lean_object* v___x_5171_; lean_object* v_env_5172_; uint8_t v___x_5173_; uint16_t v___x_5174_; uint16_t v___x_5175_; uint16_t v___x_5176_; uint8_t v___x_5177_; 
v___x_5170_ = l_Lean_OptionFlags_ofOptions(v___y_5169_);
v___x_5171_ = lean_st_ref_get(v___y_5102_);
v_env_5172_ = lean_ctor_get(v___x_5171_, 0);
lean_inc_ref(v_env_5172_);
lean_dec(v___x_5171_);
v___x_5173_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5172_);
lean_dec_ref(v_env_5172_);
v___x_5174_ = 1024;
v___x_5175_ = lean_uint16_land(v___x_5170_, v___x_5174_);
v___x_5176_ = 0;
v___x_5177_ = lean_uint16_dec_eq(v___x_5175_, v___x_5176_);
if (v___x_5177_ == 0)
{
if (v___x_5173_ == 0)
{
uint8_t v___x_5178_; 
v___x_5178_ = 1;
v___y_5144_ = v___x_5170_;
v___y_5145_ = v___x_5178_;
v___y_5146_ = v___y_5169_;
goto v___jp_5143_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_5142_);
lean_inc(v_cancelTk_x3f_5141_);
lean_inc(v_currMacroScope_5140_);
lean_inc(v_quotContext_5139_);
lean_inc(v_maxHeartbeats_5138_);
lean_inc(v_initHeartbeats_5137_);
lean_inc(v_openDecls_5136_);
lean_inc(v_currNamespace_5135_);
lean_inc_ref(v_fileMap_5133_);
lean_inc_ref(v_fileName_5132_);
v___y_5105_ = v___x_5170_;
v___y_5106_ = v___y_5169_;
v_fileName_5107_ = v_fileName_5132_;
v_fileMap_5108_ = v_fileMap_5133_;
v_currNamespace_5109_ = v_currNamespace_5135_;
v_openDecls_5110_ = v_openDecls_5136_;
v_initHeartbeats_5111_ = v_initHeartbeats_5137_;
v_maxHeartbeats_5112_ = v_maxHeartbeats_5138_;
v_quotContext_5113_ = v_quotContext_5139_;
v_currMacroScope_5114_ = v_currMacroScope_5140_;
v_cancelTk_x3f_5115_ = v_cancelTk_x3f_5141_;
v_inheritedTraceOptions_5116_ = v_inheritedTraceOptions_5142_;
v_currRecDepth_5117_ = v_currRecDepth_5128_;
v_ref_5118_ = v_ref_5129_;
v_suppressElabErrors_5119_ = v_suppressElabErrors_5130_;
v_isRecordingDeps_5120_ = v_isRecordingDeps_5131_;
v___y_5121_ = v___y_5102_;
goto v___jp_5104_;
}
}
else
{
if (v___x_5173_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_5142_);
lean_inc(v_cancelTk_x3f_5141_);
lean_inc(v_currMacroScope_5140_);
lean_inc(v_quotContext_5139_);
lean_inc(v_maxHeartbeats_5138_);
lean_inc(v_initHeartbeats_5137_);
lean_inc(v_openDecls_5136_);
lean_inc(v_currNamespace_5135_);
lean_inc_ref(v_fileMap_5133_);
lean_inc_ref(v_fileName_5132_);
v___y_5105_ = v___x_5170_;
v___y_5106_ = v___y_5169_;
v_fileName_5107_ = v_fileName_5132_;
v_fileMap_5108_ = v_fileMap_5133_;
v_currNamespace_5109_ = v_currNamespace_5135_;
v_openDecls_5110_ = v_openDecls_5136_;
v_initHeartbeats_5111_ = v_initHeartbeats_5137_;
v_maxHeartbeats_5112_ = v_maxHeartbeats_5138_;
v_quotContext_5113_ = v_quotContext_5139_;
v_currMacroScope_5114_ = v_currMacroScope_5140_;
v_cancelTk_x3f_5115_ = v_cancelTk_x3f_5141_;
v_inheritedTraceOptions_5116_ = v_inheritedTraceOptions_5142_;
v_currRecDepth_5117_ = v_currRecDepth_5128_;
v_ref_5118_ = v_ref_5129_;
v_suppressElabErrors_5119_ = v_suppressElabErrors_5130_;
v_isRecordingDeps_5120_ = v_isRecordingDeps_5131_;
v___y_5121_ = v___y_5102_;
goto v___jp_5104_;
}
else
{
v___y_5144_ = v___x_5170_;
v___y_5145_ = v___x_5098_;
v___y_5146_ = v___y_5169_;
goto v___jp_5143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed(lean_object* v_value_5182_, lean_object* v___f_5183_, lean_object* v___x_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_){
_start:
{
uint8_t v___x_5303__boxed_5190_; lean_object* v_res_5191_; 
v___x_5303__boxed_5190_ = lean_unbox(v___x_5184_);
v_res_5191_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(v_value_5182_, v___f_5183_, v___x_5303__boxed_5190_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
return v_res_5191_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_5193_; lean_object* v___x_5194_; 
v___x_5193_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0));
v___x_5194_ = l_Lean_stringToMessageData(v___x_5193_);
return v___x_5194_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3(void){
_start:
{
lean_object* v___x_5196_; lean_object* v___x_5197_; 
v___x_5196_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__2));
v___x_5197_ = l_Lean_stringToMessageData(v___x_5196_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object* v_preDef_5198_, lean_object* v_unaryPreDefName_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_){
_start:
{
lean_object* v___x_5205_; lean_object* v_env_5206_; lean_object* v_levelParams_5207_; lean_object* v_declName_5208_; lean_object* v_value_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v_env_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___f_5221_; lean_object* v___x_5222_; lean_object* v___f_5223_; uint8_t v___x_5224_; lean_object* v___x_5225_; lean_object* v___f_5226_; lean_object* v___x_5227_; 
v___x_5205_ = lean_st_ref_get(v_a_5203_);
v_env_5206_ = lean_ctor_get(v___x_5205_, 0);
lean_inc_ref(v_env_5206_);
lean_dec(v___x_5205_);
v_levelParams_5207_ = lean_ctor_get(v_preDef_5198_, 1);
lean_inc(v_levelParams_5207_);
v_declName_5208_ = lean_ctor_get(v_preDef_5198_, 3);
lean_inc_n(v_declName_5208_, 2);
v_value_5209_ = lean_ctor_get(v_preDef_5198_, 7);
lean_inc_ref(v_value_5209_);
lean_dec_ref(v_preDef_5198_);
v___x_5210_ = l_Lean_Meta_unfoldThmSuffix;
v___x_5211_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5206_, v_declName_5208_, v___x_5210_);
v___x_5212_ = lean_st_ref_get(v_a_5203_);
v_env_5213_ = lean_ctor_get(v___x_5212_, 0);
lean_inc_ref(v_env_5213_);
lean_dec(v___x_5212_);
v___x_5214_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5213_, v_unaryPreDefName_5199_, v___x_5210_);
v___x_5215_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1);
lean_inc(v___x_5211_);
v___x_5216_ = l_Lean_MessageData_ofName(v___x_5211_);
v___x_5217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5217_, 0, v___x_5215_);
lean_ctor_set(v___x_5217_, 1, v___x_5216_);
v___x_5218_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3);
v___x_5219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5217_);
lean_ctor_set(v___x_5219_, 1, v___x_5218_);
lean_inc(v___x_5214_);
v___x_5220_ = l_Lean_MessageData_ofName(v___x_5214_);
lean_inc_ref(v___x_5220_);
v___f_5221_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5221_, 0, v_levelParams_5207_);
lean_closure_set(v___f_5221_, 1, v_declName_5208_);
lean_closure_set(v___f_5221_, 2, v___x_5211_);
lean_closure_set(v___f_5221_, 3, v___x_5214_);
lean_closure_set(v___f_5221_, 4, v___x_5220_);
v___x_5222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5219_);
lean_ctor_set(v___x_5222_, 1, v___x_5220_);
v___f_5223_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_5223_, 0, v___x_5222_);
v___x_5224_ = 0;
v___x_5225_ = lean_box(v___x_5224_);
v___f_5226_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_5226_, 0, v_value_5209_);
lean_closure_set(v___f_5226_, 1, v___f_5221_);
lean_closure_set(v___f_5226_, 2, v___x_5225_);
v___x_5227_ = l_Lean_Meta_mapErrorImp___redArg(v___f_5226_, v___f_5223_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5227_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5227_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5233_; 
if (v_isShared_5231_ == 0)
{
v___x_5233_ = v___x_5230_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_a_5228_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
v_a_5236_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5227_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5227_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___boxed(lean_object* v_preDef_5244_, lean_object* v_unaryPreDefName_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_preDef_5244_, v_unaryPreDefName_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_);
lean_dec(v_a_5249_);
lean_dec_ref(v_a_5248_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5296_; uint8_t v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
v___x_5296_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5297_ = 0;
v___x_5298_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5299_ = l_Lean_registerTraceClass(v___x_5296_, v___x_5297_, v___x_5298_);
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2____boxed(lean_object* v_a_5300_){
_start:
{
lean_object* v_res_5301_; 
v_res_5301_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_();
return v_res_5301_;
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
