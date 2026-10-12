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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__27;
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
lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2_ = stack[0].m_obj;
lean_object* v___y_3_ = stack[1].m_obj;
lean_object* v___y_4_ = stack[2].m_obj;
lean_object* v___y_5_ = stack[3].m_obj;
lean_object* v___y_6_ = stack[4].m_obj;
lean_object* v_res_11_;
v_res_11_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(v_msg_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___boxed(lean_object* v_msg_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(v_msg_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0(lean_object* v_k_19_, lean_object* v_b_20_, lean_object* v_c_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___x_27_; 
lean_inc(v___y_25_);
lean_inc_ref(v___y_24_);
lean_inc(v___y_23_);
lean_inc_ref(v___y_22_);
v___x_27_ = lean_apply_7(v_k_19_, v_b_20_, v_c_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, lean_box(0));
return v___x_27_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_19_ = stack[0].m_obj;
lean_object* v_b_20_ = stack[1].m_obj;
lean_object* v_c_21_ = stack[2].m_obj;
lean_object* v___y_22_ = stack[3].m_obj;
lean_object* v___y_23_ = stack[4].m_obj;
lean_object* v___y_24_ = stack[5].m_obj;
lean_object* v___y_25_ = stack[6].m_obj;
lean_object* v_res_28_;
v_res_28_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0(v_k_19_, v_b_20_, v_c_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed(lean_object* v_k_29_, lean_object* v_b_30_, lean_object* v_c_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0(v_k_29_, v_b_30_, v_c_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
return v_res_37_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(lean_object* v_type_38_, lean_object* v_maxFVars_x3f_39_, lean_object* v_k_40_, uint8_t v_cleanupAnnotations_41_, uint8_t v_whnfType_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___f_48_; lean_object* v___x_49_; 
v___f_48_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_48_, 0, v_k_40_);
v___x_49_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_38_, v_maxFVars_x3f_39_, v___f_48_, v_cleanupAnnotations_41_, v_whnfType_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_57_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_57_ == 0)
{
v___x_52_ = v___x_49_;
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_49_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
if (v_isShared_53_ == 0)
{
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_50_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
v_a_58_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_49_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_49_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_38_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_39_ = stack[1].m_obj;
lean_object* v_k_40_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_41_ = stack[3].m_num;
uint8_t v_whnfType_42_ = stack[4].m_num;
lean_object* v___y_43_ = stack[5].m_obj;
lean_object* v___y_44_ = stack[6].m_obj;
lean_object* v___y_45_ = stack[7].m_obj;
lean_object* v___y_46_ = stack[8].m_obj;
lean_object* v_res_66_;
v_res_66_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_38_, v_maxFVars_x3f_39_, v_k_40_, v_cleanupAnnotations_41_, v_whnfType_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___boxed(lean_object* v_type_67_, lean_object* v_maxFVars_x3f_68_, lean_object* v_k_69_, lean_object* v_cleanupAnnotations_70_, lean_object* v_whnfType_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_77_; uint8_t v_whnfType_boxed_78_; lean_object* v_res_79_; 
v_cleanupAnnotations_boxed_77_ = lean_unbox(v_cleanupAnnotations_70_);
v_whnfType_boxed_78_ = lean_unbox(v_whnfType_71_);
v_res_79_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_67_, v_maxFVars_x3f_68_, v_k_69_, v_cleanupAnnotations_boxed_77_, v_whnfType_boxed_78_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_79_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1(lean_object* v_00_u03b1_80_, lean_object* v_type_81_, lean_object* v_maxFVars_x3f_82_, lean_object* v_k_83_, uint8_t v_cleanupAnnotations_84_, uint8_t v_whnfType_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_81_, v_maxFVars_x3f_82_, v_k_83_, v_cleanupAnnotations_84_, v_whnfType_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
return v___x_91_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_81_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_82_ = stack[2].m_obj;
lean_object* v_k_83_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_84_ = stack[4].m_num;
uint8_t v_whnfType_85_ = stack[5].m_num;
lean_object* v___y_86_ = stack[6].m_obj;
lean_object* v___y_87_ = stack[7].m_obj;
lean_object* v___y_88_ = stack[8].m_obj;
lean_object* v___y_89_ = stack[9].m_obj;
lean_object* v_res_92_;
v_res_92_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1(lean_box(0), v_type_81_, v_maxFVars_x3f_82_, v_k_83_, v_cleanupAnnotations_84_, v_whnfType_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___boxed(lean_object* v_00_u03b1_93_, lean_object* v_type_94_, lean_object* v_maxFVars_x3f_95_, lean_object* v_k_96_, lean_object* v_cleanupAnnotations_97_, lean_object* v_whnfType_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_104_; uint8_t v_whnfType_boxed_105_; lean_object* v_res_106_; 
v_cleanupAnnotations_boxed_104_ = lean_unbox(v_cleanupAnnotations_97_);
v_whnfType_boxed_105_ = lean_unbox(v_whnfType_98_);
v_res_106_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1(v_00_u03b1_93_, v_type_94_, v_maxFVars_x3f_95_, v_k_96_, v_cleanupAnnotations_boxed_104_, v_whnfType_boxed_105_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_106_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(lean_object* v_mvarId_107_, lean_object* v_x_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_107_, v_x_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
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
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
v_a_123_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_114_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_114_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_107_ = stack[0].m_obj;
lean_object* v_x_108_ = stack[1].m_obj;
lean_object* v___y_109_ = stack[2].m_obj;
lean_object* v___y_110_ = stack[3].m_obj;
lean_object* v___y_111_ = stack[4].m_obj;
lean_object* v___y_112_ = stack[5].m_obj;
lean_object* v_res_131_;
v_res_131_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(v_mvarId_107_, v_x_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg___boxed(lean_object* v_mvarId_132_, lean_object* v_x_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(v_mvarId_132_, v_x_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_139_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4(lean_object* v_00_u03b1_140_, lean_object* v_mvarId_141_, lean_object* v_x_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(v_mvarId_141_, v_x_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_141_ = stack[1].m_obj;
lean_object* v_x_142_ = stack[2].m_obj;
lean_object* v___y_143_ = stack[3].m_obj;
lean_object* v___y_144_ = stack[4].m_obj;
lean_object* v___y_145_ = stack[5].m_obj;
lean_object* v___y_146_ = stack[6].m_obj;
lean_object* v_res_149_;
v_res_149_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4(lean_box(0), v_mvarId_141_, v_x_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___boxed(lean_object* v_00_u03b1_150_, lean_object* v_mvarId_151_, lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4(v_00_u03b1_150_, v_mvarId_151_, v_x_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_158_;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(uint8_t v___x_159_, lean_object* v_x_160_){
_start:
{
return v___x_159_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_159_ = stack[0].m_num;
lean_object* v_x_160_ = stack[1].m_obj;
uint8_t v_res_161_;
v_res_161_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(v___x_159_, v_x_160_);
stack->m_num = v_res_161_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed(lean_object* v___x_162_, lean_object* v_x_163_){
_start:
{
uint8_t v___x_6075__boxed_164_; uint8_t v_res_165_; lean_object* v_r_166_; 
v___x_6075__boxed_164_ = lean_unbox(v___x_162_);
v_res_165_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(v___x_6075__boxed_164_, v_x_163_);
lean_dec(v_x_163_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(lean_object* v___x_167_, lean_object* v___x_168_, uint8_t v___x_169_, uint8_t v___x_170_, lean_object* v_ys_171_, lean_object* v_x_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; 
v___x_178_ = l_Lean_Expr_appFn_x21(v___x_167_);
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = lean_array_get_borrowed(v___x_168_, v_ys_171_, v___x_179_);
lean_inc(v___x_180_);
v___x_181_ = l_Lean_Expr_app___override(v___x_178_, v___x_180_);
v___x_182_ = 1;
v___x_183_ = l_Lean_Meta_mkLambdaFVars(v_ys_171_, v___x_181_, v___x_169_, v___x_170_, v___x_169_, v___x_170_, v___x_182_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
return v___x_183_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_167_ = stack[0].m_obj;
lean_object* v___x_168_ = stack[1].m_obj;
uint8_t v___x_169_ = stack[2].m_num;
uint8_t v___x_170_ = stack[3].m_num;
lean_object* v_ys_171_ = stack[4].m_obj;
lean_object* v_x_172_ = stack[5].m_obj;
lean_object* v___y_173_ = stack[6].m_obj;
lean_object* v___y_174_ = stack[7].m_obj;
lean_object* v___y_175_ = stack[8].m_obj;
lean_object* v___y_176_ = stack[9].m_obj;
lean_object* v_res_184_;
v_res_184_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(v___x_167_, v___x_168_, v___x_169_, v___x_170_, v_ys_171_, v_x_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed(lean_object* v___x_185_, lean_object* v___x_186_, lean_object* v___x_187_, lean_object* v___x_188_, lean_object* v_ys_189_, lean_object* v_x_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
uint8_t v___x_6087__boxed_196_; uint8_t v___x_6088__boxed_197_; lean_object* v_res_198_; 
v___x_6087__boxed_196_ = lean_unbox(v___x_187_);
v___x_6088__boxed_197_ = lean_unbox(v___x_188_);
v_res_198_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(v___x_185_, v___x_186_, v___x_6087__boxed_196_, v___x_6088__boxed_197_, v_ys_189_, v_x_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec_ref(v_x_190_);
lean_dec_ref(v_ys_189_);
lean_dec_ref(v___x_186_);
lean_dec_ref(v___x_185_);
return v_res_198_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(lean_object* v_msgData_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; lean_object* v_env_206_; uint8_t v___x_207_; lean_object* v_env_208_; lean_object* v___x_209_; lean_object* v_toCold_210_; lean_object* v_mctx_211_; lean_object* v_lctx_212_; lean_object* v_options_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_205_ = lean_st_ref_get(v___y_203_);
v_env_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc_ref(v_env_206_);
lean_dec(v___x_205_);
v___x_207_ = 0;
v_env_208_ = l_Lean_Environment_setRecordingDeps(v_env_206_, v___x_207_);
v___x_209_ = lean_st_ref_get(v___y_201_);
v_toCold_210_ = lean_ctor_get(v___y_202_, 0);
v_mctx_211_ = lean_ctor_get(v___x_209_, 0);
lean_inc_ref(v_mctx_211_);
lean_dec(v___x_209_);
v_lctx_212_ = lean_ctor_get(v___y_200_, 2);
v_options_213_ = lean_ctor_get(v_toCold_210_, 2);
lean_inc_ref(v_options_213_);
lean_inc_ref(v_lctx_212_);
v___x_214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_214_, 0, v_env_208_);
lean_ctor_set(v___x_214_, 1, v_mctx_211_);
lean_ctor_set(v___x_214_, 2, v_lctx_212_);
lean_ctor_set(v___x_214_, 3, v_options_213_);
v___x_215_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v_msgData_199_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_199_ = stack[0].m_obj;
lean_object* v___y_200_ = stack[1].m_obj;
lean_object* v___y_201_ = stack[2].m_obj;
lean_object* v___y_202_ = stack[3].m_obj;
lean_object* v___y_203_ = stack[4].m_obj;
lean_object* v_res_217_;
v_res_217_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msgData_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4___boxed(lean_object* v_msgData_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msgData_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_224_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(lean_object* v_msg_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_ref_231_; lean_object* v___x_232_; lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_ref_231_ = lean_ctor_get(v___y_228_, 2);
v___x_232_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
lean_inc(v_ref_231_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v_ref_231_);
lean_ctor_set(v___x_237_, 1, v_a_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 1);
lean_ctor_set(v___x_235_, 0, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_225_ = stack[0].m_obj;
lean_object* v___y_226_ = stack[1].m_obj;
lean_object* v___y_227_ = stack[2].m_obj;
lean_object* v___y_228_ = stack[3].m_obj;
lean_object* v___y_229_ = stack[4].m_obj;
lean_object* v_res_242_;
v_res_242_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg___boxed(lean_object* v_msg_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
lean_object* v_ks_254_; lean_object* v_vs_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_279_; 
v_ks_254_ = lean_ctor_get(v_x_250_, 0);
v_vs_255_ = lean_ctor_get(v_x_250_, 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_279_ == 0)
{
v___x_257_ = v_x_250_;
v_isShared_258_ = v_isSharedCheck_279_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_vs_255_);
lean_inc(v_ks_254_);
lean_dec(v_x_250_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_279_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_get_size(v_ks_254_);
v___x_260_ = lean_nat_dec_lt(v_x_251_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
lean_dec(v_x_251_);
v___x_261_ = lean_array_push(v_ks_254_, v_x_252_);
v___x_262_ = lean_array_push(v_vs_255_, v_x_253_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_262_);
lean_ctor_set(v___x_257_, 0, v___x_261_);
v___x_264_ = v___x_257_;
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
else
{
lean_object* v_k_x27_266_; uint8_t v___x_267_; 
v_k_x27_266_ = lean_array_fget_borrowed(v_ks_254_, v_x_251_);
v___x_267_ = l_Lean_instBEqMVarId_beq(v_x_252_, v_k_x27_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_269_; 
if (v_isShared_258_ == 0)
{
v___x_269_ = v___x_257_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_ks_254_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_vs_255_);
v___x_269_ = v_reuseFailAlloc_273_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_x_251_, v___x_270_);
lean_dec(v_x_251_);
v_x_250_ = v___x_269_;
v_x_251_ = v___x_271_;
goto _start;
}
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_274_ = lean_array_fset(v_ks_254_, v_x_251_, v_x_252_);
v___x_275_ = lean_array_fset(v_vs_255_, v_x_251_, v_x_253_);
lean_dec(v_x_251_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_275_);
lean_ctor_set(v___x_257_, 0, v___x_274_);
v___x_277_ = v___x_257_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_n_280_, lean_object* v_k_281_, lean_object* v_v_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_280_, v___x_283_, v_k_281_, v_v_282_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_285_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(lean_object* v_x_286_, size_t v_x_287_, size_t v_x_288_, lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
if (lean_obj_tag(v_x_286_) == 0)
{
lean_object* v_es_291_; size_t v___x_292_; size_t v___x_293_; lean_object* v_j_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_es_291_ = lean_ctor_get(v_x_286_, 0);
v___x_292_ = ((size_t)31ULL);
v___x_293_ = lean_usize_land(v_x_287_, v___x_292_);
v_j_294_ = lean_usize_to_nat(v___x_293_);
v___x_295_ = lean_array_get_size(v_es_291_);
v___x_296_ = lean_nat_dec_lt(v_j_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_dec(v_j_294_);
lean_dec(v_x_290_);
lean_dec(v_x_289_);
return v_x_286_;
}
else
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_335_; 
lean_inc_ref(v_es_291_);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_286_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v_x_286_, 0);
lean_dec(v_unused_336_);
v___x_298_ = v_x_286_;
v_isShared_299_ = v_isSharedCheck_335_;
goto v_resetjp_297_;
}
else
{
lean_dec(v_x_286_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_335_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v_v_300_; lean_object* v___x_301_; lean_object* v_xs_x27_302_; lean_object* v___y_304_; 
v_v_300_ = lean_array_fget(v_es_291_, v_j_294_);
v___x_301_ = lean_box(0);
v_xs_x27_302_ = lean_array_fset(v_es_291_, v_j_294_, v___x_301_);
switch(lean_obj_tag(v_v_300_))
{
case 0:
{
lean_object* v_key_309_; lean_object* v_val_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_320_; 
v_key_309_ = lean_ctor_get(v_v_300_, 0);
v_val_310_ = lean_ctor_get(v_v_300_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v_v_300_);
if (v_isSharedCheck_320_ == 0)
{
v___x_312_ = v_v_300_;
v_isShared_313_ = v_isSharedCheck_320_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_val_310_);
lean_inc(v_key_309_);
lean_dec(v_v_300_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_320_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
uint8_t v___x_314_; 
v___x_314_ = l_Lean_instBEqMVarId_beq(v_x_289_, v_key_309_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_del_object(v___x_312_);
v___x_315_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_309_, v_val_310_, v_x_289_, v_x_290_);
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
v___y_304_ = v___x_316_;
goto v___jp_303_;
}
else
{
lean_object* v___x_318_; 
lean_dec(v_val_310_);
lean_dec(v_key_309_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v_x_290_);
lean_ctor_set(v___x_312_, 0, v_x_289_);
v___x_318_ = v___x_312_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_x_289_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_x_290_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
v___y_304_ = v___x_318_;
goto v___jp_303_;
}
}
}
}
case 1:
{
lean_object* v_node_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_333_; 
v_node_321_ = lean_ctor_get(v_v_300_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_v_300_);
if (v_isSharedCheck_333_ == 0)
{
v___x_323_ = v_v_300_;
v_isShared_324_ = v_isSharedCheck_333_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_node_321_);
lean_dec(v_v_300_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_333_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
size_t v___x_325_; size_t v___x_326_; size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_325_ = ((size_t)5ULL);
v___x_326_ = lean_usize_shift_right(v_x_287_, v___x_325_);
v___x_327_ = ((size_t)1ULL);
v___x_328_ = lean_usize_add(v_x_288_, v___x_327_);
v___x_329_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_node_321_, v___x_326_, v___x_328_, v_x_289_, v_x_290_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_329_);
v___x_331_ = v___x_323_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
v___y_304_ = v___x_331_;
goto v___jp_303_;
}
}
}
default: 
{
lean_object* v___x_334_; 
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v_x_289_);
lean_ctor_set(v___x_334_, 1, v_x_290_);
v___y_304_ = v___x_334_;
goto v___jp_303_;
}
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = lean_array_fset(v_xs_x27_302_, v_j_294_, v___y_304_);
lean_dec(v_j_294_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_305_);
v___x_307_ = v___x_298_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
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
lean_object* v_ks_337_; lean_object* v_vs_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_356_; 
v_ks_337_ = lean_ctor_get(v_x_286_, 0);
v_vs_338_ = lean_ctor_get(v_x_286_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_286_);
if (v_isSharedCheck_356_ == 0)
{
v___x_340_ = v_x_286_;
v_isShared_341_ = v_isSharedCheck_356_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_vs_338_);
lean_inc(v_ks_337_);
lean_dec(v_x_286_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_356_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_ks_337_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_vs_338_);
v___x_343_ = v_reuseFailAlloc_355_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v_newNode_344_; size_t v___x_345_; uint8_t v___x_346_; 
v_newNode_344_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v___x_343_, v_x_289_, v_x_290_);
v___x_345_ = ((size_t)7ULL);
v___x_346_ = lean_usize_dec_le(v___x_345_, v_x_288_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_344_);
v___x_348_ = lean_unsigned_to_nat(4u);
v___x_349_ = lean_nat_dec_lt(v___x_347_, v___x_348_);
lean_dec(v___x_347_);
if (v___x_349_ == 0)
{
lean_object* v_ks_350_; lean_object* v_vs_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_ks_350_ = lean_ctor_get(v_newNode_344_, 0);
lean_inc_ref(v_ks_350_);
v_vs_351_ = lean_ctor_get(v_newNode_344_, 1);
lean_inc_ref(v_vs_351_);
lean_dec_ref(v_newNode_344_);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_354_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_x_288_, v_ks_350_, v_vs_351_, v___x_352_, v___x_353_);
lean_dec_ref(v_vs_351_);
lean_dec_ref(v_ks_350_);
return v___x_354_;
}
else
{
return v_newNode_344_;
}
}
else
{
return v_newNode_344_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_286_ = stack[0].m_obj;
size_t v_x_287_ = stack[1].m_num;
size_t v_x_288_ = stack[2].m_num;
lean_object* v_x_289_ = stack[3].m_obj;
lean_object* v_x_290_ = stack[4].m_obj;
lean_object* v_res_357_;
v_res_357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_286_, v_x_287_, v_x_288_, v_x_289_, v_x_290_);
stack->m_obj
 = v_res_357_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(size_t v_depth_358_, lean_object* v_keys_359_, lean_object* v_vals_360_, lean_object* v_i_361_, lean_object* v_entries_362_){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = lean_array_get_size(v_keys_359_);
v___x_364_ = lean_nat_dec_lt(v_i_361_, v___x_363_);
if (v___x_364_ == 0)
{
lean_dec(v_i_361_);
return v_entries_362_;
}
else
{
lean_object* v_k_365_; lean_object* v_v_366_; uint64_t v___x_367_; size_t v_h_368_; size_t v___x_369_; lean_object* v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v_h_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_k_365_ = lean_array_fget_borrowed(v_keys_359_, v_i_361_);
v_v_366_ = lean_array_fget_borrowed(v_vals_360_, v_i_361_);
v___x_367_ = l_Lean_instHashableMVarId_hash(v_k_365_);
v_h_368_ = lean_uint64_to_usize(v___x_367_);
v___x_369_ = ((size_t)5ULL);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_sub(v_depth_358_, v___x_371_);
v___x_373_ = lean_usize_mul(v___x_369_, v___x_372_);
v_h_374_ = lean_usize_shift_right(v_h_368_, v___x_373_);
v___x_375_ = lean_nat_add(v_i_361_, v___x_370_);
lean_dec(v_i_361_);
lean_inc(v_v_366_);
lean_inc(v_k_365_);
v___x_376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_entries_362_, v_h_374_, v_depth_358_, v_k_365_, v_v_366_);
v_i_361_ = v___x_375_;
v_entries_362_ = v___x_376_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_358_ = stack[0].m_num;
lean_object* v_keys_359_ = stack[1].m_obj;
lean_object* v_vals_360_ = stack[2].m_obj;
lean_object* v_i_361_ = stack[3].m_obj;
lean_object* v_entries_362_ = stack[4].m_obj;
lean_object* v_res_378_;
v_res_378_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_358_, v_keys_359_, v_vals_360_, v_i_361_, v_entries_362_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_379_, lean_object* v_keys_380_, lean_object* v_vals_381_, lean_object* v_i_382_, lean_object* v_entries_383_){
_start:
{
size_t v_depth_boxed_384_; lean_object* v_res_385_; 
v_depth_boxed_384_ = lean_unbox_usize(v_depth_379_);
lean_dec(v_depth_379_);
v_res_385_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_384_, v_keys_380_, v_vals_381_, v_i_382_, v_entries_383_);
lean_dec_ref(v_vals_381_);
lean_dec_ref(v_keys_380_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
size_t v_x_6360__boxed_391_; size_t v_x_6361__boxed_392_; lean_object* v_res_393_; 
v_x_6360__boxed_391_ = lean_unbox_usize(v_x_387_);
lean_dec(v_x_387_);
v_x_6361__boxed_392_ = lean_unbox_usize(v_x_388_);
lean_dec(v_x_388_);
v_res_393_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_386_, v_x_6360__boxed_391_, v_x_6361__boxed_392_, v_x_389_, v_x_390_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
uint64_t v___x_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; 
v___x_397_ = l_Lean_instHashableMVarId_hash(v_x_395_);
v___x_398_ = lean_uint64_to_usize(v___x_397_);
v___x_399_ = ((size_t)1ULL);
v___x_400_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_394_, v___x_398_, v___x_399_, v_x_395_, v_x_396_);
return v___x_400_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(lean_object* v_mvarId_401_, lean_object* v_val_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; lean_object* v_mctx_406_; lean_object* v_cache_407_; lean_object* v_zetaDeltaFVarIds_408_; lean_object* v_postponed_409_; lean_object* v_diag_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_440_; 
v___x_405_ = lean_st_ref_take(v___y_403_);
v_mctx_406_ = lean_ctor_get(v___x_405_, 0);
v_cache_407_ = lean_ctor_get(v___x_405_, 1);
v_zetaDeltaFVarIds_408_ = lean_ctor_get(v___x_405_, 2);
v_postponed_409_ = lean_ctor_get(v___x_405_, 3);
v_diag_410_ = lean_ctor_get(v___x_405_, 4);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_440_ == 0)
{
v___x_412_ = v___x_405_;
v_isShared_413_ = v_isSharedCheck_440_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_diag_410_);
lean_inc(v_postponed_409_);
lean_inc(v_zetaDeltaFVarIds_408_);
lean_inc(v_cache_407_);
lean_inc(v_mctx_406_);
lean_dec(v___x_405_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_440_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_depth_414_; lean_object* v_levelAssignDepth_415_; lean_object* v_lmvarCounter_416_; lean_object* v_mvarCounter_417_; lean_object* v_lDecls_418_; lean_object* v_decls_419_; lean_object* v_userNames_420_; lean_object* v_lAssignment_421_; lean_object* v_eAssignment_422_; lean_object* v_dAssignment_423_; lean_object* v_instanceTypedMVars_424_; lean_object* v_synthNormMemo_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_439_; 
v_depth_414_ = lean_ctor_get(v_mctx_406_, 0);
v_levelAssignDepth_415_ = lean_ctor_get(v_mctx_406_, 1);
v_lmvarCounter_416_ = lean_ctor_get(v_mctx_406_, 2);
v_mvarCounter_417_ = lean_ctor_get(v_mctx_406_, 3);
v_lDecls_418_ = lean_ctor_get(v_mctx_406_, 4);
v_decls_419_ = lean_ctor_get(v_mctx_406_, 5);
v_userNames_420_ = lean_ctor_get(v_mctx_406_, 6);
v_lAssignment_421_ = lean_ctor_get(v_mctx_406_, 7);
v_eAssignment_422_ = lean_ctor_get(v_mctx_406_, 8);
v_dAssignment_423_ = lean_ctor_get(v_mctx_406_, 9);
v_instanceTypedMVars_424_ = lean_ctor_get(v_mctx_406_, 10);
v_synthNormMemo_425_ = lean_ctor_get(v_mctx_406_, 11);
v_isSharedCheck_439_ = !lean_is_exclusive(v_mctx_406_);
if (v_isSharedCheck_439_ == 0)
{
v___x_427_ = v_mctx_406_;
v_isShared_428_ = v_isSharedCheck_439_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_synthNormMemo_425_);
lean_inc(v_instanceTypedMVars_424_);
lean_inc(v_dAssignment_423_);
lean_inc(v_eAssignment_422_);
lean_inc(v_lAssignment_421_);
lean_inc(v_userNames_420_);
lean_inc(v_decls_419_);
lean_inc(v_lDecls_418_);
lean_inc(v_mvarCounter_417_);
lean_inc(v_lmvarCounter_416_);
lean_inc(v_levelAssignDepth_415_);
lean_inc(v_depth_414_);
lean_dec(v_mctx_406_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_439_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_429_ = lean_box(0);
v___x_430_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_eAssignment_422_, v_mvarId_401_, v_val_402_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 8, v___x_430_);
v___x_432_ = v___x_427_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_depth_414_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_levelAssignDepth_415_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_lmvarCounter_416_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_mvarCounter_417_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_lDecls_418_);
lean_ctor_set(v_reuseFailAlloc_438_, 5, v_decls_419_);
lean_ctor_set(v_reuseFailAlloc_438_, 6, v_userNames_420_);
lean_ctor_set(v_reuseFailAlloc_438_, 7, v_lAssignment_421_);
lean_ctor_set(v_reuseFailAlloc_438_, 8, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_438_, 9, v_dAssignment_423_);
lean_ctor_set(v_reuseFailAlloc_438_, 10, v_instanceTypedMVars_424_);
lean_ctor_set(v_reuseFailAlloc_438_, 11, v_synthNormMemo_425_);
v___x_432_ = v_reuseFailAlloc_438_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_432_);
v___x_434_ = v___x_412_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_cache_407_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_zetaDeltaFVarIds_408_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_postponed_409_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_diag_410_);
v___x_434_ = v_reuseFailAlloc_437_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_st_ref_put(v___y_403_, v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_429_);
return v___x_436_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_401_ = stack[0].m_obj;
lean_object* v_val_402_ = stack[1].m_obj;
lean_object* v___y_403_ = stack[2].m_obj;
lean_object* v_res_441_;
v_res_441_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_401_, v_val_402_, v___y_403_);
stack->m_obj
 = v_res_441_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg___boxed(lean_object* v_mvarId_442_, lean_object* v_val_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_442_, v_val_443_, v___y_444_);
lean_dec(v___y_444_);
return v_res_446_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4));
v___x_454_ = lean_unsigned_to_nat(41u);
v___x_455_ = lean_unsigned_to_nat(34u);
v___x_456_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3));
v___x_457_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_458_ = l_mkPanicMessageWithDecl(v___x_457_, v___x_456_, v___x_455_, v___x_454_, v___x_453_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18(void){
_start:
{
lean_object* v___x_481_; lean_object* v_dummy_482_; 
v___x_481_ = lean_box(0);
v_dummy_482_ = l_Lean_Expr_sort___override(v___x_481_);
return v_dummy_482_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object* v_mvarId_490_, lean_object* v___x_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; 
lean_inc(v_mvarId_490_);
v___x_497_ = l_Lean_MVarId_getType_x27(v_mvarId_490_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_500_ = lean_unsigned_to_nat(3u);
v___x_501_ = l_Lean_Expr_isAppOfArity(v_a_498_, v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v_a_498_);
lean_dec_ref(v___x_491_);
lean_dec(v_mvarId_490_);
v___x_502_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5);
v___x_503_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0(v___x_502_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v___f_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___f_512_; lean_object* v___x_513_; 
v___x_504_ = lean_box(v___x_501_);
v___f_505_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_505_, 0, v___x_504_);
v___x_506_ = l_Lean_Expr_appFn_x21(v_a_498_);
v___x_507_ = l_Lean_Expr_appArg_x21(v___x_506_);
lean_dec_ref(v___x_506_);
v___x_508_ = l_Lean_Expr_appArg_x21(v_a_498_);
lean_dec(v_a_498_);
v___x_509_ = 0;
v___x_510_ = lean_box(v___x_509_);
v___x_511_ = lean_box(v___x_501_);
lean_inc_ref_n(v___x_507_, 2);
v___f_512_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed), 11, 4);
lean_closure_set(v___f_512_, 0, v___x_507_);
lean_closure_set(v___f_512_, 1, v___x_491_);
lean_closure_set(v___f_512_, 2, v___x_510_);
lean_closure_set(v___f_512_, 3, v___x_511_);
v___x_513_ = l_Lean_Meta_delta_x3f(v___x_507_, v___f_505_, v___x_509_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
if (lean_obj_tag(v_a_514_) == 1)
{
lean_object* v_val_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v___x_507_);
v_val_515_ = lean_ctor_get(v_a_514_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_a_514_);
if (v_isSharedCheck_664_ == 0)
{
v___x_517_ = v_a_514_;
v_isShared_518_ = v_isSharedCheck_664_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_val_515_);
lean_dec(v_a_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_664_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_h_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___x_615_; 
lean_inc(v_val_515_);
v___x_615_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_val_515_, v___y_493_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = l_Lean_Expr_cleanupAnnotations(v_a_616_);
v___x_618_ = l_Lean_Expr_isApp(v___x_617_);
if (v___x_618_ == 0)
{
lean_dec_ref(v___x_617_);
v___y_594_ = v___y_492_;
v___y_595_ = v___y_493_;
v___y_596_ = v___y_494_;
v___y_597_ = v___y_495_;
goto v___jp_593_;
}
else
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = l_Lean_Expr_appFnCleanup___redArg(v___x_617_);
v___x_620_ = l_Lean_Expr_isApp(v___x_619_);
if (v___x_620_ == 0)
{
lean_dec_ref(v___x_619_);
v___y_594_ = v___y_492_;
v___y_595_ = v___y_493_;
v___y_596_ = v___y_494_;
v___y_597_ = v___y_495_;
goto v___jp_593_;
}
else
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = l_Lean_Expr_appFnCleanup___redArg(v___x_619_);
v___x_622_ = l_Lean_Expr_isApp(v___x_621_);
if (v___x_622_ == 0)
{
lean_dec_ref(v___x_621_);
v___y_594_ = v___y_492_;
v___y_595_ = v___y_493_;
v___y_596_ = v___y_494_;
v___y_597_ = v___y_495_;
goto v___jp_593_;
}
else
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = l_Lean_Expr_appFnCleanup___redArg(v___x_621_);
v___x_624_ = l_Lean_Expr_isApp(v___x_623_);
if (v___x_624_ == 0)
{
lean_dec_ref(v___x_623_);
v___y_594_ = v___y_492_;
v___y_595_ = v___y_493_;
v___y_596_ = v___y_494_;
v___y_597_ = v___y_495_;
goto v___jp_593_;
}
else
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = l_Lean_Expr_appFnCleanup___redArg(v___x_623_);
v___x_626_ = l_Lean_Expr_isApp(v___x_625_);
if (v___x_626_ == 0)
{
lean_dec_ref(v___x_625_);
v___y_594_ = v___y_492_;
v___y_595_ = v___y_493_;
v___y_596_ = v___y_494_;
v___y_597_ = v___y_495_;
goto v___jp_593_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = l_Lean_Expr_appFnCleanup___redArg(v___x_625_);
v___x_628_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14));
v___x_629_ = l_Lean_Expr_isConstOf(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; 
v___x_630_ = l_Lean_Expr_isApp(v___x_627_);
if (v___x_630_ == 0)
{
lean_dec_ref(v___x_627_);
v___y_594_ = v___y_492_;
v___y_595_ = v___y_493_;
v___y_596_ = v___y_494_;
v___y_597_ = v___y_495_;
goto v___jp_593_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_631_ = l_Lean_Expr_appFnCleanup___redArg(v___x_627_);
v___x_632_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15));
v___x_633_ = l_Lean_Expr_isConstOf(v___x_631_, v___x_632_);
lean_dec_ref(v___x_631_);
if (v___x_633_ == 0)
{
v___y_594_ = v___y_492_;
v___y_595_ = v___y_493_;
v___y_596_ = v___y_494_;
v___y_597_ = v___y_495_;
goto v___jp_593_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_dummy_638_; lean_object* v_nargs_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_del_object(v___x_517_);
v___x_634_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17));
v___x_635_ = l_Lean_Expr_getAppFn(v_val_515_);
v___x_636_ = l_Lean_Expr_constLevels_x21(v___x_635_);
lean_dec_ref(v___x_635_);
v___x_637_ = l_Lean_mkConst(v___x_634_, v___x_636_);
v_dummy_638_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_639_ = l_Lean_Expr_getAppNumArgs(v_val_515_);
lean_inc(v_nargs_639_);
v___x_640_ = lean_mk_array(v_nargs_639_, v_dummy_638_);
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_sub(v_nargs_639_, v___x_641_);
lean_dec(v_nargs_639_);
lean_inc(v_val_515_);
v___x_643_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_515_, v___x_640_, v___x_642_);
v___x_644_ = l_Lean_mkAppN(v___x_637_, v___x_643_);
lean_dec_ref(v___x_643_);
v_h_520_ = v___x_644_;
v___y_521_ = v___y_492_;
v___y_522_ = v___y_493_;
v___y_523_ = v___y_494_;
v___y_524_ = v___y_495_;
goto v___jp_519_;
}
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_dummy_649_; lean_object* v_nargs_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec_ref(v___x_627_);
lean_del_object(v___x_517_);
v___x_645_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19));
v___x_646_ = l_Lean_Expr_getAppFn(v_val_515_);
v___x_647_ = l_Lean_Expr_constLevels_x21(v___x_646_);
lean_dec_ref(v___x_646_);
v___x_648_ = l_Lean_mkConst(v___x_645_, v___x_647_);
v_dummy_649_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_650_ = l_Lean_Expr_getAppNumArgs(v_val_515_);
lean_inc(v_nargs_650_);
v___x_651_ = lean_mk_array(v_nargs_650_, v_dummy_649_);
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_sub(v_nargs_650_, v___x_652_);
lean_dec(v_nargs_650_);
lean_inc(v_val_515_);
v___x_654_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_515_, v___x_651_, v___x_653_);
v___x_655_ = l_Lean_mkAppN(v___x_648_, v___x_654_);
lean_dec_ref(v___x_654_);
v_h_520_ = v___x_655_;
v___y_521_ = v___y_492_;
v___y_522_ = v___y_493_;
v___y_523_ = v___y_494_;
v___y_524_ = v___y_495_;
goto v___jp_519_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_del_object(v___x_517_);
lean_dec(v_val_515_);
lean_dec_ref(v___f_512_);
lean_dec_ref(v___x_508_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v_mvarId_490_);
v_a_656_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_615_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_615_);
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
v___jp_519_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_525_ = l_Lean_Expr_appFn_x21(v_val_515_);
v___x_526_ = l_Lean_Expr_appArg_x21(v___x_525_);
lean_dec_ref(v___x_525_);
v___x_527_ = l_Lean_Expr_appArg_x21(v_val_515_);
lean_dec(v_val_515_);
lean_inc_ref(v___x_527_);
lean_inc_ref(v___x_526_);
v___x_528_ = l_Lean_Expr_app___override(v___x_526_, v___x_527_);
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
lean_inc(v___y_522_);
lean_inc_ref(v___y_521_);
v___x_529_ = lean_infer_type(v___x_528_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_529_, 1);
v___x_531_ = l_Lean_Expr_bindingDomain_x21(v_a_530_);
lean_dec(v_a_530_);
v___x_532_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_533_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_531_, v___x_532_, v___f_512_, v___x_509_, v___x_509_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = l_Lean_mkAppB(v___x_526_, v___x_527_, v_a_534_);
v___x_536_ = l_Lean_Meta_mkEq(v___x_535_, v___x_508_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
v___x_538_ = lean_box(0);
v___x_539_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_537_, v___x_538_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc_n(v_a_540_, 2);
lean_dec_ref_known(v___x_539_, 1);
v___x_541_ = l_Lean_Meta_mkEqTrans(v_h_520_, v_a_540_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_521_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
v___x_543_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_490_, v_a_542_, v___y_522_);
lean_dec(v___y_522_);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v___x_543_, 0);
lean_dec(v_unused_552_);
v___x_545_ = v___x_543_;
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
else
{
lean_dec(v___x_543_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = l_Lean_Expr_mvarId_x21(v_a_540_);
lean_dec(v_a_540_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v_a_540_);
lean_dec(v___y_522_);
lean_dec(v_mvarId_490_);
v_a_553_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_541_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_541_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_h_520_);
lean_dec(v_mvarId_490_);
v_a_561_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_539_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_539_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_h_520_);
lean_dec(v_mvarId_490_);
v_a_569_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_536_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_536_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec_ref(v___x_527_);
lean_dec_ref(v___x_526_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_h_520_);
lean_dec_ref(v___x_508_);
lean_dec(v_mvarId_490_);
v_a_577_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_533_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_533_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v___x_527_);
lean_dec_ref(v___x_526_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_h_520_);
lean_dec_ref(v___f_512_);
lean_dec_ref(v___x_508_);
lean_dec(v_mvarId_490_);
v_a_585_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_529_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_529_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
v___jp_593_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8));
v___x_599_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10);
lean_inc(v_val_515_);
v___x_600_ = l_Lean_MessageData_ofExpr(v_val_515_);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_601_);
v___x_603_ = v___x_517_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_614_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; 
lean_inc(v_mvarId_490_);
v___x_604_ = l_Lean_Meta_throwTacticEx___redArg(v___x_598_, v_mvarId_490_, v___x_603_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v_h_520_ = v_a_605_;
v___y_521_ = v___y_594_;
v___y_522_ = v___y_595_;
v___y_523_ = v___y_596_;
v___y_524_ = v___y_597_;
goto v___jp_519_;
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v_val_515_);
lean_dec_ref(v___f_512_);
lean_dec_ref(v___x_508_);
lean_dec(v_mvarId_490_);
v_a_606_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_604_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_604_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_a_514_);
lean_dec_ref(v___f_512_);
lean_dec_ref(v___x_508_);
lean_dec(v_mvarId_490_);
v___x_665_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21);
v___x_666_ = l_Lean_MessageData_ofExpr(v___x_507_);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_667_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
return v___x_668_;
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v___f_512_);
lean_dec_ref(v___x_508_);
lean_dec_ref(v___x_507_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v_mvarId_490_);
v_a_669_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_513_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_513_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec_ref(v___x_491_);
lean_dec(v_mvarId_490_);
v_a_677_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_497_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_497_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_490_ = stack[0].m_obj;
lean_object* v___x_491_ = stack[1].m_obj;
lean_object* v___y_492_ = stack[2].m_obj;
lean_object* v___y_493_ = stack[3].m_obj;
lean_object* v___y_494_ = stack[4].m_obj;
lean_object* v___y_495_ = stack[5].m_obj;
lean_object* v_res_685_;
v_res_685_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(v_mvarId_490_, v___x_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed(lean_object* v_mvarId_686_, lean_object* v___x_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(v_mvarId_686_, v___x_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
return v_res_693_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(lean_object* v_mvarId_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_700_; lean_object* v___f_701_; lean_object* v___x_702_; 
v___x_700_ = l_Lean_instInhabitedExpr;
lean_inc(v_mvarId_694_);
v___f_701_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___boxed), 7, 2);
lean_closure_set(v___f_701_, 0, v_mvarId_694_);
lean_closure_set(v___f_701_, 1, v___x_700_);
v___x_702_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__4___redArg(v_mvarId_694_, v___f_701_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
return v___x_702_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_694_ = stack[0].m_obj;
lean_object* v_a_695_ = stack[1].m_obj;
lean_object* v_a_696_ = stack[2].m_obj;
lean_object* v_a_697_ = stack[3].m_obj;
lean_object* v_a_698_ = stack[4].m_obj;
lean_object* v_res_703_;
v_res_703_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
stack->m_obj
 = v_res_703_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___boxed(lean_object* v_mvarId_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
return v_res_710_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(lean_object* v_mvarId_711_, lean_object* v_val_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___redArg(v_mvarId_711_, v_val_712_, v___y_714_);
return v___x_718_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_711_ = stack[0].m_obj;
lean_object* v_val_712_ = stack[1].m_obj;
lean_object* v___y_713_ = stack[2].m_obj;
lean_object* v___y_714_ = stack[3].m_obj;
lean_object* v___y_715_ = stack[4].m_obj;
lean_object* v___y_716_ = stack[5].m_obj;
lean_object* v_res_719_;
v_res_719_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(v_mvarId_711_, v_val_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
stack->m_obj
 = v_res_719_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2___boxed(lean_object* v_mvarId_720_, lean_object* v_val_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2(v_mvarId_720_, v_val_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_727_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(lean_object* v_00_u03b1_728_, lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_729_ = stack[1].m_obj;
lean_object* v___y_730_ = stack[2].m_obj;
lean_object* v___y_731_ = stack[3].m_obj;
lean_object* v___y_732_ = stack[4].m_obj;
lean_object* v___y_733_ = stack[5].m_obj;
lean_object* v_res_736_;
v_res_736_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(lean_box(0), v_msg_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
stack->m_obj
 = v_res_736_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___boxed(lean_object* v_00_u03b1_737_, lean_object* v_msg_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3(v_00_u03b1_737_, v_msg_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2(lean_object* v_00_u03b2_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2___redArg(v_x_746_, v_x_747_, v_x_748_);
return v___x_749_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_750_, lean_object* v_x_751_, size_t v_x_752_, size_t v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___redArg(v_x_751_, v_x_752_, v_x_753_, v_x_754_, v_x_755_);
return v___x_756_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_751_ = stack[1].m_obj;
size_t v_x_752_ = stack[2].m_num;
size_t v_x_753_ = stack[3].m_num;
lean_object* v_x_754_ = stack[4].m_obj;
lean_object* v_x_755_ = stack[5].m_obj;
lean_object* v_res_757_;
v_res_757_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(lean_box(0), v_x_751_, v_x_752_, v_x_753_, v_x_754_, v_x_755_);
stack->m_obj
 = v_res_757_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
size_t v_x_7517__boxed_764_; size_t v_x_7518__boxed_765_; lean_object* v_res_766_; 
v_x_7517__boxed_764_ = lean_unbox_usize(v_x_760_);
lean_dec(v_x_760_);
v_x_7518__boxed_765_ = lean_unbox_usize(v_x_761_);
lean_dec(v_x_761_);
v_res_766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4(v_00_u03b2_758_, v_x_759_, v_x_7517__boxed_764_, v_x_7518__boxed_765_, v_x_762_, v_x_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_767_, lean_object* v_n_768_, lean_object* v_k_769_, lean_object* v_v_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7___redArg(v_n_768_, v_k_769_, v_v_770_);
return v___x_771_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_772_, size_t v_depth_773_, lean_object* v_keys_774_, lean_object* v_vals_775_, lean_object* v_heq_776_, lean_object* v_i_777_, lean_object* v_entries_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_773_, v_keys_774_, v_vals_775_, v_i_777_, v_entries_778_);
return v___x_779_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_depth_773_ = stack[1].m_num;
lean_object* v_keys_774_ = stack[2].m_obj;
lean_object* v_vals_775_ = stack[3].m_obj;
lean_object* v_i_777_ = stack[5].m_obj;
lean_object* v_entries_778_ = stack[6].m_obj;
lean_object* v_res_780_;
v_res_780_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(lean_box(0), v_depth_773_, v_keys_774_, v_vals_775_, lean_box(0), v_i_777_, v_entries_778_);
stack->m_obj
 = v_res_780_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_781_, lean_object* v_depth_782_, lean_object* v_keys_783_, lean_object* v_vals_784_, lean_object* v_heq_785_, lean_object* v_i_786_, lean_object* v_entries_787_){
_start:
{
size_t v_depth_boxed_788_; lean_object* v_res_789_; 
v_depth_boxed_788_ = lean_unbox_usize(v_depth_782_);
lean_dec(v_depth_782_);
v_res_789_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_781_, v_depth_boxed_788_, v_keys_783_, v_vals_784_, v_heq_785_, v_i_786_, v_entries_787_);
lean_dec_ref(v_vals_784_);
lean_dec_ref(v_keys_783_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_791_, v_x_792_, v_x_793_, v_x_794_);
return v___x_795_;
}
}
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(lean_object* v_e_796_, lean_object* v_maxFVars_797_, lean_object* v_k_798_, uint8_t v_cleanupAnnotations_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___f_805_; uint8_t v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___f_805_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_805_, 0, v_k_798_);
v___x_806_ = 1;
v___x_807_ = 0;
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v_maxFVars_797_);
v___x_809_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_796_, v___x_806_, v___x_807_, v___x_806_, v___x_807_, v___x_808_, v___f_805_, v_cleanupAnnotations_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec_ref_known(v___x_808_, 1);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_809_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_809_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_796_ = stack[0].m_obj;
lean_object* v_maxFVars_797_ = stack[1].m_obj;
lean_object* v_k_798_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_799_ = stack[3].m_num;
lean_object* v___y_800_ = stack[4].m_obj;
lean_object* v___y_801_ = stack[5].m_obj;
lean_object* v___y_802_ = stack[6].m_obj;
lean_object* v___y_803_ = stack[7].m_obj;
lean_object* v_res_826_;
v_res_826_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_796_, v_maxFVars_797_, v_k_798_, v_cleanupAnnotations_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
stack->m_obj
 = v_res_826_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg___boxed(lean_object* v_e_827_, lean_object* v_maxFVars_828_, lean_object* v_k_829_, lean_object* v_cleanupAnnotations_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_836_; lean_object* v_res_837_; 
v_cleanupAnnotations_boxed_836_ = lean_unbox(v_cleanupAnnotations_830_);
v_res_837_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_827_, v_maxFVars_828_, v_k_829_, v_cleanupAnnotations_boxed_836_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_837_;
}
}
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(lean_object* v_00_u03b1_838_, lean_object* v_e_839_, lean_object* v_maxFVars_840_, lean_object* v_k_841_, uint8_t v_cleanupAnnotations_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_e_839_, v_maxFVars_840_, v_k_841_, v_cleanupAnnotations_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
return v___x_848_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_839_ = stack[1].m_obj;
lean_object* v_maxFVars_840_ = stack[2].m_obj;
lean_object* v_k_841_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_842_ = stack[4].m_num;
lean_object* v___y_843_ = stack[5].m_obj;
lean_object* v___y_844_ = stack[6].m_obj;
lean_object* v___y_845_ = stack[7].m_obj;
lean_object* v___y_846_ = stack[8].m_obj;
lean_object* v_res_849_;
v_res_849_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(lean_box(0), v_e_839_, v_maxFVars_840_, v_k_841_, v_cleanupAnnotations_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
stack->m_obj
 = v_res_849_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___boxed(lean_object* v_00_u03b1_850_, lean_object* v_e_851_, lean_object* v_maxFVars_852_, lean_object* v_k_853_, lean_object* v_cleanupAnnotations_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_860_; lean_object* v_res_861_; 
v_cleanupAnnotations_boxed_860_ = lean_unbox(v_cleanupAnnotations_854_);
v_res_861_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0(v_00_u03b1_850_, v_e_851_, v_maxFVars_852_, v_k_853_, v_cleanupAnnotations_boxed_860_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_861_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(lean_object* v___x_862_, lean_object* v_xs_863_, lean_object* v_t_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_873_ = lean_array_get_size(v_xs_863_);
v___x_874_ = lean_nat_dec_eq(v___x_873_, v___x_862_);
if (v___x_874_ == 0)
{
goto v___jp_870_;
}
else
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_Expr_isForall(v_t_864_);
if (v___x_875_ == 0)
{
goto v___jp_870_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_876_ = l_Lean_Expr_bindingBody_x21(v_t_864_);
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_expr_has_loose_bvar(v___x_876_, v___x_877_);
if (v___x_878_ == 0)
{
uint8_t v___x_879_; lean_object* v___x_880_; 
v___x_879_ = 1;
v___x_880_ = l_Lean_Meta_mkLambdaFVars(v_xs_863_, v___x_876_, v___x_878_, v___x_875_, v___x_878_, v___x_875_, v___x_879_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_889_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_889_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_885_, 0, v_a_881_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_a_890_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_880_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_880_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_dec_ref(v___x_876_);
goto v___jp_870_;
}
}
}
v___jp_870_:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_box(0);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_862_ = stack[0].m_obj;
lean_object* v_xs_863_ = stack[1].m_obj;
lean_object* v_t_864_ = stack[2].m_obj;
lean_object* v___y_865_ = stack[3].m_obj;
lean_object* v___y_866_ = stack[4].m_obj;
lean_object* v___y_867_ = stack[5].m_obj;
lean_object* v___y_868_ = stack[6].m_obj;
lean_object* v_res_898_;
v_res_898_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(v___x_862_, v_xs_863_, v_t_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
stack->m_obj
 = v_res_898_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed(lean_object* v___x_899_, lean_object* v_xs_900_, lean_object* v_t_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0(v___x_899_, v_xs_900_, v_t_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_t_901_);
lean_dec_ref(v_xs_900_);
lean_dec(v___x_899_);
return v_res_907_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(lean_object* v_matcherApp_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_motive_914_; lean_object* v_discrs_915_; lean_object* v___x_916_; lean_object* v___f_917_; uint8_t v___x_918_; lean_object* v___x_919_; 
v_motive_914_ = lean_ctor_get(v_matcherApp_908_, 4);
lean_inc_ref(v_motive_914_);
v_discrs_915_ = lean_ctor_get(v_matcherApp_908_, 5);
lean_inc_ref(v_discrs_915_);
lean_dec_ref(v_matcherApp_908_);
v___x_916_ = lean_array_get_size(v_discrs_915_);
lean_dec_ref(v_discrs_915_);
v___f_917_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___lam__0___boxed), 8, 1);
lean_closure_set(v___f_917_, 0, v___x_916_);
v___x_918_ = 0;
v___x_919_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_motive_914_, v___x_916_, v___f_917_, v___x_918_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_919_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_908_ = stack[0].m_obj;
lean_object* v_a_909_ = stack[1].m_obj;
lean_object* v_a_910_ = stack[2].m_obj;
lean_object* v_a_911_ = stack[3].m_obj;
lean_object* v_a_912_ = stack[4].m_obj;
lean_object* v_res_920_;
v_res_920_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_matcherApp_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
stack->m_obj
 = v_res_920_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive___boxed(lean_object* v_matcherApp_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_matcherApp_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
return v_res_927_;
}
}
lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(lean_object* v_e_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; lean_object* v_env_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_931_ = lean_st_ref_get(v___y_929_);
v_env_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc_ref(v_env_932_);
lean_dec(v___x_931_);
v___x_933_ = l_Lean_Meta_isMatcherAppCore(v_env_932_, v_e_928_);
v___x_934_ = lean_box(v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_928_ = stack[0].m_obj;
lean_object* v___y_929_ = stack[1].m_obj;
lean_object* v_res_936_;
v_res_936_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_928_, v___y_929_);
stack->m_obj
 = v_res_936_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg___boxed(lean_object* v_e_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v_e_937_);
return v_res_940_;
}
}
lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(lean_object* v_e_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_941_, v___y_945_);
return v___x_947_;
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_941_ = stack[0].m_obj;
lean_object* v___y_942_ = stack[1].m_obj;
lean_object* v___y_943_ = stack[2].m_obj;
lean_object* v___y_944_ = stack[3].m_obj;
lean_object* v___y_945_ = stack[4].m_obj;
lean_object* v_res_948_;
v_res_948_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(v_e_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___boxed(lean_object* v_e_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0(v_e_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v_e_949_);
return v_res_955_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(lean_object* v_msg_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___f_962_; lean_object* v___x_613__overap_963_; lean_object* v___x_964_; 
v___f_962_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_613__overap_963_ = lean_panic_fn_borrowed(v___f_962_, v_msg_956_);
lean_inc(v___y_960_);
lean_inc_ref(v___y_959_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
v___x_964_ = lean_apply_5(v___x_613__overap_963_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, lean_box(0));
return v___x_964_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_956_ = stack[0].m_obj;
lean_object* v___y_957_ = stack[1].m_obj;
lean_object* v___y_958_ = stack[2].m_obj;
lean_object* v___y_959_ = stack[3].m_obj;
lean_object* v___y_960_ = stack[4].m_obj;
lean_object* v_res_965_;
v_res_965_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v_msg_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
stack->m_obj
 = v_res_965_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1___boxed(lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v_msg_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_972_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(size_t v_sz_973_, size_t v_i_974_, lean_object* v_bs_975_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = lean_usize_dec_lt(v_i_974_, v_sz_973_);
if (v___x_976_ == 0)
{
return v_bs_975_;
}
else
{
lean_object* v_v_977_; lean_object* v_toInductionSubgoal_978_; lean_object* v_mvarId_979_; lean_object* v___x_980_; lean_object* v_bs_x27_981_; size_t v___x_982_; size_t v___x_983_; lean_object* v___x_984_; 
v_v_977_ = lean_array_uget_borrowed(v_bs_975_, v_i_974_);
v_toInductionSubgoal_978_ = lean_ctor_get(v_v_977_, 0);
v_mvarId_979_ = lean_ctor_get(v_toInductionSubgoal_978_, 0);
lean_inc(v_mvarId_979_);
v___x_980_ = lean_unsigned_to_nat(0u);
v_bs_x27_981_ = lean_array_uset(v_bs_975_, v_i_974_, v___x_980_);
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_add(v_i_974_, v___x_982_);
v___x_984_ = lean_array_uset(v_bs_x27_981_, v_i_974_, v_mvarId_979_);
v_i_974_ = v___x_983_;
v_bs_975_ = v___x_984_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_973_ = stack[0].m_num;
size_t v_i_974_ = stack[1].m_num;
lean_object* v_bs_975_ = stack[2].m_obj;
lean_object* v_res_986_;
v_res_986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_973_, v_i_974_, v_bs_975_);
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2___boxed(lean_object* v_sz_987_, lean_object* v_i_988_, lean_object* v_bs_989_){
_start:
{
size_t v_sz_boxed_990_; size_t v_i_boxed_991_; lean_object* v_res_992_; 
v_sz_boxed_990_ = lean_unbox_usize(v_sz_987_);
lean_dec(v_sz_987_);
v_i_boxed_991_ = lean_unbox_usize(v_i_988_);
lean_dec(v_i_988_);
v_res_992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_boxed_990_, v_i_boxed_991_, v_bs_989_);
return v_res_992_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_995_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__1));
v___x_996_ = lean_unsigned_to_nat(4u);
v___x_997_ = lean_unsigned_to_nat(79u);
v___x_998_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__0));
v___x_999_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_1000_ = l_mkPanicMessageWithDecl(v___x_999_, v___x_998_, v___x_997_, v___x_996_, v___x_995_);
return v___x_1000_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(lean_object* v_mvarId_1003_, lean_object* v_e_1004_, lean_object* v_matcherInfo_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_a_1013_; uint8_t v___x_1014_; 
v___x_1011_ = l_Lean_instInhabitedExpr;
v___x_1012_ = l_Lean_Meta_isMatcherApp___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__0___redArg(v_e_1004_, v_a_1009_);
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = lean_unbox(v_a_1013_);
if (v___x_1014_ == 0)
{
lean_object* v_numParams_1015_; lean_object* v_numDiscrs_1016_; lean_object* v_nargs_1017_; lean_object* v_dummy_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_numParams_1015_ = lean_ctor_get(v_matcherInfo_1005_, 0);
v_numDiscrs_1016_ = lean_ctor_get(v_matcherInfo_1005_, 1);
v_nargs_1017_ = l_Lean_Expr_getAppNumArgs(v_e_1004_);
v_dummy_1018_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_1017_);
v___x_1019_ = lean_mk_array(v_nargs_1017_, v_dummy_1018_);
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_sub(v_nargs_1017_, v___x_1020_);
lean_dec(v_nargs_1017_);
v___x_1022_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1004_, v___x_1019_, v___x_1021_);
v___x_1023_ = lean_nat_add(v_numParams_1015_, v_numDiscrs_1016_);
v___x_1024_ = lean_array_get(v___x_1011_, v___x_1022_, v___x_1023_);
lean_dec(v___x_1023_);
lean_dec_ref(v___x_1022_);
v___x_1025_ = l_Lean_Expr_isFVar(v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec(v___x_1024_);
lean_dec(v_a_1013_);
lean_dec(v_mvarId_1003_);
v___x_1026_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__2);
v___x_1027_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__1(v___x_1026_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1028_ = l_Lean_Expr_fvarId_x21(v___x_1024_);
lean_dec(v___x_1024_);
v___x_1029_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___closed__3));
v___x_1030_ = lean_box(0);
v___x_1031_ = lean_unbox(v_a_1013_);
lean_dec(v_a_1013_);
v___x_1032_ = l_Lean_MVarId_cases(v_mvarId_1003_, v___x_1028_, v___x_1029_, v___x_1031_, v___x_1030_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1044_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
size_t v_sz_1037_; size_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v_sz_1037_ = lean_array_size(v_a_1033_);
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_spec__2(v_sz_1037_, v___x_1038_, v_a_1033_);
v___x_1040_ = lean_array_to_list(v___x_1039_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1040_);
v___x_1042_ = v___x_1035_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
v_a_1045_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1032_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1032_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
else
{
lean_object* v___x_1053_; 
lean_dec(v_a_1013_);
v___x_1053_ = l_Lean_Meta_Split_splitMatch(v_mvarId_1003_, v_e_1004_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
return v___x_1053_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1003_ = stack[0].m_obj;
lean_object* v_e_1004_ = stack[1].m_obj;
lean_object* v_matcherInfo_1005_ = stack[2].m_obj;
lean_object* v_a_1006_ = stack[3].m_obj;
lean_object* v_a_1007_ = stack[4].m_obj;
lean_object* v_a_1008_ = stack[5].m_obj;
lean_object* v_a_1009_ = stack[6].m_obj;
lean_object* v_res_1054_;
v_res_1054_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v_mvarId_1003_, v_e_1004_, v_matcherInfo_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
stack->m_obj
 = v_res_1054_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn___boxed(lean_object* v_mvarId_1055_, lean_object* v_e_1056_, lean_object* v_matcherInfo_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v_mvarId_1055_, v_e_1056_, v_matcherInfo_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec_ref(v_matcherInfo_1057_);
return v_res_1063_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___f_1070_; lean_object* v___x_11820__overap_1071_; lean_object* v___x_1072_; 
v___f_1070_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__0___closed__0));
v___x_11820__overap_1071_ = lean_panic_fn_borrowed(v___f_1070_, v_msg_1064_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
v___x_1072_ = lean_apply_5(v___x_11820__overap_1071_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, lean_box(0));
return v___x_1072_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1064_ = stack[0].m_obj;
lean_object* v___y_1065_ = stack[1].m_obj;
lean_object* v___y_1066_ = stack[2].m_obj;
lean_object* v___y_1067_ = stack[3].m_obj;
lean_object* v___y_1068_ = stack[4].m_obj;
lean_object* v_res_1073_;
v_res_1073_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v_msg_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
stack->m_obj
 = v_res_1073_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1___boxed(lean_object* v_msg_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v_msg_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1080_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(lean_object* v_type_1081_, lean_object* v_k_1082_, uint8_t v_cleanupAnnotations_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___f_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___f_1089_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1089_, 0, v_k_1082_);
v___x_1090_ = 0;
v___x_1091_ = lean_box(0);
v___x_1092_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1090_, v___x_1091_, v_type_1081_, v___f_1089_, v_cleanupAnnotations_1083_, v___x_1090_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1101_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1092_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1092_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1081_ = stack[0].m_obj;
lean_object* v_k_1082_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_1083_ = stack[2].m_num;
lean_object* v___y_1084_ = stack[3].m_obj;
lean_object* v___y_1085_ = stack[4].m_obj;
lean_object* v___y_1086_ = stack[5].m_obj;
lean_object* v___y_1087_ = stack[6].m_obj;
lean_object* v_res_1109_;
v_res_1109_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1081_, v_k_1082_, v_cleanupAnnotations_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg___boxed(lean_object* v_type_1110_, lean_object* v_k_1111_, lean_object* v_cleanupAnnotations_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1118_; lean_object* v_res_1119_; 
v_cleanupAnnotations_boxed_1118_ = lean_unbox(v_cleanupAnnotations_1112_);
v_res_1119_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1110_, v_k_1111_, v_cleanupAnnotations_boxed_1118_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
return v_res_1119_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(lean_object* v_00_u03b1_1120_, lean_object* v_type_1121_, lean_object* v_k_1122_, uint8_t v_cleanupAnnotations_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_type_1121_, v_k_1122_, v_cleanupAnnotations_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v___x_1129_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1121_ = stack[1].m_obj;
lean_object* v_k_1122_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1123_ = stack[3].m_num;
lean_object* v___y_1124_ = stack[4].m_obj;
lean_object* v___y_1125_ = stack[5].m_obj;
lean_object* v___y_1126_ = stack[6].m_obj;
lean_object* v___y_1127_ = stack[7].m_obj;
lean_object* v_res_1130_;
v_res_1130_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(lean_box(0), v_type_1121_, v_k_1122_, v_cleanupAnnotations_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
stack->m_obj
 = v_res_1130_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___boxed(lean_object* v_00_u03b1_1131_, lean_object* v_type_1132_, lean_object* v_k_1133_, lean_object* v_cleanupAnnotations_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1140_; lean_object* v_res_1141_; 
v_cleanupAnnotations_boxed_1140_ = lean_unbox(v_cleanupAnnotations_1134_);
v_res_1141_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2(v_00_u03b1_1131_, v_type_1132_, v_k_1133_, v_cleanupAnnotations_boxed_1140_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
return v_res_1141_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(lean_object* v_e_1142_, lean_object* v___y_1143_){
_start:
{
uint8_t v___x_1145_; 
v___x_1145_ = l_Lean_Expr_hasMVar(v_e_1142_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_e_1142_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; lean_object* v_mctx_1148_; lean_object* v___x_1149_; lean_object* v_fst_1150_; lean_object* v_snd_1151_; lean_object* v___x_1152_; lean_object* v_cache_1153_; lean_object* v_zetaDeltaFVarIds_1154_; lean_object* v_postponed_1155_; lean_object* v_diag_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1165_; 
v___x_1147_ = lean_st_ref_get(v___y_1143_);
v_mctx_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc_ref(v_mctx_1148_);
lean_dec(v___x_1147_);
v___x_1149_ = l_Lean_instantiateMVarsCore(v_mctx_1148_, v_e_1142_);
v_fst_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_fst_1150_);
v_snd_1151_ = lean_ctor_get(v___x_1149_, 1);
lean_inc(v_snd_1151_);
lean_dec_ref(v___x_1149_);
v___x_1152_ = lean_st_ref_take(v___y_1143_);
v_cache_1153_ = lean_ctor_get(v___x_1152_, 1);
v_zetaDeltaFVarIds_1154_ = lean_ctor_get(v___x_1152_, 2);
v_postponed_1155_ = lean_ctor_get(v___x_1152_, 3);
v_diag_1156_ = lean_ctor_get(v___x_1152_, 4);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1152_, 0);
lean_dec(v_unused_1166_);
v___x_1158_ = v___x_1152_;
v_isShared_1159_ = v_isSharedCheck_1165_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_diag_1156_);
lean_inc(v_postponed_1155_);
lean_inc(v_zetaDeltaFVarIds_1154_);
lean_inc(v_cache_1153_);
lean_dec(v___x_1152_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1165_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v_snd_1151_);
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_snd_1151_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_cache_1153_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_zetaDeltaFVarIds_1154_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_postponed_1155_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_diag_1156_);
v___x_1161_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_st_ref_put(v___y_1143_, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v_fst_1150_);
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1142_ = stack[0].m_obj;
lean_object* v___y_1143_ = stack[1].m_obj;
lean_object* v_res_1167_;
v_res_1167_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1142_, v___y_1143_);
stack->m_obj
 = v_res_1167_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg___boxed(lean_object* v_e_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1168_, v___y_1169_);
lean_dec(v___y_1169_);
return v_res_1171_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(lean_object* v_e_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_e_1172_, v___y_1174_);
return v___x_1178_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1172_ = stack[0].m_obj;
lean_object* v___y_1173_ = stack[1].m_obj;
lean_object* v___y_1174_ = stack[2].m_obj;
lean_object* v___y_1175_ = stack[3].m_obj;
lean_object* v___y_1176_ = stack[4].m_obj;
lean_object* v_res_1179_;
v_res_1179_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(v_e_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
stack->m_obj
 = v_res_1179_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___boxed(lean_object* v_e_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6(v_e_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1186_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(lean_object* v_x_1187_, lean_object* v_motiveBody_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_Meta_getLevel(v_motiveBody_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1187_ = stack[0].m_obj;
lean_object* v_motiveBody_1188_ = stack[1].m_obj;
lean_object* v___y_1189_ = stack[2].m_obj;
lean_object* v___y_1190_ = stack[3].m_obj;
lean_object* v___y_1191_ = stack[4].m_obj;
lean_object* v___y_1192_ = stack[5].m_obj;
lean_object* v_res_1195_;
v_res_1195_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(v_x_1187_, v_motiveBody_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
stack->m_obj
 = v_res_1195_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0___boxed(lean_object* v_x_1196_, lean_object* v_motiveBody_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__0(v_x_1196_, v_motiveBody_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v_x_1196_);
return v_res_1203_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(lean_object* v___x_1204_, lean_object* v___x_1205_, lean_object* v_alpha_1206_, uint8_t v___x_1207_, lean_object* v_xs_1208_, lean_object* v_x_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; uint8_t v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1215_ = l_Lean_Level_ofNat(v___x_1204_);
v___x_1216_ = l_Lean_Expr_sort___override(v___x_1215_);
v___x_1217_ = l_Lean_Expr_forallE___override(v___x_1205_, v_alpha_1206_, v___x_1216_, v___x_1207_);
v___x_1218_ = 0;
v___x_1219_ = 1;
v___x_1220_ = 1;
v___x_1221_ = l_Lean_Meta_mkForallFVars(v_xs_1208_, v___x_1217_, v___x_1218_, v___x_1219_, v___x_1219_, v___x_1220_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1221_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1204_ = stack[0].m_obj;
lean_object* v___x_1205_ = stack[1].m_obj;
lean_object* v_alpha_1206_ = stack[2].m_obj;
uint8_t v___x_1207_ = stack[3].m_num;
lean_object* v_xs_1208_ = stack[4].m_obj;
lean_object* v_x_1209_ = stack[5].m_obj;
lean_object* v___y_1210_ = stack[6].m_obj;
lean_object* v___y_1211_ = stack[7].m_obj;
lean_object* v___y_1212_ = stack[8].m_obj;
lean_object* v___y_1213_ = stack[9].m_obj;
lean_object* v_res_1222_;
v_res_1222_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(v___x_1204_, v___x_1205_, v_alpha_1206_, v___x_1207_, v_xs_1208_, v_x_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
stack->m_obj
 = v_res_1222_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed(lean_object* v___x_1223_, lean_object* v___x_1224_, lean_object* v_alpha_1225_, lean_object* v___x_1226_, lean_object* v_xs_1227_, lean_object* v_x_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
uint8_t v___x_16114__boxed_1234_; lean_object* v_res_1235_; 
v___x_16114__boxed_1234_ = lean_unbox(v___x_1226_);
v_res_1235_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1(v___x_1223_, v___x_1224_, v_alpha_1225_, v___x_16114__boxed_1234_, v_xs_1227_, v_x_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v_x_1228_);
lean_dec_ref(v_xs_1227_);
lean_dec(v___x_1223_);
return v_res_1235_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(lean_object* v___x_1242_, lean_object* v___x_1243_, lean_object* v_rel_1244_, lean_object* v___x_1245_, lean_object* v_beta_1246_, uint8_t v___x_1247_, lean_object* v_alpha_1248_, uint8_t v___x_1249_, lean_object* v_xs_1250_, lean_object* v_x_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1257_ = l_Lean_mkAppN(v___x_1242_, v_xs_1250_);
v___x_1258_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_xs_1250_);
v___x_1260_ = lean_array_push(v_xs_1250_, v___x_1243_);
v___x_1261_ = l_Lean_mkAppN(v_rel_1244_, v___x_1260_);
lean_dec_ref(v___x_1260_);
v___x_1262_ = l_Lean_Expr_bvar___override(v___x_1245_);
v___x_1263_ = l_Lean_Expr_app___override(v_beta_1246_, v___x_1262_);
v___x_1264_ = l_Lean_Expr_forallE___override(v___x_1259_, v___x_1261_, v___x_1263_, v___x_1247_);
v___x_1265_ = l_Lean_Expr_forallE___override(v___x_1258_, v_alpha_1248_, v___x_1264_, v___x_1247_);
v___x_1266_ = l_Lean_mkArrow(v___x_1265_, v___x_1257_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; uint8_t v___x_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1268_ = 1;
v___x_1269_ = 1;
v___x_1270_ = l_Lean_Meta_mkLambdaFVars(v_xs_1250_, v_a_1267_, v___x_1249_, v___x_1268_, v___x_1249_, v___x_1268_, v___x_1269_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec_ref(v_xs_1250_);
return v___x_1270_;
}
else
{
lean_dec_ref(v_xs_1250_);
return v___x_1266_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1242_ = stack[0].m_obj;
lean_object* v___x_1243_ = stack[1].m_obj;
lean_object* v_rel_1244_ = stack[2].m_obj;
lean_object* v___x_1245_ = stack[3].m_obj;
lean_object* v_beta_1246_ = stack[4].m_obj;
uint8_t v___x_1247_ = stack[5].m_num;
lean_object* v_alpha_1248_ = stack[6].m_obj;
uint8_t v___x_1249_ = stack[7].m_num;
lean_object* v_xs_1250_ = stack[8].m_obj;
lean_object* v_x_1251_ = stack[9].m_obj;
lean_object* v___y_1252_ = stack[10].m_obj;
lean_object* v___y_1253_ = stack[11].m_obj;
lean_object* v___y_1254_ = stack[12].m_obj;
lean_object* v___y_1255_ = stack[13].m_obj;
lean_object* v_res_1271_;
v_res_1271_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(v___x_1242_, v___x_1243_, v_rel_1244_, v___x_1245_, v_beta_1246_, v___x_1247_, v_alpha_1248_, v___x_1249_, v_xs_1250_, v_x_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
stack->m_obj
 = v_res_1271_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed(lean_object* v___x_1272_, lean_object* v___x_1273_, lean_object* v_rel_1274_, lean_object* v___x_1275_, lean_object* v_beta_1276_, lean_object* v___x_1277_, lean_object* v_alpha_1278_, lean_object* v___x_1279_, lean_object* v_xs_1280_, lean_object* v_x_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
uint8_t v___x_16193__boxed_1287_; uint8_t v___x_16194__boxed_1288_; lean_object* v_res_1289_; 
v___x_16193__boxed_1287_ = lean_unbox(v___x_1277_);
v___x_16194__boxed_1288_ = lean_unbox(v___x_1279_);
v_res_1289_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2(v___x_1272_, v___x_1273_, v_rel_1274_, v___x_1275_, v_beta_1276_, v___x_16193__boxed_1287_, v_alpha_1278_, v___x_16194__boxed_1288_, v_xs_1280_, v_x_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec_ref(v_x_1281_);
return v_res_1289_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__1));
v___x_1293_ = lean_unsigned_to_nat(10u);
v___x_1294_ = lean_unsigned_to_nat(146u);
v___x_1295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__0));
v___x_1296_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_1297_ = l_mkPanicMessageWithDecl(v___x_1296_, v___x_1295_, v___x_1294_, v___x_1293_, v___x_1292_);
return v___x_1297_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(lean_object* v___f_1298_, uint8_t v___x_1299_, lean_object* v_a_1300_, uint8_t v___x_1301_, lean_object* v_ys_1302_, lean_object* v_altBodyType_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
uint8_t v___x_1309_; 
v___x_1309_ = l_Lean_Expr_isForall(v_altBodyType_1303_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec_ref(v_ys_1302_);
lean_dec_ref(v_a_1300_);
lean_dec_ref(v___f_1298_);
v___x_1310_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___closed__2);
v___x_1311_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__1(v___x_1310_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = l_Lean_Expr_bindingDomain_x21(v_altBodyType_1303_);
v___x_1313_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6));
v___x_1314_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v___x_1312_, v___x_1313_, v___f_1298_, v___x_1299_, v___x_1299_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
lean_inc_ref(v_ys_1302_);
v___x_1316_ = lean_array_push(v_ys_1302_, v_a_1315_);
v___x_1317_ = l_Lean_mkAppN(v_a_1300_, v___x_1316_);
lean_dec_ref(v___x_1316_);
v___x_1318_ = 1;
v___x_1319_ = l_Lean_Meta_mkLambdaFVars(v_ys_1302_, v___x_1317_, v___x_1299_, v___x_1301_, v___x_1299_, v___x_1301_, v___x_1318_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec_ref(v_ys_1302_);
return v___x_1319_;
}
else
{
lean_dec_ref(v_ys_1302_);
lean_dec_ref(v_a_1300_);
return v___x_1314_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1298_ = stack[0].m_obj;
uint8_t v___x_1299_ = stack[1].m_num;
lean_object* v_a_1300_ = stack[2].m_obj;
uint8_t v___x_1301_ = stack[3].m_num;
lean_object* v_ys_1302_ = stack[4].m_obj;
lean_object* v_altBodyType_1303_ = stack[5].m_obj;
lean_object* v___y_1304_ = stack[6].m_obj;
lean_object* v___y_1305_ = stack[7].m_obj;
lean_object* v___y_1306_ = stack[8].m_obj;
lean_object* v___y_1307_ = stack[9].m_obj;
lean_object* v_res_1320_;
v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(v___f_1298_, v___x_1299_, v_a_1300_, v___x_1301_, v_ys_1302_, v_altBodyType_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
stack->m_obj
 = v_res_1320_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed(lean_object* v___f_1321_, lean_object* v___x_1322_, lean_object* v_a_1323_, lean_object* v___x_1324_, lean_object* v_ys_1325_, lean_object* v_altBodyType_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v___x_16320__boxed_1332_; uint8_t v___x_16321__boxed_1333_; lean_object* v_res_1334_; 
v___x_16320__boxed_1332_ = lean_unbox(v___x_1322_);
v___x_16321__boxed_1333_ = lean_unbox(v___x_1324_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1(v___f_1321_, v___x_16320__boxed_1332_, v_a_1323_, v___x_16321__boxed_1333_, v_ys_1325_, v_altBodyType_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec_ref(v_altBodyType_1326_);
return v_res_1334_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(lean_object* v___x_1335_, lean_object* v___x_1336_, lean_object* v_f_1337_, uint8_t v___x_1338_, uint8_t v___x_1339_, lean_object* v_ys_1340_, lean_object* v_x_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; 
v___x_1347_ = lean_array_get_borrowed(v___x_1335_, v_ys_1340_, v___x_1336_);
lean_inc(v___x_1347_);
v___x_1348_ = l_Lean_Expr_app___override(v_f_1337_, v___x_1347_);
v___x_1349_ = 1;
v___x_1350_ = l_Lean_Meta_mkLambdaFVars(v_ys_1340_, v___x_1348_, v___x_1338_, v___x_1339_, v___x_1338_, v___x_1339_, v___x_1349_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
return v___x_1350_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1335_ = stack[0].m_obj;
lean_object* v___x_1336_ = stack[1].m_obj;
lean_object* v_f_1337_ = stack[2].m_obj;
uint8_t v___x_1338_ = stack[3].m_num;
uint8_t v___x_1339_ = stack[4].m_num;
lean_object* v_ys_1340_ = stack[5].m_obj;
lean_object* v_x_1341_ = stack[6].m_obj;
lean_object* v___y_1342_ = stack[7].m_obj;
lean_object* v___y_1343_ = stack[8].m_obj;
lean_object* v___y_1344_ = stack[9].m_obj;
lean_object* v___y_1345_ = stack[10].m_obj;
lean_object* v_res_1351_;
v_res_1351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(v___x_1335_, v___x_1336_, v_f_1337_, v___x_1338_, v___x_1339_, v_ys_1340_, v_x_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
stack->m_obj
 = v_res_1351_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed(lean_object* v___x_1352_, lean_object* v___x_1353_, lean_object* v_f_1354_, lean_object* v___x_1355_, lean_object* v___x_1356_, lean_object* v_ys_1357_, lean_object* v_x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v___x_16411__boxed_1364_; uint8_t v___x_16412__boxed_1365_; lean_object* v_res_1366_; 
v___x_16411__boxed_1364_ = lean_unbox(v___x_1355_);
v___x_16412__boxed_1365_ = lean_unbox(v___x_1356_);
v_res_1366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0(v___x_1352_, v___x_1353_, v_f_1354_, v___x_16411__boxed_1364_, v___x_16412__boxed_1365_, v_ys_1357_, v_x_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v_x_1358_);
lean_dec_ref(v_ys_1357_);
lean_dec(v___x_1353_);
lean_dec_ref(v___x_1352_);
return v_res_1366_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(lean_object* v_f_1367_, lean_object* v_as_1368_, size_t v_sz_1369_, size_t v_i_1370_, lean_object* v_b_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_usize_dec_lt(v_i_1370_, v_sz_1369_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
lean_dec_ref(v_f_1367_);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v_b_1371_);
return v___x_1378_;
}
else
{
lean_object* v_snd_1379_; lean_object* v_fst_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1443_; 
v_snd_1379_ = lean_ctor_get(v_b_1371_, 1);
v_fst_1380_ = lean_ctor_get(v_b_1371_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_b_1371_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1382_ = v_b_1371_;
v_isShared_1383_ = v_isSharedCheck_1443_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_snd_1379_);
lean_inc(v_fst_1380_);
lean_dec(v_b_1371_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1443_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_array_1384_; lean_object* v_start_1385_; lean_object* v_stop_1386_; uint8_t v___x_1387_; 
v_array_1384_ = lean_ctor_get(v_snd_1379_, 0);
v_start_1385_ = lean_ctor_get(v_snd_1379_, 1);
v_stop_1386_ = lean_ctor_get(v_snd_1379_, 2);
v___x_1387_ = lean_nat_dec_lt(v_start_1385_, v_stop_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1389_; 
lean_dec_ref(v_f_1367_);
if (v_isShared_1383_ == 0)
{
v___x_1389_ = v___x_1382_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_fst_1380_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_snd_1379_);
v___x_1389_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
else
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1439_; 
lean_inc(v_stop_1386_);
lean_inc(v_start_1385_);
lean_inc_ref(v_array_1384_);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_snd_1379_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; lean_object* v_unused_1441_; lean_object* v_unused_1442_; 
v_unused_1440_ = lean_ctor_get(v_snd_1379_, 2);
lean_dec(v_unused_1440_);
v_unused_1441_ = lean_ctor_get(v_snd_1379_, 1);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_snd_1379_, 0);
lean_dec(v_unused_1442_);
v___x_1393_ = v_snd_1379_;
v_isShared_1394_ = v_isSharedCheck_1439_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v_snd_1379_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1439_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; lean_object* v_a_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___f_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1395_ = l_Lean_instInhabitedExpr;
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = 0;
v_a_1398_ = lean_array_uget_borrowed(v_as_1368_, v_i_1370_);
v___x_1399_ = lean_box(v___x_1397_);
v___x_1400_ = lean_box(v___x_1387_);
lean_inc_ref(v_f_1367_);
v___f_1401_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1401_, 0, v___x_1395_);
lean_closure_set(v___f_1401_, 1, v___x_1396_);
lean_closure_set(v___f_1401_, 2, v_f_1367_);
lean_closure_set(v___f_1401_, 3, v___x_1399_);
lean_closure_set(v___f_1401_, 4, v___x_1400_);
v___x_1402_ = lean_box(v___x_1397_);
v___x_1403_ = lean_box(v___x_1387_);
lean_inc(v_a_1398_);
v___f_1404_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1404_, 0, v___f_1401_);
lean_closure_set(v___f_1404_, 1, v___x_1402_);
lean_closure_set(v___f_1404_, 2, v_a_1398_);
lean_closure_set(v___f_1404_, 3, v___x_1403_);
v___x_1405_ = lean_array_fget(v_array_1384_, v_start_1385_);
v___x_1406_ = lean_unsigned_to_nat(1u);
v___x_1407_ = lean_nat_add(v_start_1385_, v___x_1406_);
lean_dec(v_start_1385_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v___x_1407_);
v___x_1409_ = v___x_1393_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_array_1384_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_stop_1386_);
v___x_1409_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; 
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
lean_inc(v_a_1398_);
v___x_1410_ = lean_infer_type(v_a_1398_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1405_);
v___x_1413_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1411_, v___x_1412_, v___f_1404_, v___x_1397_, v___x_1397_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = l_Lean_Expr_app___override(v_fst_1380_, v_a_1414_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v___x_1409_);
lean_ctor_set(v___x_1382_, 0, v___x_1415_);
v___x_1417_ = v___x_1382_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1409_);
v___x_1417_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
size_t v___x_1418_; size_t v___x_1419_; 
v___x_1418_ = ((size_t)1ULL);
v___x_1419_ = lean_usize_add(v_i_1370_, v___x_1418_);
v_i_1370_ = v___x_1419_;
v_b_1371_ = v___x_1417_;
goto _start;
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec_ref(v___x_1409_);
lean_del_object(v___x_1382_);
lean_dec(v_fst_1380_);
lean_dec_ref(v_f_1367_);
v_a_1422_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1413_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1413_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v___x_1409_);
lean_dec(v___x_1405_);
lean_dec_ref(v___f_1404_);
lean_del_object(v___x_1382_);
lean_dec(v_fst_1380_);
lean_dec_ref(v_f_1367_);
v_a_1430_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1410_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1410_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1367_ = stack[0].m_obj;
lean_object* v_as_1368_ = stack[1].m_obj;
size_t v_sz_1369_ = stack[2].m_num;
size_t v_i_1370_ = stack[3].m_num;
lean_object* v_b_1371_ = stack[4].m_obj;
lean_object* v___y_1372_ = stack[5].m_obj;
lean_object* v___y_1373_ = stack[6].m_obj;
lean_object* v___y_1374_ = stack[7].m_obj;
lean_object* v___y_1375_ = stack[8].m_obj;
lean_object* v_res_1444_;
v_res_1444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1367_, v_as_1368_, v_sz_1369_, v_i_1370_, v_b_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
stack->m_obj
 = v_res_1444_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4___boxed(lean_object* v_f_1445_, lean_object* v_as_1446_, lean_object* v_sz_1447_, lean_object* v_i_1448_, lean_object* v_b_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
size_t v_sz_boxed_1455_; size_t v_i_boxed_1456_; lean_object* v_res_1457_; 
v_sz_boxed_1455_ = lean_unbox_usize(v_sz_1447_);
lean_dec(v_sz_1447_);
v_i_boxed_1456_ = lean_unbox_usize(v_i_1448_);
lean_dec(v_i_1448_);
v_res_1457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1445_, v_as_1446_, v_sz_boxed_1455_, v_i_boxed_1456_, v_b_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec_ref(v_as_1446_);
return v_res_1457_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(lean_object* v_as_x27_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
if (lean_obj_tag(v_as_x27_1458_) == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_b_1459_);
return v___x_1465_;
}
else
{
lean_object* v_head_1466_; lean_object* v_tail_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; 
v_head_1466_ = lean_ctor_get(v_as_x27_1458_, 0);
v_tail_1467_ = lean_ctor_get(v_as_x27_1458_, 1);
v___x_1468_ = lean_box(0);
v___x_1469_ = 1;
lean_inc(v_head_1466_);
v___x_1470_ = l_Lean_MVarId_refl(v_head_1466_, v___x_1469_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_dec_ref_known(v___x_1470_, 1);
v_as_x27_1458_ = v_tail_1467_;
v_b_1459_ = v___x_1468_;
goto _start;
}
else
{
return v___x_1470_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1458_ = stack[0].m_obj;
lean_object* v_b_1459_ = stack[1].m_obj;
lean_object* v___y_1460_ = stack[2].m_obj;
lean_object* v___y_1461_ = stack[3].m_obj;
lean_object* v___y_1462_ = stack[4].m_obj;
lean_object* v___y_1463_ = stack[5].m_obj;
lean_object* v_res_1472_;
v_res_1472_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_1458_, v_b_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
stack->m_obj
 = v_res_1472_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg___boxed(lean_object* v_as_x27_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_1473_, v_b_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v_as_x27_1473_);
return v_res_1480_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(lean_object* v___x_1481_, lean_object* v_matcherInfo_1482_, lean_object* v___x_1483_, lean_object* v___x_1484_, lean_object* v_f_1485_, lean_object* v_discrs_1486_, lean_object* v___x_1487_, lean_object* v_rel_1488_, lean_object* v___x_1489_, uint8_t v___x_1490_, lean_object* v_alpha_1491_, lean_object* v___x_1492_, lean_object* v_beta_1493_, lean_object* v___x_1494_, uint8_t v___x_1495_, lean_object* v___x_1496_, lean_object* v___x_1497_, lean_object* v___x_1498_, lean_object* v_alts_1499_, lean_object* v_x_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; size_t v_sz_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1506_ = l_Lean_mkAppN(v___x_1481_, v_alts_1499_);
lean_inc_ref(v_matcherInfo_1482_);
v___x_1507_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_matcherInfo_1482_);
v___x_1508_ = lean_array_get_size(v___x_1507_);
v___x_1509_ = l_Array_toSubarray___redArg(v___x_1507_, v___x_1483_, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1484_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v_sz_1511_ = lean_array_size(v_alts_1499_);
v___x_1512_ = ((size_t)0ULL);
lean_inc_ref(v_f_1485_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__4(v_f_1485_, v_alts_1499_, v_sz_1511_, v___x_1512_, v___x_1510_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v_fst_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1609_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v_fst_1515_ = lean_ctor_get(v_a_1514_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_a_1514_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v_a_1514_, 1);
lean_dec(v_unused_1610_);
v___x_1517_ = v_a_1514_;
v_isShared_1518_ = v_isSharedCheck_1609_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_fst_1515_);
lean_dec(v_a_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1609_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1519_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__1));
v___x_1520_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___closed__3));
lean_inc_ref(v_discrs_1486_);
v___x_1521_ = lean_array_push(v_discrs_1486_, v___x_1487_);
lean_inc_ref(v_rel_1488_);
v___x_1522_ = l_Lean_mkAppN(v_rel_1488_, v___x_1521_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = l_Lean_Expr_bvar___override(v___x_1489_);
lean_inc_ref(v_f_1485_);
v___x_1524_ = l_Lean_Expr_app___override(v_f_1485_, v___x_1523_);
v___x_1525_ = l_Lean_Expr_lam___override(v___x_1520_, v___x_1522_, v___x_1524_, v___x_1490_);
lean_inc_ref(v_alpha_1491_);
v___x_1526_ = l_Lean_Expr_lam___override(v___x_1519_, v_alpha_1491_, v___x_1525_, v___x_1490_);
v___x_1527_ = l_Lean_Expr_app___override(v___x_1506_, v___x_1526_);
lean_inc(v_fst_1515_);
v___x_1528_ = l_Lean_Meta_mkEq(v___x_1527_, v_fst_1515_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc_n(v_a_1529_, 2);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1530_ = lean_box(0);
v___x_1531_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1529_, v___x_1530_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1533_ = l_Lean_Expr_mvarId_x21(v_a_1532_);
v___x_1534_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_splitMatchOrCasesOn(v___x_1533_, v_fst_1515_, v_matcherInfo_1482_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec_ref(v_matcherInfo_1482_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v___x_1536_ = lean_box(0);
v___x_1537_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_a_1535_, v___x_1536_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v_a_1535_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v___x_1538_; lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref_known(v___x_1537_, 1);
v___x_1538_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_1532_, v___y_1502_);
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1584_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1584_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; 
v___x_1543_ = lean_unsigned_to_nat(5u);
v___x_1544_ = lean_mk_empty_array_with_capacity(v___x_1543_);
v___x_1545_ = lean_array_push(v___x_1544_, v___x_1492_);
v___x_1546_ = lean_array_push(v___x_1545_, v_alpha_1491_);
v___x_1547_ = lean_array_push(v___x_1546_, v_beta_1493_);
v___x_1548_ = lean_array_push(v___x_1547_, v_f_1485_);
v___x_1549_ = lean_array_push(v___x_1548_, v_rel_1488_);
v___x_1550_ = l_Array_append___redArg(v___x_1494_, v___x_1549_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l_Array_append___redArg(v___x_1550_, v_discrs_1486_);
lean_dec_ref(v_discrs_1486_);
v___x_1552_ = l_Array_append___redArg(v___x_1551_, v_alts_1499_);
v___x_1553_ = 1;
v___x_1554_ = 1;
v___x_1555_ = l_Lean_Meta_mkForallFVars(v___x_1552_, v_a_1529_, v___x_1495_, v___x_1553_, v___x_1553_, v___x_1554_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1557_ = l_Lean_Meta_mkLambdaFVars(v___x_1552_, v_a_1539_, v___x_1495_, v___x_1553_, v___x_1495_, v___x_1553_, v___x_1554_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec_ref(v___x_1552_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
lean_inc(v___x_1496_);
v___x_1559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1496_);
lean_ctor_set(v___x_1559_, 1, v___x_1497_);
lean_ctor_set(v___x_1559_, 2, v_a_1556_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set_tag(v___x_1517_, 1);
lean_ctor_set(v___x_1517_, 1, v___x_1498_);
lean_ctor_set(v___x_1517_, 0, v___x_1496_);
v___x_1561_ = v___x_1517_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___x_1498_);
v___x_1561_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1559_);
lean_ctor_set(v___x_1562_, 1, v_a_1558_);
lean_ctor_set(v___x_1562_, 2, v___x_1561_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set_tag(v___x_1541_, 2);
lean_ctor_set(v___x_1541_, 0, v___x_1562_);
v___x_1564_ = v___x_1541_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_addDecl(v___x_1564_, v___x_1495_, v___y_1503_, v___y_1504_);
return v___x_1565_;
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v_a_1556_);
lean_del_object(v___x_1541_);
lean_del_object(v___x_1517_);
lean_dec(v___x_1498_);
lean_dec(v___x_1497_);
lean_dec(v___x_1496_);
v_a_1568_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1557_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1557_);
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
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref(v___x_1552_);
lean_del_object(v___x_1541_);
lean_dec(v_a_1539_);
lean_del_object(v___x_1517_);
lean_dec(v___x_1498_);
lean_dec(v___x_1497_);
lean_dec(v___x_1496_);
v_a_1576_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1555_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1555_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
else
{
lean_dec(v_a_1532_);
lean_dec(v_a_1529_);
lean_del_object(v___x_1517_);
lean_dec(v___x_1498_);
lean_dec(v___x_1497_);
lean_dec(v___x_1496_);
lean_dec_ref(v___x_1494_);
lean_dec_ref(v_beta_1493_);
lean_dec_ref(v___x_1492_);
lean_dec_ref(v_alpha_1491_);
lean_dec_ref(v_rel_1488_);
lean_dec_ref(v_discrs_1486_);
lean_dec_ref(v_f_1485_);
return v___x_1537_;
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v_a_1532_);
lean_dec(v_a_1529_);
lean_del_object(v___x_1517_);
lean_dec(v___x_1498_);
lean_dec(v___x_1497_);
lean_dec(v___x_1496_);
lean_dec_ref(v___x_1494_);
lean_dec_ref(v_beta_1493_);
lean_dec_ref(v___x_1492_);
lean_dec_ref(v_alpha_1491_);
lean_dec_ref(v_rel_1488_);
lean_dec_ref(v_discrs_1486_);
lean_dec_ref(v_f_1485_);
v_a_1585_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1534_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1534_);
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
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_a_1529_);
lean_del_object(v___x_1517_);
lean_dec(v_fst_1515_);
lean_dec(v___x_1498_);
lean_dec(v___x_1497_);
lean_dec(v___x_1496_);
lean_dec_ref(v___x_1494_);
lean_dec_ref(v_beta_1493_);
lean_dec_ref(v___x_1492_);
lean_dec_ref(v_alpha_1491_);
lean_dec_ref(v_rel_1488_);
lean_dec_ref(v_discrs_1486_);
lean_dec_ref(v_f_1485_);
lean_dec_ref(v_matcherInfo_1482_);
v_a_1593_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1531_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1531_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_del_object(v___x_1517_);
lean_dec(v_fst_1515_);
lean_dec(v___x_1498_);
lean_dec(v___x_1497_);
lean_dec(v___x_1496_);
lean_dec_ref(v___x_1494_);
lean_dec_ref(v_beta_1493_);
lean_dec_ref(v___x_1492_);
lean_dec_ref(v_alpha_1491_);
lean_dec_ref(v_rel_1488_);
lean_dec_ref(v_discrs_1486_);
lean_dec_ref(v_f_1485_);
lean_dec_ref(v_matcherInfo_1482_);
v_a_1601_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1528_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1528_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
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
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v___x_1506_);
lean_dec(v___x_1498_);
lean_dec(v___x_1497_);
lean_dec(v___x_1496_);
lean_dec_ref(v___x_1494_);
lean_dec_ref(v_beta_1493_);
lean_dec_ref(v___x_1492_);
lean_dec_ref(v_alpha_1491_);
lean_dec(v___x_1489_);
lean_dec_ref(v_rel_1488_);
lean_dec_ref(v___x_1487_);
lean_dec_ref(v_discrs_1486_);
lean_dec_ref(v_f_1485_);
lean_dec_ref(v_matcherInfo_1482_);
v_a_1611_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1513_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1513_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1481_ = stack[0].m_obj;
lean_object* v_matcherInfo_1482_ = stack[1].m_obj;
lean_object* v___x_1483_ = stack[2].m_obj;
lean_object* v___x_1484_ = stack[3].m_obj;
lean_object* v_f_1485_ = stack[4].m_obj;
lean_object* v_discrs_1486_ = stack[5].m_obj;
lean_object* v___x_1487_ = stack[6].m_obj;
lean_object* v_rel_1488_ = stack[7].m_obj;
lean_object* v___x_1489_ = stack[8].m_obj;
uint8_t v___x_1490_ = stack[9].m_num;
lean_object* v_alpha_1491_ = stack[10].m_obj;
lean_object* v___x_1492_ = stack[11].m_obj;
lean_object* v_beta_1493_ = stack[12].m_obj;
lean_object* v___x_1494_ = stack[13].m_obj;
uint8_t v___x_1495_ = stack[14].m_num;
lean_object* v___x_1496_ = stack[15].m_obj;
lean_object* v___x_1497_ = stack[16].m_obj;
lean_object* v___x_1498_ = stack[17].m_obj;
lean_object* v_alts_1499_ = stack[18].m_obj;
lean_object* v_x_1500_ = stack[19].m_obj;
lean_object* v___y_1501_ = stack[20].m_obj;
lean_object* v___y_1502_ = stack[21].m_obj;
lean_object* v___y_1503_ = stack[22].m_obj;
lean_object* v___y_1504_ = stack[23].m_obj;
lean_object* v_res_1619_;
v_res_1619_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(v___x_1481_, v_matcherInfo_1482_, v___x_1483_, v___x_1484_, v_f_1485_, v_discrs_1486_, v___x_1487_, v_rel_1488_, v___x_1489_, v___x_1490_, v_alpha_1491_, v___x_1492_, v_beta_1493_, v___x_1494_, v___x_1495_, v___x_1496_, v___x_1497_, v___x_1498_, v_alts_1499_, v_x_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
stack->m_obj
 = v_res_1619_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed(lean_object** _args){
lean_object* v___x_1620_ = _args[0];
lean_object* v_matcherInfo_1621_ = _args[1];
lean_object* v___x_1622_ = _args[2];
lean_object* v___x_1623_ = _args[3];
lean_object* v_f_1624_ = _args[4];
lean_object* v_discrs_1625_ = _args[5];
lean_object* v___x_1626_ = _args[6];
lean_object* v_rel_1627_ = _args[7];
lean_object* v___x_1628_ = _args[8];
lean_object* v___x_1629_ = _args[9];
lean_object* v_alpha_1630_ = _args[10];
lean_object* v___x_1631_ = _args[11];
lean_object* v_beta_1632_ = _args[12];
lean_object* v___x_1633_ = _args[13];
lean_object* v___x_1634_ = _args[14];
lean_object* v___x_1635_ = _args[15];
lean_object* v___x_1636_ = _args[16];
lean_object* v___x_1637_ = _args[17];
lean_object* v_alts_1638_ = _args[18];
lean_object* v_x_1639_ = _args[19];
lean_object* v___y_1640_ = _args[20];
lean_object* v___y_1641_ = _args[21];
lean_object* v___y_1642_ = _args[22];
lean_object* v___y_1643_ = _args[23];
lean_object* v___y_1644_ = _args[24];
_start:
{
uint8_t v___x_16738__boxed_1645_; uint8_t v___x_16741__boxed_1646_; lean_object* v_res_1647_; 
v___x_16738__boxed_1645_ = lean_unbox(v___x_1629_);
v___x_16741__boxed_1646_ = lean_unbox(v___x_1634_);
v_res_1647_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3(v___x_1620_, v_matcherInfo_1621_, v___x_1622_, v___x_1623_, v_f_1624_, v_discrs_1625_, v___x_1626_, v_rel_1627_, v___x_1628_, v___x_16738__boxed_1645_, v_alpha_1630_, v___x_1631_, v_beta_1632_, v___x_1633_, v___x_16741__boxed_1646_, v___x_1635_, v___x_1636_, v___x_1637_, v_alts_1638_, v_x_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v_x_1639_);
lean_dec_ref(v_alts_1638_);
return v_res_1647_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(lean_object* v___x_1648_, lean_object* v___x_1649_, lean_object* v_matcherInfo_1650_, lean_object* v___x_1651_, lean_object* v_f_1652_, lean_object* v___x_1653_, lean_object* v_rel_1654_, lean_object* v___x_1655_, uint8_t v___x_1656_, lean_object* v_alpha_1657_, lean_object* v___x_1658_, lean_object* v_beta_1659_, lean_object* v___x_1660_, uint8_t v___x_1661_, lean_object* v___x_1662_, lean_object* v___x_1663_, lean_object* v___x_1664_, lean_object* v_discrs_1665_, lean_object* v_x_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___f_1676_; lean_object* v___x_1677_; 
v___x_1672_ = l_Lean_mkAppN(v___x_1648_, v_discrs_1665_);
v___x_1673_ = l_Lean_mkAppN(v___x_1649_, v_discrs_1665_);
v___x_1674_ = lean_box(v___x_1656_);
v___x_1675_ = lean_box(v___x_1661_);
lean_inc_ref(v_matcherInfo_1650_);
lean_inc_ref(v___x_1672_);
v___f_1676_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1676_, 0, v___x_1672_);
lean_closure_set(v___f_1676_, 1, v_matcherInfo_1650_);
lean_closure_set(v___f_1676_, 2, v___x_1651_);
lean_closure_set(v___f_1676_, 3, v___x_1673_);
lean_closure_set(v___f_1676_, 4, v_f_1652_);
lean_closure_set(v___f_1676_, 5, v_discrs_1665_);
lean_closure_set(v___f_1676_, 6, v___x_1653_);
lean_closure_set(v___f_1676_, 7, v_rel_1654_);
lean_closure_set(v___f_1676_, 8, v___x_1655_);
lean_closure_set(v___f_1676_, 9, v___x_1674_);
lean_closure_set(v___f_1676_, 10, v_alpha_1657_);
lean_closure_set(v___f_1676_, 11, v___x_1658_);
lean_closure_set(v___f_1676_, 12, v_beta_1659_);
lean_closure_set(v___f_1676_, 13, v___x_1660_);
lean_closure_set(v___f_1676_, 14, v___x_1675_);
lean_closure_set(v___f_1676_, 15, v___x_1662_);
lean_closure_set(v___f_1676_, 16, v___x_1663_);
lean_closure_set(v___f_1676_, 17, v___x_1664_);
lean_inc(v___y_1670_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
v___x_1677_ = lean_infer_type(v___x_1672_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1677_, 1);
v___x_1679_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_matcherInfo_1650_);
lean_dec_ref(v_matcherInfo_1650_);
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
v___x_1681_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1678_, v___x_1680_, v___f_1676_, v___x_1661_, v___x_1661_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1681_;
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref(v___f_1676_);
lean_dec_ref(v_matcherInfo_1650_);
v_a_1682_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1677_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1677_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1648_ = stack[0].m_obj;
lean_object* v___x_1649_ = stack[1].m_obj;
lean_object* v_matcherInfo_1650_ = stack[2].m_obj;
lean_object* v___x_1651_ = stack[3].m_obj;
lean_object* v_f_1652_ = stack[4].m_obj;
lean_object* v___x_1653_ = stack[5].m_obj;
lean_object* v_rel_1654_ = stack[6].m_obj;
lean_object* v___x_1655_ = stack[7].m_obj;
uint8_t v___x_1656_ = stack[8].m_num;
lean_object* v_alpha_1657_ = stack[9].m_obj;
lean_object* v___x_1658_ = stack[10].m_obj;
lean_object* v_beta_1659_ = stack[11].m_obj;
lean_object* v___x_1660_ = stack[12].m_obj;
uint8_t v___x_1661_ = stack[13].m_num;
lean_object* v___x_1662_ = stack[14].m_obj;
lean_object* v___x_1663_ = stack[15].m_obj;
lean_object* v___x_1664_ = stack[16].m_obj;
lean_object* v_discrs_1665_ = stack[17].m_obj;
lean_object* v_x_1666_ = stack[18].m_obj;
lean_object* v___y_1667_ = stack[19].m_obj;
lean_object* v___y_1668_ = stack[20].m_obj;
lean_object* v___y_1669_ = stack[21].m_obj;
lean_object* v___y_1670_ = stack[22].m_obj;
lean_object* v_res_1690_;
v_res_1690_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(v___x_1648_, v___x_1649_, v_matcherInfo_1650_, v___x_1651_, v_f_1652_, v___x_1653_, v_rel_1654_, v___x_1655_, v___x_1656_, v_alpha_1657_, v___x_1658_, v_beta_1659_, v___x_1660_, v___x_1661_, v___x_1662_, v___x_1663_, v___x_1664_, v_discrs_1665_, v_x_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
stack->m_obj
 = v_res_1690_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed(lean_object** _args){
lean_object* v___x_1691_ = _args[0];
lean_object* v___x_1692_ = _args[1];
lean_object* v_matcherInfo_1693_ = _args[2];
lean_object* v___x_1694_ = _args[3];
lean_object* v_f_1695_ = _args[4];
lean_object* v___x_1696_ = _args[5];
lean_object* v_rel_1697_ = _args[6];
lean_object* v___x_1698_ = _args[7];
lean_object* v___x_1699_ = _args[8];
lean_object* v_alpha_1700_ = _args[9];
lean_object* v___x_1701_ = _args[10];
lean_object* v_beta_1702_ = _args[11];
lean_object* v___x_1703_ = _args[12];
lean_object* v___x_1704_ = _args[13];
lean_object* v___x_1705_ = _args[14];
lean_object* v___x_1706_ = _args[15];
lean_object* v___x_1707_ = _args[16];
lean_object* v_discrs_1708_ = _args[17];
lean_object* v_x_1709_ = _args[18];
lean_object* v___y_1710_ = _args[19];
lean_object* v___y_1711_ = _args[20];
lean_object* v___y_1712_ = _args[21];
lean_object* v___y_1713_ = _args[22];
lean_object* v___y_1714_ = _args[23];
_start:
{
uint8_t v___x_17166__boxed_1715_; uint8_t v___x_17169__boxed_1716_; lean_object* v_res_1717_; 
v___x_17166__boxed_1715_ = lean_unbox(v___x_1699_);
v___x_17169__boxed_1716_ = lean_unbox(v___x_1704_);
v_res_1717_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4(v___x_1691_, v___x_1692_, v_matcherInfo_1693_, v___x_1694_, v_f_1695_, v___x_1696_, v_rel_1697_, v___x_1698_, v___x_17166__boxed_1715_, v_alpha_1700_, v___x_1701_, v_beta_1702_, v___x_1703_, v___x_17169__boxed_1716_, v___x_1705_, v___x_1706_, v___x_1707_, v_discrs_1708_, v_x_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec_ref(v_x_1709_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
if (lean_obj_tag(v_a_1718_) == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = l_List_reverse___redArg(v_a_1719_);
return v___x_1720_;
}
else
{
lean_object* v_head_1721_; lean_object* v_tail_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1731_; 
v_head_1721_ = lean_ctor_get(v_a_1718_, 0);
v_tail_1722_ = lean_ctor_get(v_a_1718_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_a_1718_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1724_ = v_a_1718_;
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_tail_1722_);
lean_inc(v_head_1721_);
lean_dec(v_a_1718_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_mkLevelParam(v_head_1721_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v_a_1719_);
lean_ctor_set(v___x_1724_, 0, v___x_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_a_1719_);
v___x_1728_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
v_a_1718_ = v_tail_1722_;
v_a_1719_ = v___x_1728_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__0));
v___x_1734_ = l_Lean_stringToMessageData(v___x_1733_);
return v___x_1734_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__2));
v___x_1737_ = l_Lean_stringToMessageData(v___x_1736_);
return v___x_1737_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(lean_object* v___x_1738_, lean_object* v___x_1739_, lean_object* v___x_1740_, lean_object* v_beta_1741_, uint8_t v___x_1742_, lean_object* v_alpha_1743_, uint8_t v___x_1744_, lean_object* v_numDiscrs_1745_, lean_object* v___f_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_levelParams_1749_, lean_object* v_matcherName_1750_, lean_object* v___x_1751_, lean_object* v_matcherInfo_1752_, lean_object* v___x_1753_, lean_object* v_f_1754_, lean_object* v___x_1755_, lean_object* v_uElimPos_x3f_1756_, lean_object* v_rel_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___f_1765_; lean_object* v___x_1766_; 
v___x_1763_ = lean_box(v___x_1742_);
v___x_1764_ = lean_box(v___x_1744_);
lean_inc_ref(v_alpha_1743_);
lean_inc_ref(v_beta_1741_);
lean_inc(v___x_1740_);
lean_inc_ref(v_rel_1757_);
lean_inc_ref(v___x_1739_);
lean_inc_ref_n(v___x_1738_, 2);
v___f_1765_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__2___boxed), 15, 8);
lean_closure_set(v___f_1765_, 0, v___x_1738_);
lean_closure_set(v___f_1765_, 1, v___x_1739_);
lean_closure_set(v___f_1765_, 2, v_rel_1757_);
lean_closure_set(v___f_1765_, 3, v___x_1740_);
lean_closure_set(v___f_1765_, 4, v_beta_1741_);
lean_closure_set(v___f_1765_, 5, v___x_1763_);
lean_closure_set(v___f_1765_, 6, v_alpha_1743_);
lean_closure_set(v___f_1765_, 7, v___x_1764_);
lean_inc(v___y_1761_);
lean_inc_ref(v___y_1760_);
lean_inc(v___y_1759_);
lean_inc_ref(v___y_1758_);
v___x_1766_ = lean_infer_type(v___x_1738_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1767_, v___f_1765_, v___x_1744_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc_n(v_a_1769_, 2);
lean_dec_ref_known(v___x_1768_, 1);
lean_inc(v_numDiscrs_1745_);
v___x_1770_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive_spec__0___redArg(v_a_1769_, v_numDiscrs_1745_, v___f_1746_, v___x_1744_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v_matcherLevels_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = lean_box(0);
v___x_1773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1773_, 0, v_a_1747_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1774_, 0, v_a_1748_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
lean_inc(v_levelParams_1749_);
v___x_1775_ = l_List_appendTR___redArg(v_levelParams_1749_, v___x_1774_);
v___x_1776_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_1749_, v___x_1772_);
if (lean_obj_tag(v_uElimPos_x3f_1756_) == 0)
{
uint8_t v___x_1805_; 
v___x_1805_ = l_Lean_Level_isZero(v_a_1771_);
lean_dec(v_a_1771_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec(v___x_1776_);
lean_dec(v___x_1775_);
lean_dec(v_a_1769_);
lean_dec_ref(v_rel_1757_);
lean_dec(v___x_1755_);
lean_dec_ref(v_f_1754_);
lean_dec(v___x_1753_);
lean_dec_ref(v_matcherInfo_1752_);
lean_dec_ref(v___x_1751_);
lean_dec(v_numDiscrs_1745_);
lean_dec_ref(v_alpha_1743_);
lean_dec_ref(v_beta_1741_);
lean_dec(v___x_1740_);
lean_dec_ref(v___x_1739_);
lean_dec_ref(v___x_1738_);
v___x_1806_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__1);
v___x_1807_ = l_Lean_MessageData_ofConstName(v_matcherName_1750_, v___x_1744_);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___closed__3);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_1810_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
return v___x_1811_;
}
else
{
lean_inc(v___x_1776_);
v_matcherLevels_1778_ = v___x_1776_;
v___y_1779_ = v___y_1758_;
v___y_1780_ = v___y_1759_;
v___y_1781_ = v___y_1760_;
v___y_1782_ = v___y_1761_;
goto v___jp_1777_;
}
}
else
{
lean_object* v_val_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v_val_1812_ = lean_ctor_get(v_uElimPos_x3f_1756_, 0);
lean_inc(v___x_1776_);
v___x_1813_ = lean_array_mk(v___x_1776_);
v___x_1814_ = lean_array_set(v___x_1813_, v_val_1812_, v_a_1771_);
v___x_1815_ = lean_array_to_list(v___x_1814_);
v_matcherLevels_1778_ = v___x_1815_;
v___y_1779_ = v___y_1758_;
v___y_1780_ = v___y_1759_;
v___y_1781_ = v___y_1760_;
v___y_1782_ = v___y_1761_;
goto v___jp_1777_;
}
v___jp_1777_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___f_1792_; lean_object* v___x_1793_; 
lean_inc(v_matcherName_1750_);
v___x_1783_ = l_Lean_Expr_const___override(v_matcherName_1750_, v_matcherLevels_1778_);
v___x_1784_ = l_Lean_Expr_const___override(v_matcherName_1750_, v___x_1776_);
v___x_1785_ = l_Subarray_copy___redArg(v___x_1751_);
v___x_1786_ = l_Lean_mkAppN(v___x_1783_, v___x_1785_);
v___x_1787_ = l_Lean_mkAppN(v___x_1784_, v___x_1785_);
v___x_1788_ = l_Lean_Expr_app___override(v___x_1786_, v_a_1769_);
lean_inc_ref(v___x_1738_);
v___x_1789_ = l_Lean_Expr_app___override(v___x_1787_, v___x_1738_);
v___x_1790_ = lean_box(v___x_1742_);
v___x_1791_ = lean_box(v___x_1744_);
lean_inc_ref(v___x_1788_);
v___f_1792_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__4___boxed), 24, 17);
lean_closure_set(v___f_1792_, 0, v___x_1788_);
lean_closure_set(v___f_1792_, 1, v___x_1789_);
lean_closure_set(v___f_1792_, 2, v_matcherInfo_1752_);
lean_closure_set(v___f_1792_, 3, v___x_1753_);
lean_closure_set(v___f_1792_, 4, v_f_1754_);
lean_closure_set(v___f_1792_, 5, v___x_1739_);
lean_closure_set(v___f_1792_, 6, v_rel_1757_);
lean_closure_set(v___f_1792_, 7, v___x_1740_);
lean_closure_set(v___f_1792_, 8, v___x_1790_);
lean_closure_set(v___f_1792_, 9, v_alpha_1743_);
lean_closure_set(v___f_1792_, 10, v___x_1738_);
lean_closure_set(v___f_1792_, 11, v_beta_1741_);
lean_closure_set(v___f_1792_, 12, v___x_1785_);
lean_closure_set(v___f_1792_, 13, v___x_1791_);
lean_closure_set(v___f_1792_, 14, v___x_1755_);
lean_closure_set(v___f_1792_, 15, v___x_1775_);
lean_closure_set(v___f_1792_, 16, v___x_1772_);
lean_inc(v___y_1782_);
lean_inc_ref(v___y_1781_);
lean_inc(v___y_1780_);
lean_inc_ref(v___y_1779_);
v___x_1793_ = lean_infer_type(v___x_1788_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___x_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1795_, 0, v_numDiscrs_1745_);
v___x_1796_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_a_1794_, v___x_1795_, v___f_1792_, v___x_1744_, v___x_1744_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
return v___x_1796_;
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v___f_1792_);
lean_dec(v_numDiscrs_1745_);
v_a_1797_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1793_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1793_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec(v_a_1769_);
lean_dec_ref(v_rel_1757_);
lean_dec(v___x_1755_);
lean_dec_ref(v_f_1754_);
lean_dec(v___x_1753_);
lean_dec_ref(v_matcherInfo_1752_);
lean_dec_ref(v___x_1751_);
lean_dec(v_matcherName_1750_);
lean_dec(v_levelParams_1749_);
lean_dec(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec(v_numDiscrs_1745_);
lean_dec_ref(v_alpha_1743_);
lean_dec_ref(v_beta_1741_);
lean_dec(v___x_1740_);
lean_dec_ref(v___x_1739_);
lean_dec_ref(v___x_1738_);
v_a_1816_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1770_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1770_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec_ref(v_rel_1757_);
lean_dec(v___x_1755_);
lean_dec_ref(v_f_1754_);
lean_dec(v___x_1753_);
lean_dec_ref(v_matcherInfo_1752_);
lean_dec_ref(v___x_1751_);
lean_dec(v_matcherName_1750_);
lean_dec(v_levelParams_1749_);
lean_dec(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v___f_1746_);
lean_dec(v_numDiscrs_1745_);
lean_dec_ref(v_alpha_1743_);
lean_dec_ref(v_beta_1741_);
lean_dec(v___x_1740_);
lean_dec_ref(v___x_1739_);
lean_dec_ref(v___x_1738_);
v_a_1824_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1768_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1768_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v___f_1765_);
lean_dec_ref(v_rel_1757_);
lean_dec(v___x_1755_);
lean_dec_ref(v_f_1754_);
lean_dec(v___x_1753_);
lean_dec_ref(v_matcherInfo_1752_);
lean_dec_ref(v___x_1751_);
lean_dec(v_matcherName_1750_);
lean_dec(v_levelParams_1749_);
lean_dec(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v___f_1746_);
lean_dec(v_numDiscrs_1745_);
lean_dec_ref(v_alpha_1743_);
lean_dec_ref(v_beta_1741_);
lean_dec(v___x_1740_);
lean_dec_ref(v___x_1739_);
lean_dec_ref(v___x_1738_);
v_a_1832_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1766_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1766_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1738_ = stack[0].m_obj;
lean_object* v___x_1739_ = stack[1].m_obj;
lean_object* v___x_1740_ = stack[2].m_obj;
lean_object* v_beta_1741_ = stack[3].m_obj;
uint8_t v___x_1742_ = stack[4].m_num;
lean_object* v_alpha_1743_ = stack[5].m_obj;
uint8_t v___x_1744_ = stack[6].m_num;
lean_object* v_numDiscrs_1745_ = stack[7].m_obj;
lean_object* v___f_1746_ = stack[8].m_obj;
lean_object* v_a_1747_ = stack[9].m_obj;
lean_object* v_a_1748_ = stack[10].m_obj;
lean_object* v_levelParams_1749_ = stack[11].m_obj;
lean_object* v_matcherName_1750_ = stack[12].m_obj;
lean_object* v___x_1751_ = stack[13].m_obj;
lean_object* v_matcherInfo_1752_ = stack[14].m_obj;
lean_object* v___x_1753_ = stack[15].m_obj;
lean_object* v_f_1754_ = stack[16].m_obj;
lean_object* v___x_1755_ = stack[17].m_obj;
lean_object* v_uElimPos_x3f_1756_ = stack[18].m_obj;
lean_object* v_rel_1757_ = stack[19].m_obj;
lean_object* v___y_1758_ = stack[20].m_obj;
lean_object* v___y_1759_ = stack[21].m_obj;
lean_object* v___y_1760_ = stack[22].m_obj;
lean_object* v___y_1761_ = stack[23].m_obj;
lean_object* v_res_1840_;
v_res_1840_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(v___x_1738_, v___x_1739_, v___x_1740_, v_beta_1741_, v___x_1742_, v_alpha_1743_, v___x_1744_, v_numDiscrs_1745_, v___f_1746_, v_a_1747_, v_a_1748_, v_levelParams_1749_, v_matcherName_1750_, v___x_1751_, v_matcherInfo_1752_, v___x_1753_, v_f_1754_, v___x_1755_, v_uElimPos_x3f_1756_, v_rel_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
stack->m_obj
 = v_res_1840_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed(lean_object** _args){
lean_object* v___x_1841_ = _args[0];
lean_object* v___x_1842_ = _args[1];
lean_object* v___x_1843_ = _args[2];
lean_object* v_beta_1844_ = _args[3];
lean_object* v___x_1845_ = _args[4];
lean_object* v_alpha_1846_ = _args[5];
lean_object* v___x_1847_ = _args[6];
lean_object* v_numDiscrs_1848_ = _args[7];
lean_object* v___f_1849_ = _args[8];
lean_object* v_a_1850_ = _args[9];
lean_object* v_a_1851_ = _args[10];
lean_object* v_levelParams_1852_ = _args[11];
lean_object* v_matcherName_1853_ = _args[12];
lean_object* v___x_1854_ = _args[13];
lean_object* v_matcherInfo_1855_ = _args[14];
lean_object* v___x_1856_ = _args[15];
lean_object* v_f_1857_ = _args[16];
lean_object* v___x_1858_ = _args[17];
lean_object* v_uElimPos_x3f_1859_ = _args[18];
lean_object* v_rel_1860_ = _args[19];
lean_object* v___y_1861_ = _args[20];
lean_object* v___y_1862_ = _args[21];
lean_object* v___y_1863_ = _args[22];
lean_object* v___y_1864_ = _args[23];
lean_object* v___y_1865_ = _args[24];
_start:
{
uint8_t v___x_17362__boxed_1866_; uint8_t v___x_17363__boxed_1867_; lean_object* v_res_1868_; 
v___x_17362__boxed_1866_ = lean_unbox(v___x_1845_);
v___x_17363__boxed_1867_ = lean_unbox(v___x_1847_);
v_res_1868_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5(v___x_1841_, v___x_1842_, v___x_1843_, v_beta_1844_, v___x_17362__boxed_1866_, v_alpha_1846_, v___x_17363__boxed_1867_, v_numDiscrs_1848_, v___f_1849_, v_a_1850_, v_a_1851_, v_levelParams_1852_, v_matcherName_1853_, v___x_1854_, v_matcherInfo_1855_, v___x_1856_, v_f_1857_, v___x_1858_, v_uElimPos_x3f_1859_, v_rel_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v_uElimPos_x3f_1859_);
return v_res_1868_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(lean_object* v_k_1869_, lean_object* v_b_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; 
lean_inc(v___y_1874_);
lean_inc_ref(v___y_1873_);
lean_inc(v___y_1872_);
lean_inc_ref(v___y_1871_);
v___x_1876_ = lean_apply_6(v_k_1869_, v_b_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, lean_box(0));
return v___x_1876_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1869_ = stack[0].m_obj;
lean_object* v_b_1870_ = stack[1].m_obj;
lean_object* v___y_1871_ = stack[2].m_obj;
lean_object* v___y_1872_ = stack[3].m_obj;
lean_object* v___y_1873_ = stack[4].m_obj;
lean_object* v___y_1874_ = stack[5].m_obj;
lean_object* v_res_1877_;
v_res_1877_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(v_k_1869_, v_b_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
stack->m_obj
 = v_res_1877_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v_k_1878_, lean_object* v_b_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0(v_k_1878_, v_b_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1885_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(lean_object* v_name_1886_, uint8_t v_bi_1887_, lean_object* v_type_1888_, lean_object* v_k_1889_, uint8_t v_kind_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___f_1896_; lean_object* v___x_1897_; 
v___f_1896_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1896_, 0, v_k_1889_);
v___x_1897_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1886_, v_bi_1887_, v_type_1888_, v___f_1896_, v_kind_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_a_1906_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1897_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1897_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1886_ = stack[0].m_obj;
uint8_t v_bi_1887_ = stack[1].m_num;
lean_object* v_type_1888_ = stack[2].m_obj;
lean_object* v_k_1889_ = stack[3].m_obj;
uint8_t v_kind_1890_ = stack[4].m_num;
lean_object* v___y_1891_ = stack[5].m_obj;
lean_object* v___y_1892_ = stack[6].m_obj;
lean_object* v___y_1893_ = stack[7].m_obj;
lean_object* v___y_1894_ = stack[8].m_obj;
lean_object* v_res_1914_;
v_res_1914_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1886_, v_bi_1887_, v_type_1888_, v_k_1889_, v_kind_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
stack->m_obj
 = v_res_1914_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg___boxed(lean_object* v_name_1915_, lean_object* v_bi_1916_, lean_object* v_type_1917_, lean_object* v_k_1918_, lean_object* v_kind_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
uint8_t v_bi_boxed_1925_; uint8_t v_kind_boxed_1926_; lean_object* v_res_1927_; 
v_bi_boxed_1925_ = lean_unbox(v_bi_1916_);
v_kind_boxed_1926_ = lean_unbox(v_kind_1919_);
v_res_1927_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1915_, v_bi_boxed_1925_, v_type_1917_, v_k_1918_, v_kind_boxed_1926_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1927_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(lean_object* v_name_1928_, lean_object* v_type_1929_, lean_object* v_k_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
uint8_t v___x_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = 0;
v___x_1937_ = 0;
v___x_1938_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_1928_, v___x_1936_, v_type_1929_, v_k_1930_, v___x_1937_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
return v___x_1938_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1928_ = stack[0].m_obj;
lean_object* v_type_1929_ = stack[1].m_obj;
lean_object* v_k_1930_ = stack[2].m_obj;
lean_object* v___y_1931_ = stack[3].m_obj;
lean_object* v___y_1932_ = stack[4].m_obj;
lean_object* v___y_1933_ = stack[5].m_obj;
lean_object* v___y_1934_ = stack[6].m_obj;
lean_object* v_res_1939_;
v_res_1939_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_1928_, v_type_1929_, v_k_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
stack->m_obj
 = v_res_1939_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg___boxed(lean_object* v_name_1940_, lean_object* v_type_1941_, lean_object* v_k_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_1940_, v_type_1941_, v_k_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1948_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(lean_object* v___x_1952_, lean_object* v___x_1953_, lean_object* v___x_1954_, lean_object* v_beta_1955_, uint8_t v___x_1956_, lean_object* v_alpha_1957_, lean_object* v_numDiscrs_1958_, lean_object* v___f_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_levelParams_1962_, lean_object* v_matcherName_1963_, lean_object* v___x_1964_, lean_object* v_matcherInfo_1965_, lean_object* v___x_1966_, lean_object* v___x_1967_, lean_object* v_uElimPos_x3f_1968_, lean_object* v___f_1969_, lean_object* v_f_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
lean_inc(v___y_1974_);
lean_inc_ref(v___y_1973_);
lean_inc(v___y_1972_);
lean_inc_ref(v___y_1971_);
lean_inc_ref(v___x_1952_);
v___x_1976_ = lean_infer_type(v___x_1952_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___f_1981_; lean_object* v___x_1982_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
v___x_1978_ = 0;
v___x_1979_ = lean_box(v___x_1956_);
v___x_1980_ = lean_box(v___x_1978_);
v___f_1981_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__5___boxed), 25, 19);
lean_closure_set(v___f_1981_, 0, v___x_1952_);
lean_closure_set(v___f_1981_, 1, v___x_1953_);
lean_closure_set(v___f_1981_, 2, v___x_1954_);
lean_closure_set(v___f_1981_, 3, v_beta_1955_);
lean_closure_set(v___f_1981_, 4, v___x_1979_);
lean_closure_set(v___f_1981_, 5, v_alpha_1957_);
lean_closure_set(v___f_1981_, 6, v___x_1980_);
lean_closure_set(v___f_1981_, 7, v_numDiscrs_1958_);
lean_closure_set(v___f_1981_, 8, v___f_1959_);
lean_closure_set(v___f_1981_, 9, v_a_1960_);
lean_closure_set(v___f_1981_, 10, v_a_1961_);
lean_closure_set(v___f_1981_, 11, v_levelParams_1962_);
lean_closure_set(v___f_1981_, 12, v_matcherName_1963_);
lean_closure_set(v___f_1981_, 13, v___x_1964_);
lean_closure_set(v___f_1981_, 14, v_matcherInfo_1965_);
lean_closure_set(v___f_1981_, 15, v___x_1966_);
lean_closure_set(v___f_1981_, 16, v_f_1970_);
lean_closure_set(v___f_1981_, 17, v___x_1967_);
lean_closure_set(v___f_1981_, 18, v_uElimPos_x3f_1968_);
v___x_1982_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__2___redArg(v_a_1977_, v___f_1969_, v___x_1978_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1982_, 1);
v___x_1984_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___closed__1));
v___x_1985_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_1984_, v_a_1983_, v___f_1981_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_1985_;
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref(v___f_1981_);
v_a_1986_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1982_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1982_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_f_1970_);
lean_dec_ref(v___f_1969_);
lean_dec(v_uElimPos_x3f_1968_);
lean_dec(v___x_1967_);
lean_dec(v___x_1966_);
lean_dec_ref(v_matcherInfo_1965_);
lean_dec_ref(v___x_1964_);
lean_dec(v_matcherName_1963_);
lean_dec(v_levelParams_1962_);
lean_dec(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v___f_1959_);
lean_dec(v_numDiscrs_1958_);
lean_dec_ref(v_alpha_1957_);
lean_dec_ref(v_beta_1955_);
lean_dec(v___x_1954_);
lean_dec_ref(v___x_1953_);
lean_dec_ref(v___x_1952_);
v_a_1994_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1976_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1976_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1952_ = stack[0].m_obj;
lean_object* v___x_1953_ = stack[1].m_obj;
lean_object* v___x_1954_ = stack[2].m_obj;
lean_object* v_beta_1955_ = stack[3].m_obj;
uint8_t v___x_1956_ = stack[4].m_num;
lean_object* v_alpha_1957_ = stack[5].m_obj;
lean_object* v_numDiscrs_1958_ = stack[6].m_obj;
lean_object* v___f_1959_ = stack[7].m_obj;
lean_object* v_a_1960_ = stack[8].m_obj;
lean_object* v_a_1961_ = stack[9].m_obj;
lean_object* v_levelParams_1962_ = stack[10].m_obj;
lean_object* v_matcherName_1963_ = stack[11].m_obj;
lean_object* v___x_1964_ = stack[12].m_obj;
lean_object* v_matcherInfo_1965_ = stack[13].m_obj;
lean_object* v___x_1966_ = stack[14].m_obj;
lean_object* v___x_1967_ = stack[15].m_obj;
lean_object* v_uElimPos_x3f_1968_ = stack[16].m_obj;
lean_object* v___f_1969_ = stack[17].m_obj;
lean_object* v_f_1970_ = stack[18].m_obj;
lean_object* v___y_1971_ = stack[19].m_obj;
lean_object* v___y_1972_ = stack[20].m_obj;
lean_object* v___y_1973_ = stack[21].m_obj;
lean_object* v___y_1974_ = stack[22].m_obj;
lean_object* v_res_2002_;
v_res_2002_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(v___x_1952_, v___x_1953_, v___x_1954_, v_beta_1955_, v___x_1956_, v_alpha_1957_, v_numDiscrs_1958_, v___f_1959_, v_a_1960_, v_a_1961_, v_levelParams_1962_, v_matcherName_1963_, v___x_1964_, v_matcherInfo_1965_, v___x_1966_, v___x_1967_, v_uElimPos_x3f_1968_, v___f_1969_, v_f_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
stack->m_obj
 = v_res_2002_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed(lean_object** _args){
lean_object* v___x_2003_ = _args[0];
lean_object* v___x_2004_ = _args[1];
lean_object* v___x_2005_ = _args[2];
lean_object* v_beta_2006_ = _args[3];
lean_object* v___x_2007_ = _args[4];
lean_object* v_alpha_2008_ = _args[5];
lean_object* v_numDiscrs_2009_ = _args[6];
lean_object* v___f_2010_ = _args[7];
lean_object* v_a_2011_ = _args[8];
lean_object* v_a_2012_ = _args[9];
lean_object* v_levelParams_2013_ = _args[10];
lean_object* v_matcherName_2014_ = _args[11];
lean_object* v___x_2015_ = _args[12];
lean_object* v_matcherInfo_2016_ = _args[13];
lean_object* v___x_2017_ = _args[14];
lean_object* v___x_2018_ = _args[15];
lean_object* v_uElimPos_x3f_2019_ = _args[16];
lean_object* v___f_2020_ = _args[17];
lean_object* v_f_2021_ = _args[18];
lean_object* v___y_2022_ = _args[19];
lean_object* v___y_2023_ = _args[20];
lean_object* v___y_2024_ = _args[21];
lean_object* v___y_2025_ = _args[22];
lean_object* v___y_2026_ = _args[23];
_start:
{
uint8_t v___x_17831__boxed_2027_; lean_object* v_res_2028_; 
v___x_17831__boxed_2027_ = lean_unbox(v___x_2007_);
v_res_2028_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6(v___x_2003_, v___x_2004_, v___x_2005_, v_beta_2006_, v___x_17831__boxed_2027_, v_alpha_2008_, v_numDiscrs_2009_, v___f_2010_, v_a_2011_, v_a_2012_, v_levelParams_2013_, v_matcherName_2014_, v___x_2015_, v_matcherInfo_2016_, v___x_2017_, v___x_2018_, v_uElimPos_x3f_2019_, v___f_2020_, v_f_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
return v_res_2028_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(lean_object* v___x_2035_, lean_object* v_alpha_2036_, lean_object* v___x_2037_, lean_object* v___x_2038_, lean_object* v_numDiscrs_2039_, lean_object* v___f_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_levelParams_2043_, lean_object* v_matcherName_2044_, lean_object* v___x_2045_, lean_object* v_matcherInfo_2046_, lean_object* v___x_2047_, lean_object* v_uElimPos_x3f_2048_, lean_object* v_beta_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___f_2061_; lean_object* v___x_2062_; lean_object* v___f_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2055_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__1));
v___x_2056_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___closed__3));
lean_inc_n(v___x_2035_, 2);
v___x_2057_ = l_Lean_Expr_bvar___override(v___x_2035_);
lean_inc_ref(v___x_2057_);
lean_inc_ref(v_beta_2049_);
v___x_2058_ = l_Lean_Expr_app___override(v_beta_2049_, v___x_2057_);
v___x_2059_ = 0;
v___x_2060_ = lean_box(v___x_2059_);
lean_inc_ref_n(v_alpha_2036_, 2);
v___f_2061_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2061_, 0, v___x_2035_);
lean_closure_set(v___f_2061_, 1, v___x_2056_);
lean_closure_set(v___f_2061_, 2, v_alpha_2036_);
lean_closure_set(v___f_2061_, 3, v___x_2060_);
v___x_2062_ = lean_box(v___x_2059_);
v___f_2063_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__6___boxed), 24, 18);
lean_closure_set(v___f_2063_, 0, v___x_2037_);
lean_closure_set(v___f_2063_, 1, v___x_2057_);
lean_closure_set(v___f_2063_, 2, v___x_2038_);
lean_closure_set(v___f_2063_, 3, v_beta_2049_);
lean_closure_set(v___f_2063_, 4, v___x_2062_);
lean_closure_set(v___f_2063_, 5, v_alpha_2036_);
lean_closure_set(v___f_2063_, 6, v_numDiscrs_2039_);
lean_closure_set(v___f_2063_, 7, v___f_2040_);
lean_closure_set(v___f_2063_, 8, v_a_2041_);
lean_closure_set(v___f_2063_, 9, v_a_2042_);
lean_closure_set(v___f_2063_, 10, v_levelParams_2043_);
lean_closure_set(v___f_2063_, 11, v_matcherName_2044_);
lean_closure_set(v___f_2063_, 12, v___x_2045_);
lean_closure_set(v___f_2063_, 13, v_matcherInfo_2046_);
lean_closure_set(v___f_2063_, 14, v___x_2035_);
lean_closure_set(v___f_2063_, 15, v___x_2047_);
lean_closure_set(v___f_2063_, 16, v_uElimPos_x3f_2048_);
lean_closure_set(v___f_2063_, 17, v___f_2061_);
v___x_2064_ = l_Lean_Expr_forallE___override(v___x_2056_, v_alpha_2036_, v___x_2058_, v___x_2059_);
v___x_2065_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2055_, v___x_2064_, v___f_2063_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
return v___x_2065_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2035_ = stack[0].m_obj;
lean_object* v_alpha_2036_ = stack[1].m_obj;
lean_object* v___x_2037_ = stack[2].m_obj;
lean_object* v___x_2038_ = stack[3].m_obj;
lean_object* v_numDiscrs_2039_ = stack[4].m_obj;
lean_object* v___f_2040_ = stack[5].m_obj;
lean_object* v_a_2041_ = stack[6].m_obj;
lean_object* v_a_2042_ = stack[7].m_obj;
lean_object* v_levelParams_2043_ = stack[8].m_obj;
lean_object* v_matcherName_2044_ = stack[9].m_obj;
lean_object* v___x_2045_ = stack[10].m_obj;
lean_object* v_matcherInfo_2046_ = stack[11].m_obj;
lean_object* v___x_2047_ = stack[12].m_obj;
lean_object* v_uElimPos_x3f_2048_ = stack[13].m_obj;
lean_object* v_beta_2049_ = stack[14].m_obj;
lean_object* v___y_2050_ = stack[15].m_obj;
lean_object* v___y_2051_ = stack[16].m_obj;
lean_object* v___y_2052_ = stack[17].m_obj;
lean_object* v___y_2053_ = stack[18].m_obj;
lean_object* v_res_2066_;
v_res_2066_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(v___x_2035_, v_alpha_2036_, v___x_2037_, v___x_2038_, v_numDiscrs_2039_, v___f_2040_, v_a_2041_, v_a_2042_, v_levelParams_2043_, v_matcherName_2044_, v___x_2045_, v_matcherInfo_2046_, v___x_2047_, v_uElimPos_x3f_2048_, v_beta_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
stack->m_obj
 = v_res_2066_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed(lean_object** _args){
lean_object* v___x_2067_ = _args[0];
lean_object* v_alpha_2068_ = _args[1];
lean_object* v___x_2069_ = _args[2];
lean_object* v___x_2070_ = _args[3];
lean_object* v_numDiscrs_2071_ = _args[4];
lean_object* v___f_2072_ = _args[5];
lean_object* v_a_2073_ = _args[6];
lean_object* v_a_2074_ = _args[7];
lean_object* v_levelParams_2075_ = _args[8];
lean_object* v_matcherName_2076_ = _args[9];
lean_object* v___x_2077_ = _args[10];
lean_object* v_matcherInfo_2078_ = _args[11];
lean_object* v___x_2079_ = _args[12];
lean_object* v_uElimPos_x3f_2080_ = _args[13];
lean_object* v_beta_2081_ = _args[14];
lean_object* v___y_2082_ = _args[15];
lean_object* v___y_2083_ = _args[16];
lean_object* v___y_2084_ = _args[17];
lean_object* v___y_2085_ = _args[18];
lean_object* v___y_2086_ = _args[19];
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7(v___x_2067_, v_alpha_2068_, v___x_2069_, v___x_2070_, v_numDiscrs_2071_, v___f_2072_, v_a_2073_, v_a_2074_, v_levelParams_2075_, v_matcherName_2076_, v___x_2077_, v_matcherInfo_2078_, v___x_2079_, v_uElimPos_x3f_2080_, v_beta_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
return v_res_2087_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(lean_object* v___x_2091_, lean_object* v___x_2092_, lean_object* v___x_2093_, lean_object* v_numDiscrs_2094_, lean_object* v___f_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_levelParams_2098_, lean_object* v_matcherName_2099_, lean_object* v___x_2100_, lean_object* v_matcherInfo_2101_, lean_object* v___x_2102_, lean_object* v_uElimPos_x3f_2103_, lean_object* v_alpha_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___f_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_inc(v_a_2096_);
lean_inc_ref(v_alpha_2104_);
v___f_2110_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__7___boxed), 20, 14);
lean_closure_set(v___f_2110_, 0, v___x_2091_);
lean_closure_set(v___f_2110_, 1, v_alpha_2104_);
lean_closure_set(v___f_2110_, 2, v___x_2092_);
lean_closure_set(v___f_2110_, 3, v___x_2093_);
lean_closure_set(v___f_2110_, 4, v_numDiscrs_2094_);
lean_closure_set(v___f_2110_, 5, v___f_2095_);
lean_closure_set(v___f_2110_, 6, v_a_2096_);
lean_closure_set(v___f_2110_, 7, v_a_2097_);
lean_closure_set(v___f_2110_, 8, v_levelParams_2098_);
lean_closure_set(v___f_2110_, 9, v_matcherName_2099_);
lean_closure_set(v___f_2110_, 10, v___x_2100_);
lean_closure_set(v___f_2110_, 11, v_matcherInfo_2101_);
lean_closure_set(v___f_2110_, 12, v___x_2102_);
lean_closure_set(v___f_2110_, 13, v_uElimPos_x3f_2103_);
v___x_2111_ = l_Lean_Level_param___override(v_a_2096_);
v___x_2112_ = l_Lean_Expr_sort___override(v___x_2111_);
v___x_2113_ = l_Lean_mkArrow(v_alpha_2104_, v___x_2112_, v___y_2107_, v___y_2108_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___closed__1));
v___x_2116_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2115_, v_a_2114_, v___f_2110_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
return v___x_2116_;
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v___f_2110_);
v_a_2117_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2113_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2113_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2091_ = stack[0].m_obj;
lean_object* v___x_2092_ = stack[1].m_obj;
lean_object* v___x_2093_ = stack[2].m_obj;
lean_object* v_numDiscrs_2094_ = stack[3].m_obj;
lean_object* v___f_2095_ = stack[4].m_obj;
lean_object* v_a_2096_ = stack[5].m_obj;
lean_object* v_a_2097_ = stack[6].m_obj;
lean_object* v_levelParams_2098_ = stack[7].m_obj;
lean_object* v_matcherName_2099_ = stack[8].m_obj;
lean_object* v___x_2100_ = stack[9].m_obj;
lean_object* v_matcherInfo_2101_ = stack[10].m_obj;
lean_object* v___x_2102_ = stack[11].m_obj;
lean_object* v_uElimPos_x3f_2103_ = stack[12].m_obj;
lean_object* v_alpha_2104_ = stack[13].m_obj;
lean_object* v___y_2105_ = stack[14].m_obj;
lean_object* v___y_2106_ = stack[15].m_obj;
lean_object* v___y_2107_ = stack[16].m_obj;
lean_object* v___y_2108_ = stack[17].m_obj;
lean_object* v_res_2125_;
v_res_2125_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(v___x_2091_, v___x_2092_, v___x_2093_, v_numDiscrs_2094_, v___f_2095_, v_a_2096_, v_a_2097_, v_levelParams_2098_, v_matcherName_2099_, v___x_2100_, v_matcherInfo_2101_, v___x_2102_, v_uElimPos_x3f_2103_, v_alpha_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
stack->m_obj
 = v_res_2125_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed(lean_object** _args){
lean_object* v___x_2126_ = _args[0];
lean_object* v___x_2127_ = _args[1];
lean_object* v___x_2128_ = _args[2];
lean_object* v_numDiscrs_2129_ = _args[3];
lean_object* v___f_2130_ = _args[4];
lean_object* v_a_2131_ = _args[5];
lean_object* v_a_2132_ = _args[6];
lean_object* v_levelParams_2133_ = _args[7];
lean_object* v_matcherName_2134_ = _args[8];
lean_object* v___x_2135_ = _args[9];
lean_object* v_matcherInfo_2136_ = _args[10];
lean_object* v___x_2137_ = _args[11];
lean_object* v_uElimPos_x3f_2138_ = _args[12];
lean_object* v_alpha_2139_ = _args[13];
lean_object* v___y_2140_ = _args[14];
lean_object* v___y_2141_ = _args[15];
lean_object* v___y_2142_ = _args[16];
lean_object* v___y_2143_ = _args[17];
lean_object* v___y_2144_ = _args[18];
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8(v___x_2126_, v___x_2127_, v___x_2128_, v_numDiscrs_2129_, v___f_2130_, v_a_2131_, v_a_2132_, v_levelParams_2133_, v_matcherName_2134_, v___x_2135_, v_matcherInfo_2136_, v___x_2137_, v_uElimPos_x3f_2138_, v_alpha_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2145_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(lean_object* v_numParams_2155_, lean_object* v___x_2156_, lean_object* v___x_2157_, lean_object* v_numDiscrs_2158_, lean_object* v___f_2159_, lean_object* v_levelParams_2160_, lean_object* v_matcherName_2161_, lean_object* v_matcherInfo_2162_, lean_object* v___x_2163_, lean_object* v_uElimPos_x3f_2164_, lean_object* v_xs_2165_, lean_object* v_x_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2172_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2155_);
lean_inc_ref(v_xs_2165_);
v___x_2173_ = l_Array_toSubarray___redArg(v_xs_2165_, v___x_2172_, v_numParams_2155_);
v___x_2174_ = lean_array_get(v___x_2156_, v_xs_2165_, v_numParams_2155_);
lean_dec(v_numParams_2155_);
lean_dec_ref(v_xs_2165_);
v___x_2175_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__1));
v___x_2176_ = l_Lean_Core_mkFreshUserName(v___x_2175_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__3));
v___x_2179_ = l_Lean_Core_mkFreshUserName(v___x_2178_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___f_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
lean_inc(v_a_2177_);
v___f_2181_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__8___boxed), 19, 13);
lean_closure_set(v___f_2181_, 0, v___x_2172_);
lean_closure_set(v___f_2181_, 1, v___x_2174_);
lean_closure_set(v___f_2181_, 2, v___x_2157_);
lean_closure_set(v___f_2181_, 3, v_numDiscrs_2158_);
lean_closure_set(v___f_2181_, 4, v___f_2159_);
lean_closure_set(v___f_2181_, 5, v_a_2180_);
lean_closure_set(v___f_2181_, 6, v_a_2177_);
lean_closure_set(v___f_2181_, 7, v_levelParams_2160_);
lean_closure_set(v___f_2181_, 8, v_matcherName_2161_);
lean_closure_set(v___f_2181_, 9, v___x_2173_);
lean_closure_set(v___f_2181_, 10, v_matcherInfo_2162_);
lean_closure_set(v___f_2181_, 11, v___x_2163_);
lean_closure_set(v___f_2181_, 12, v_uElimPos_x3f_2164_);
v___x_2182_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___closed__5));
v___x_2183_ = l_Lean_Level_param___override(v_a_2177_);
v___x_2184_ = l_Lean_Expr_sort___override(v___x_2183_);
v___x_2185_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v___x_2182_, v___x_2184_, v___f_2181_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
return v___x_2185_;
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_a_2177_);
lean_dec(v___x_2174_);
lean_dec_ref(v___x_2173_);
lean_dec(v_uElimPos_x3f_2164_);
lean_dec(v___x_2163_);
lean_dec_ref(v_matcherInfo_2162_);
lean_dec(v_matcherName_2161_);
lean_dec(v_levelParams_2160_);
lean_dec_ref(v___f_2159_);
lean_dec(v_numDiscrs_2158_);
lean_dec(v___x_2157_);
v_a_2186_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2179_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2179_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v___x_2174_);
lean_dec_ref(v___x_2173_);
lean_dec(v_uElimPos_x3f_2164_);
lean_dec(v___x_2163_);
lean_dec_ref(v_matcherInfo_2162_);
lean_dec(v_matcherName_2161_);
lean_dec(v_levelParams_2160_);
lean_dec_ref(v___f_2159_);
lean_dec(v_numDiscrs_2158_);
lean_dec(v___x_2157_);
v_a_2194_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2176_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2176_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_numParams_2155_ = stack[0].m_obj;
lean_object* v___x_2156_ = stack[1].m_obj;
lean_object* v___x_2157_ = stack[2].m_obj;
lean_object* v_numDiscrs_2158_ = stack[3].m_obj;
lean_object* v___f_2159_ = stack[4].m_obj;
lean_object* v_levelParams_2160_ = stack[5].m_obj;
lean_object* v_matcherName_2161_ = stack[6].m_obj;
lean_object* v_matcherInfo_2162_ = stack[7].m_obj;
lean_object* v___x_2163_ = stack[8].m_obj;
lean_object* v_uElimPos_x3f_2164_ = stack[9].m_obj;
lean_object* v_xs_2165_ = stack[10].m_obj;
lean_object* v_x_2166_ = stack[11].m_obj;
lean_object* v___y_2167_ = stack[12].m_obj;
lean_object* v___y_2168_ = stack[13].m_obj;
lean_object* v___y_2169_ = stack[14].m_obj;
lean_object* v___y_2170_ = stack[15].m_obj;
lean_object* v_res_2202_;
v_res_2202_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(v_numParams_2155_, v___x_2156_, v___x_2157_, v_numDiscrs_2158_, v___f_2159_, v_levelParams_2160_, v_matcherName_2161_, v_matcherInfo_2162_, v___x_2163_, v_uElimPos_x3f_2164_, v_xs_2165_, v_x_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
stack->m_obj
 = v_res_2202_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed(lean_object** _args){
lean_object* v_numParams_2203_ = _args[0];
lean_object* v___x_2204_ = _args[1];
lean_object* v___x_2205_ = _args[2];
lean_object* v_numDiscrs_2206_ = _args[3];
lean_object* v___f_2207_ = _args[4];
lean_object* v_levelParams_2208_ = _args[5];
lean_object* v_matcherName_2209_ = _args[6];
lean_object* v_matcherInfo_2210_ = _args[7];
lean_object* v___x_2211_ = _args[8];
lean_object* v_uElimPos_x3f_2212_ = _args[9];
lean_object* v_xs_2213_ = _args[10];
lean_object* v_x_2214_ = _args[11];
lean_object* v___y_2215_ = _args[12];
lean_object* v___y_2216_ = _args[13];
lean_object* v___y_2217_ = _args[14];
lean_object* v___y_2218_ = _args[15];
lean_object* v___y_2219_ = _args[16];
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9(v_numParams_2203_, v___x_2204_, v___x_2205_, v_numDiscrs_2206_, v___f_2207_, v_levelParams_2208_, v_matcherName_2209_, v_matcherInfo_2210_, v___x_2211_, v_uElimPos_x3f_2212_, v_xs_2213_, v_x_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec_ref(v_x_2214_);
lean_dec_ref(v___x_2204_);
return v_res_2220_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(lean_object* v_ref_2221_, lean_object* v_msg_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_toCold_2228_; lean_object* v_currRecDepth_2229_; lean_object* v_ref_2230_; uint16_t v_optionFlags_2231_; uint8_t v_suppressElabErrors_2232_; uint8_t v_isRecordingDeps_2233_; lean_object* v_ref_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v_toCold_2228_ = lean_ctor_get(v___y_2225_, 0);
v_currRecDepth_2229_ = lean_ctor_get(v___y_2225_, 1);
v_ref_2230_ = lean_ctor_get(v___y_2225_, 2);
v_optionFlags_2231_ = lean_ctor_get_uint16(v___y_2225_, sizeof(void*)*3);
v_suppressElabErrors_2232_ = lean_ctor_get_uint8(v___y_2225_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2233_ = lean_ctor_get_uint8(v___y_2225_, sizeof(void*)*3 + 3);
v_ref_2234_ = l_Lean_replaceRef(v_ref_2221_, v_ref_2230_);
lean_inc(v_currRecDepth_2229_);
lean_inc_ref(v_toCold_2228_);
v___x_2235_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2235_, 0, v_toCold_2228_);
lean_ctor_set(v___x_2235_, 1, v_currRecDepth_2229_);
lean_ctor_set(v___x_2235_, 2, v_ref_2234_);
lean_ctor_set_uint16(v___x_2235_, sizeof(void*)*3, v_optionFlags_2231_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*3 + 2, v_suppressElabErrors_2232_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*3 + 3, v_isRecordingDeps_2233_);
v___x_2236_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v_msg_2222_, v___y_2223_, v___y_2224_, v___x_2235_, v___y_2226_);
lean_dec_ref_known(v___x_2235_, 3);
return v___x_2236_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2221_ = stack[0].m_obj;
lean_object* v_msg_2222_ = stack[1].m_obj;
lean_object* v___y_2223_ = stack[2].m_obj;
lean_object* v___y_2224_ = stack[3].m_obj;
lean_object* v___y_2225_ = stack[4].m_obj;
lean_object* v___y_2226_ = stack[5].m_obj;
lean_object* v_res_2237_;
v_res_2237_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2221_, v_msg_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
stack->m_obj
 = v_res_2237_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_ref_2238_, lean_object* v_msg_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2238_, v_msg_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v_ref_2238_);
return v_res_2245_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2246_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
return v___x_2248_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2249_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2251_ = lean_unsigned_to_nat(0u);
v___x_2252_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
lean_ctor_set(v___x_2252_, 2, v___x_2251_);
lean_ctor_set(v___x_2252_, 3, v___x_2251_);
lean_ctor_set(v___x_2252_, 4, v___x_2250_);
lean_ctor_set(v___x_2252_, 5, v___x_2250_);
lean_ctor_set(v___x_2252_, 6, v___x_2250_);
lean_ctor_set(v___x_2252_, 7, v___x_2250_);
lean_ctor_set(v___x_2252_, 8, v___x_2250_);
lean_ctor_set(v___x_2252_, 9, v___x_2250_);
lean_ctor_set(v___x_2252_, 10, v___x_2250_);
lean_ctor_set(v___x_2252_, 11, v___x_2249_);
return v___x_2252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = lean_unsigned_to_nat(32u);
v___x_2254_ = lean_mk_empty_array_with_capacity(v___x_2253_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2256_ = ((size_t)5ULL);
v___x_2257_ = lean_unsigned_to_nat(0u);
v___x_2258_ = lean_unsigned_to_nat(32u);
v___x_2259_ = lean_mk_empty_array_with_capacity(v___x_2258_);
v___x_2260_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__3);
v___x_2261_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v___x_2259_);
lean_ctor_set(v___x_2261_, 2, v___x_2257_);
lean_ctor_set(v___x_2261_, 3, v___x_2257_);
lean_ctor_set_usize(v___x_2261_, 4, v___x_2256_);
return v___x_2261_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2262_ = lean_box(1);
v___x_2263_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__4);
v___x_2264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_2265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v___x_2263_);
lean_ctor_set(v___x_2265_, 2, v___x_2262_);
return v___x_2265_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__6));
v___x_2268_ = l_Lean_stringToMessageData(v___x_2267_);
return v___x_2268_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__8));
v___x_2271_ = l_Lean_stringToMessageData(v___x_2270_);
return v___x_2271_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__10));
v___x_2274_ = l_Lean_stringToMessageData(v___x_2273_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__12));
v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__14));
v___x_2280_ = l_Lean_stringToMessageData(v___x_2279_);
return v___x_2280_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__16));
v___x_2283_ = l_Lean_stringToMessageData(v___x_2282_);
return v___x_2283_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__18));
v___x_2286_ = l_Lean_stringToMessageData(v___x_2285_);
return v___x_2286_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__21(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__20));
v___x_2289_ = l_Lean_stringToMessageData(v___x_2288_);
return v___x_2289_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__23(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__22));
v___x_2292_ = l_Lean_stringToMessageData(v___x_2291_);
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__25(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__24));
v___x_2295_ = l_Lean_stringToMessageData(v___x_2294_);
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__27(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__26));
v___x_2298_ = l_Lean_stringToMessageData(v___x_2297_);
return v___x_2298_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_2299_, lean_object* v_declHint_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v_env_2305_; uint8_t v___x_2306_; 
v___x_2303_ = lean_box(0);
v___x_2304_ = lean_st_ref_get(v___y_2301_);
v_env_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc_ref(v_env_2305_);
lean_dec(v___x_2304_);
v___x_2306_ = l_Lean_Name_isAnonymous(v_declHint_2300_);
if (v___x_2306_ == 0)
{
uint8_t v_isExporting_2307_; 
v_isExporting_2307_ = lean_ctor_get_uint8(v_env_2305_, sizeof(void*)*13);
if (v_isExporting_2307_ == 0)
{
lean_object* v___x_2308_; 
lean_dec_ref(v_env_2305_);
lean_dec(v_declHint_2300_);
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v_msg_2299_);
return v___x_2308_;
}
else
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
lean_inc_ref(v_env_2305_);
v___x_2309_ = l_Lean_Environment_setExporting(v_env_2305_, v___x_2306_);
lean_inc(v_declHint_2300_);
lean_inc_ref(v___x_2309_);
v___x_2310_ = l_Lean_Environment_contains(v___x_2309_, v_declHint_2300_, v_isExporting_2307_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; 
lean_dec_ref(v___x_2309_);
lean_dec_ref(v_env_2305_);
lean_dec(v_declHint_2300_);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v_msg_2299_);
return v___x_2311_;
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v_c_2317_; lean_object* v___x_2318_; 
v___x_2312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_2313_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_2314_ = l_Lean_Options_empty;
v___x_2315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2309_);
lean_ctor_set(v___x_2315_, 1, v___x_2312_);
lean_ctor_set(v___x_2315_, 2, v___x_2313_);
lean_ctor_set(v___x_2315_, 3, v___x_2314_);
lean_inc(v_declHint_2300_);
v___x_2316_ = l_Lean_MessageData_ofConstName(v_declHint_2300_, v___x_2306_);
v_c_2317_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2317_, 0, v___x_2315_);
lean_ctor_set(v_c_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2305_, v_declHint_2300_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_dec_ref(v_env_2305_);
lean_dec(v_declHint_2300_);
v___x_2319_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
lean_ctor_set(v___x_2320_, 1, v_c_2317_);
v___x_2321_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = l_Lean_MessageData_note(v___x_2322_);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v_msg_2299_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
return v___x_2325_;
}
else
{
lean_object* v_val_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2382_; 
v_val_2326_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2328_ = v___x_2318_;
v_isShared_2329_ = v_isSharedCheck_2382_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_val_2326_);
lean_dec(v___x_2318_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2382_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v_modules_2331_; lean_object* v_moduleNames_2332_; lean_object* v_mod_2333_; uint8_t v___y_2335_; uint8_t v___x_2365_; 
v___x_2330_ = l_Lean_Environment_header(v_env_2305_);
lean_dec_ref(v_env_2305_);
v_modules_2331_ = lean_ctor_get(v___x_2330_, 3);
lean_inc_ref(v_modules_2331_);
v_moduleNames_2332_ = lean_ctor_get(v___x_2330_, 4);
lean_inc_ref(v_moduleNames_2332_);
lean_dec_ref(v___x_2330_);
v_mod_2333_ = lean_array_get(v___x_2303_, v_moduleNames_2332_, v_val_2326_);
lean_dec_ref(v_moduleNames_2332_);
v___x_2365_ = l_Lean_isPrivateName(v_declHint_2300_);
lean_dec(v_declHint_2300_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = lean_array_get_size(v_modules_2331_);
v___x_2367_ = lean_nat_dec_lt(v_val_2326_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_dec_ref(v_modules_2331_);
lean_dec(v_val_2326_);
v___y_2335_ = v___x_2365_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2368_; lean_object* v_toImport_2369_; uint8_t v_isExported_2370_; 
v___x_2368_ = lean_array_fget(v_modules_2331_, v_val_2326_);
lean_dec(v_val_2326_);
lean_dec_ref(v_modules_2331_);
v_toImport_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc_ref(v_toImport_2369_);
lean_dec(v___x_2368_);
v_isExported_2370_ = lean_ctor_get_uint8(v_toImport_2369_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2369_);
v___y_2335_ = v_isExported_2370_;
goto v___jp_2334_;
}
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_dec_ref(v_modules_2331_);
lean_del_object(v___x_2328_);
lean_dec(v_val_2326_);
v___x_2371_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_2372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
lean_ctor_set(v___x_2372_, 1, v_c_2317_);
v___x_2373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__25);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = l_Lean_MessageData_ofName(v_mod_2333_);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__27);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = l_Lean_MessageData_note(v___x_2378_);
v___x_2380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2380_, 0, v_msg_2299_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
v___jp_2334_:
{
if (v___y_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2336_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v_c_2317_);
v___x_2338_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_2339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = l_Lean_MessageData_ofName(v_mod_2333_);
v___x_2341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
v___x_2342_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2341_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = l_Lean_MessageData_note(v___x_2343_);
v___x_2345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2345_, 0, v_msg_2299_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set_tag(v___x_2328_, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2345_);
v___x_2347_ = v___x_2328_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2349_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v_c_2317_);
v___x_2351_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_2352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = l_Lean_MessageData_ofName(v_mod_2333_);
lean_inc_ref(v___x_2353_);
v___x_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__21);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set(v___x_2357_, 1, v___x_2353_);
v___x_2358_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__23);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = l_Lean_MessageData_note(v___x_2359_);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v_msg_2299_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set_tag(v___x_2328_, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2361_);
v___x_2363_ = v___x_2328_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
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
}
}
}
else
{
lean_object* v___x_2383_; 
lean_dec_ref(v_env_2305_);
lean_dec(v_declHint_2300_);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v_msg_2299_);
return v___x_2383_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2299_ = stack[0].m_obj;
lean_object* v_declHint_2300_ = stack[1].m_obj;
lean_object* v___y_2301_ = stack[2].m_obj;
lean_object* v_res_2384_;
v_res_2384_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2299_, v_declHint_2300_, v___y_2301_);
stack->m_obj
 = v_res_2384_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2385_, lean_object* v_declHint_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2385_, v_declHint_2386_, v___y_2387_);
lean_dec(v___y_2387_);
return v_res_2389_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(lean_object* v_msg_2390_, lean_object* v_declHint_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2407_; 
v___x_2397_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2390_, v_declHint_2391_, v___y_2395_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2407_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2407_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2402_ = l_Lean_unknownIdentifierMessageTag;
v___x_2403_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v_a_2398_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2403_);
v___x_2405_ = v___x_2400_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2390_ = stack[0].m_obj;
lean_object* v_declHint_2391_ = stack[1].m_obj;
lean_object* v___y_2392_ = stack[2].m_obj;
lean_object* v___y_2393_ = stack[3].m_obj;
lean_object* v___y_2394_ = stack[4].m_obj;
lean_object* v___y_2395_ = stack[5].m_obj;
lean_object* v_res_2408_;
v_res_2408_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2390_, v_declHint_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
stack->m_obj
 = v_res_2408_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11___boxed(lean_object* v_msg_2409_, lean_object* v_declHint_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2409_, v_declHint_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2416_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_ref_2417_, lean_object* v_msg_2418_, lean_object* v_declHint_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; lean_object* v_a_2426_; lean_object* v___x_2427_; 
v___x_2425_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11(v_msg_2418_, v_declHint_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref(v___x_2425_);
v___x_2427_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2417_, v_a_2426_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2427_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2417_ = stack[0].m_obj;
lean_object* v_msg_2418_ = stack[1].m_obj;
lean_object* v_declHint_2419_ = stack[2].m_obj;
lean_object* v___y_2420_ = stack[3].m_obj;
lean_object* v___y_2421_ = stack[4].m_obj;
lean_object* v___y_2422_ = stack[5].m_obj;
lean_object* v___y_2423_ = stack[6].m_obj;
lean_object* v_res_2428_;
v_res_2428_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2417_, v_msg_2418_, v_declHint_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
stack->m_obj
 = v_res_2428_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_ref_2429_, lean_object* v_msg_2430_, lean_object* v_declHint_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2429_, v_msg_2430_, v_declHint_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v_ref_2429_);
return v_res_2437_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_2440_ = l_Lean_stringToMessageData(v___x_2439_);
return v___x_2440_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_2443_ = l_Lean_stringToMessageData(v___x_2442_);
return v___x_2443_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_2444_, lean_object* v_constName_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2451_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_2452_ = 0;
lean_inc(v_constName_2445_);
v___x_2453_ = l_Lean_MessageData_ofConstName(v_constName_2445_, v___x_2452_);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2451_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2444_, v___x_2456_, v_constName_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
return v___x_2457_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2444_ = stack[0].m_obj;
lean_object* v_constName_2445_ = stack[1].m_obj;
lean_object* v___y_2446_ = stack[2].m_obj;
lean_object* v___y_2447_ = stack[3].m_obj;
lean_object* v___y_2448_ = stack[4].m_obj;
lean_object* v___y_2449_ = stack[5].m_obj;
lean_object* v_res_2458_;
v_res_2458_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2444_, v_constName_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
stack->m_obj
 = v_res_2458_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_2459_, lean_object* v_constName_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2459_, v_constName_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v_ref_2459_);
return v_res_2466_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(lean_object* v_constName_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_ref_2473_; lean_object* v___x_2474_; 
v_ref_2473_ = lean_ctor_get(v___y_2470_, 2);
v___x_2474_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2473_, v_constName_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
return v___x_2474_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2467_ = stack[0].m_obj;
lean_object* v___y_2468_ = stack[1].m_obj;
lean_object* v___y_2469_ = stack[2].m_obj;
lean_object* v___y_2470_ = stack[3].m_obj;
lean_object* v___y_2471_ = stack[4].m_obj;
lean_object* v_res_2475_;
v_res_2475_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
stack->m_obj
 = v_res_2475_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
return v_res_2482_;
}
}
lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(lean_object* v_constName_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v___x_2489_; lean_object* v_env_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2489_ = lean_st_ref_get(v___y_2487_);
v_env_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc_ref(v_env_2490_);
lean_dec(v___x_2489_);
v___x_2491_ = 0;
lean_inc(v_constName_2483_);
v___x_2492_ = l_Lean_Environment_findConstVal_x3f(v_env_2490_, v_constName_2483_, v___x_2491_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
return v___x_2493_;
}
else
{
lean_object* v_val_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v_constName_2483_);
v_val_2494_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2492_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_val_2494_);
lean_dec(v___x_2492_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set_tag(v___x_2496_, 0);
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_val_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2483_ = stack[0].m_obj;
lean_object* v___y_2484_ = stack[1].m_obj;
lean_object* v___y_2485_ = stack[2].m_obj;
lean_object* v___y_2486_ = stack[3].m_obj;
lean_object* v___y_2487_ = stack[4].m_obj;
lean_object* v_res_2502_;
v_res_2502_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_constName_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
stack->m_obj
 = v_res_2502_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0___boxed(lean_object* v_constName_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_constName_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
return v_res_2509_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(lean_object* v_matcherName_2510_, lean_object* v_matcherInfo_2511_, lean_object* v___x_2512_, lean_object* v___f_2513_, lean_object* v___x_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2520_; 
lean_inc(v_matcherName_2510_);
v___x_2520_ = l_Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0(v_matcherName_2510_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v_levelParams_2522_; lean_object* v_type_2523_; lean_object* v_numParams_2524_; lean_object* v_numDiscrs_2525_; lean_object* v_uElimPos_x3f_2526_; lean_object* v___x_2527_; lean_object* v___f_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v_levelParams_2522_ = lean_ctor_get(v_a_2521_, 1);
lean_inc(v_levelParams_2522_);
v_type_2523_ = lean_ctor_get(v_a_2521_, 2);
lean_inc_ref(v_type_2523_);
lean_dec(v_a_2521_);
v_numParams_2524_ = lean_ctor_get(v_matcherInfo_2511_, 0);
lean_inc_n(v_numParams_2524_, 2);
v_numDiscrs_2525_ = lean_ctor_get(v_matcherInfo_2511_, 1);
lean_inc(v_numDiscrs_2525_);
v_uElimPos_x3f_2526_ = lean_ctor_get(v_matcherInfo_2511_, 3);
lean_inc(v_uElimPos_x3f_2526_);
v___x_2527_ = lean_unsigned_to_nat(1u);
v___f_2528_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__9___boxed), 17, 10);
lean_closure_set(v___f_2528_, 0, v_numParams_2524_);
lean_closure_set(v___f_2528_, 1, v___x_2512_);
lean_closure_set(v___f_2528_, 2, v___x_2527_);
lean_closure_set(v___f_2528_, 3, v_numDiscrs_2525_);
lean_closure_set(v___f_2528_, 4, v___f_2513_);
lean_closure_set(v___f_2528_, 5, v_levelParams_2522_);
lean_closure_set(v___f_2528_, 6, v_matcherName_2510_);
lean_closure_set(v___f_2528_, 7, v_matcherInfo_2511_);
lean_closure_set(v___f_2528_, 8, v___x_2514_);
lean_closure_set(v___f_2528_, 9, v_uElimPos_x3f_2526_);
v___x_2529_ = lean_nat_add(v_numParams_2524_, v___x_2527_);
lean_dec(v_numParams_2524_);
v___x_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
v___x_2531_ = 0;
v___x_2532_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg(v_type_2523_, v___x_2530_, v___f_2528_, v___x_2531_, v___x_2531_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
return v___x_2532_;
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v___x_2514_);
lean_dec_ref(v___f_2513_);
lean_dec_ref(v___x_2512_);
lean_dec_ref(v_matcherInfo_2511_);
lean_dec(v_matcherName_2510_);
v_a_2533_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2520_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2520_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherName_2510_ = stack[0].m_obj;
lean_object* v_matcherInfo_2511_ = stack[1].m_obj;
lean_object* v___x_2512_ = stack[2].m_obj;
lean_object* v___f_2513_ = stack[3].m_obj;
lean_object* v___x_2514_ = stack[4].m_obj;
lean_object* v___y_2515_ = stack[5].m_obj;
lean_object* v___y_2516_ = stack[6].m_obj;
lean_object* v___y_2517_ = stack[7].m_obj;
lean_object* v___y_2518_ = stack[8].m_obj;
lean_object* v_res_2541_;
v_res_2541_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(v_matcherName_2510_, v_matcherInfo_2511_, v___x_2512_, v___f_2513_, v___x_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
stack->m_obj
 = v_res_2541_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed(lean_object* v_matcherName_2542_, lean_object* v_matcherInfo_2543_, lean_object* v___x_2544_, lean_object* v___f_2545_, lean_object* v___x_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10(v_matcherName_2542_, v_matcherInfo_2543_, v___x_2544_, v___f_2545_, v___x_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11(lean_object* v___x_2553_, lean_object* v_e_2554_){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = l_Lean_indentD(v_e_2554_);
v___x_2556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2553_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
return v___x_2556_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(lean_object* v___f_2557_, lean_object* v___f_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2557_, v___f_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
v_a_2573_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2564_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2564_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2557_ = stack[0].m_obj;
lean_object* v___f_2558_ = stack[1].m_obj;
lean_object* v___y_2559_ = stack[2].m_obj;
lean_object* v___y_2560_ = stack[3].m_obj;
lean_object* v___y_2561_ = stack[4].m_obj;
lean_object* v___y_2562_ = stack[5].m_obj;
lean_object* v_res_2581_;
v_res_2581_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(v___f_2557_, v___f_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
stack->m_obj
 = v_res_2581_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed(lean_object* v___f_2582_, lean_object* v___f_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12(v___f_2582_, v___f_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2589_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__3));
v___x_2596_ = l_Lean_stringToMessageData(v___x_2595_);
return v___x_2596_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(lean_object* v_matcherName_2597_, lean_object* v_matcherInfo_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v_env_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___f_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___f_2615_; lean_object* v___f_2616_; lean_object* v___x_2617_; 
v___f_2604_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__0));
v___x_2605_ = l_Lean_instInhabitedExpr;
v___x_2606_ = lean_st_ref_get(v_a_2602_);
v_env_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc_ref(v_env_2607_);
lean_dec(v___x_2606_);
lean_inc_n(v_matcherName_2597_, 3);
v___x_2608_ = l_Lean_mkPrivateName(v_env_2607_, v_matcherName_2597_);
lean_dec_ref(v_env_2607_);
v___x_2609_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__2));
v___x_2610_ = l_Lean_Name_append(v___x_2608_, v___x_2609_);
lean_inc_n(v___x_2610_, 2);
v___f_2611_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__10___boxed), 10, 5);
lean_closure_set(v___f_2611_, 0, v_matcherName_2597_);
lean_closure_set(v___f_2611_, 1, v_matcherInfo_2598_);
lean_closure_set(v___f_2611_, 2, v___x_2605_);
lean_closure_set(v___f_2611_, 3, v___f_2604_);
lean_closure_set(v___f_2611_, 4, v___x_2610_);
v___x_2612_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___closed__4);
v___x_2613_ = l_Lean_MessageData_ofName(v_matcherName_2597_);
v___x_2614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2612_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___f_2615_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_2615_, 0, v___x_2614_);
v___f_2616_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__12___boxed), 7, 2);
lean_closure_set(v___f_2616_, 0, v___f_2611_);
lean_closure_set(v___f_2616_, 1, v___f_2615_);
v___x_2617_ = l_Lean_Meta_realizeConst(v_matcherName_2597_, v___x_2610_, v___f_2616_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2624_ == 0)
{
lean_object* v_unused_2625_; 
v_unused_2625_ = lean_ctor_get(v___x_2617_, 0);
lean_dec(v_unused_2625_);
v___x_2619_ = v___x_2617_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_dec(v___x_2617_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2610_);
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2610_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec(v___x_2610_);
v_a_2626_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2617_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2617_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherName_2597_ = stack[0].m_obj;
lean_object* v_matcherInfo_2598_ = stack[1].m_obj;
lean_object* v_a_2599_ = stack[2].m_obj;
lean_object* v_a_2600_ = stack[3].m_obj;
lean_object* v_a_2601_ = stack[4].m_obj;
lean_object* v_a_2602_ = stack[5].m_obj;
lean_object* v_res_2634_;
v_res_2634_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_2597_, v_matcherInfo_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
stack->m_obj
 = v_res_2634_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___boxed(lean_object* v_matcherName_2635_, lean_object* v_matcherInfo_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_2635_, v_matcherInfo_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
return v_res_2642_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(lean_object* v_as_2643_, lean_object* v_as_x27_2644_, lean_object* v_b_2645_, lean_object* v_a_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___redArg(v_as_x27_2644_, v_b_2645_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2652_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2643_ = stack[0].m_obj;
lean_object* v_as_x27_2644_ = stack[1].m_obj;
lean_object* v_b_2645_ = stack[2].m_obj;
lean_object* v___y_2647_ = stack[4].m_obj;
lean_object* v___y_2648_ = stack[5].m_obj;
lean_object* v___y_2649_ = stack[6].m_obj;
lean_object* v___y_2650_ = stack[7].m_obj;
lean_object* v_res_2653_;
v_res_2653_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(v_as_2643_, v_as_x27_2644_, v_b_2645_, lean_box(0), v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
stack->m_obj
 = v_res_2653_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5___boxed(lean_object* v_as_2654_, lean_object* v_as_x27_2655_, lean_object* v_b_2656_, lean_object* v_a_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__5(v_as_2654_, v_as_x27_2655_, v_b_2656_, v_a_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v_as_x27_2655_);
lean_dec(v_as_2654_);
return v_res_2663_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(lean_object* v_00_u03b1_2664_, lean_object* v_name_2665_, uint8_t v_bi_2666_, lean_object* v_type_2667_, lean_object* v_k_2668_, uint8_t v_kind_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___redArg(v_name_2665_, v_bi_2666_, v_type_2667_, v_k_2668_, v_kind_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2665_ = stack[1].m_obj;
uint8_t v_bi_2666_ = stack[2].m_num;
lean_object* v_type_2667_ = stack[3].m_obj;
lean_object* v_k_2668_ = stack[4].m_obj;
uint8_t v_kind_2669_ = stack[5].m_num;
lean_object* v___y_2670_ = stack[6].m_obj;
lean_object* v___y_2671_ = stack[7].m_obj;
lean_object* v___y_2672_ = stack[8].m_obj;
lean_object* v___y_2673_ = stack[9].m_obj;
lean_object* v_res_2676_;
v_res_2676_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(lean_box(0), v_name_2665_, v_bi_2666_, v_type_2667_, v_k_2668_, v_kind_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
stack->m_obj
 = v_res_2676_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2677_, lean_object* v_name_2678_, lean_object* v_bi_2679_, lean_object* v_type_2680_, lean_object* v_k_2681_, lean_object* v_kind_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v_bi_boxed_2688_; uint8_t v_kind_boxed_2689_; lean_object* v_res_2690_; 
v_bi_boxed_2688_ = lean_unbox(v_bi_2679_);
v_kind_boxed_2689_ = lean_unbox(v_kind_2682_);
v_res_2690_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_spec__8(v_00_u03b1_2677_, v_name_2678_, v_bi_boxed_2688_, v_type_2680_, v_k_2681_, v_kind_boxed_2689_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
return v_res_2690_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(lean_object* v_00_u03b1_2691_, lean_object* v_name_2692_, lean_object* v_type_2693_, lean_object* v_k_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___redArg(v_name_2692_, v_type_2693_, v_k_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2692_ = stack[1].m_obj;
lean_object* v_type_2693_ = stack[2].m_obj;
lean_object* v_k_2694_ = stack[3].m_obj;
lean_object* v___y_2695_ = stack[4].m_obj;
lean_object* v___y_2696_ = stack[5].m_obj;
lean_object* v___y_2697_ = stack[6].m_obj;
lean_object* v___y_2698_ = stack[7].m_obj;
lean_object* v_res_2701_;
v_res_2701_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(lean_box(0), v_name_2692_, v_type_2693_, v_k_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
stack->m_obj
 = v_res_2701_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7___boxed(lean_object* v_00_u03b1_2702_, lean_object* v_name_2703_, lean_object* v_type_2704_, lean_object* v_k_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__7(v_00_u03b1_2702_, v_name_2703_, v_type_2704_, v_k_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
return v_res_2711_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(lean_object* v_00_u03b1_2712_, lean_object* v_constName_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___redArg(v_constName_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2713_ = stack[1].m_obj;
lean_object* v___y_2714_ = stack[2].m_obj;
lean_object* v___y_2715_ = stack[3].m_obj;
lean_object* v___y_2716_ = stack[4].m_obj;
lean_object* v___y_2717_ = stack[5].m_obj;
lean_object* v_res_2720_;
v_res_2720_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(lean_box(0), v_constName_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
stack->m_obj
 = v_res_2720_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2721_, lean_object* v_constName_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0(v_00_u03b1_2721_, v_constName_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2728_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2729_, lean_object* v_ref_2730_, lean_object* v_constName_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg(v_ref_2730_, v_constName_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
return v___x_2737_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2730_ = stack[1].m_obj;
lean_object* v_constName_2731_ = stack[2].m_obj;
lean_object* v___y_2732_ = stack[3].m_obj;
lean_object* v___y_2733_ = stack[4].m_obj;
lean_object* v___y_2734_ = stack[5].m_obj;
lean_object* v___y_2735_ = stack[6].m_obj;
lean_object* v_res_2738_;
v_res_2738_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(lean_box(0), v_ref_2730_, v_constName_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
stack->m_obj
 = v_res_2738_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2739_, lean_object* v_ref_2740_, lean_object* v_constName_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4(v_00_u03b1_2739_, v_ref_2740_, v_constName_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v_ref_2740_);
return v_res_2747_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b1_2748_, lean_object* v_ref_2749_, lean_object* v_msg_2750_, lean_object* v_declHint_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2749_, v_msg_2750_, v_declHint_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
return v___x_2757_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2749_ = stack[1].m_obj;
lean_object* v_msg_2750_ = stack[2].m_obj;
lean_object* v_declHint_2751_ = stack[3].m_obj;
lean_object* v___y_2752_ = stack[4].m_obj;
lean_object* v___y_2753_ = stack[5].m_obj;
lean_object* v___y_2754_ = stack[6].m_obj;
lean_object* v___y_2755_ = stack[7].m_obj;
lean_object* v_res_2758_;
v_res_2758_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(lean_box(0), v_ref_2749_, v_msg_2750_, v_declHint_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
stack->m_obj
 = v_res_2758_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b1_2759_, lean_object* v_ref_2760_, lean_object* v_msg_2761_, lean_object* v_declHint_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10(v_00_u03b1_2759_, v_ref_2760_, v_msg_2761_, v_declHint_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v_ref_2760_);
return v_res_2768_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(lean_object* v_msg_2769_, lean_object* v_declHint_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg(v_msg_2769_, v_declHint_2770_, v___y_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2769_ = stack[0].m_obj;
lean_object* v_declHint_2770_ = stack[1].m_obj;
lean_object* v___y_2771_ = stack[2].m_obj;
lean_object* v___y_2772_ = stack[3].m_obj;
lean_object* v___y_2773_ = stack[4].m_obj;
lean_object* v___y_2774_ = stack[5].m_obj;
lean_object* v_res_2777_;
v_res_2777_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(v_msg_2769_, v_declHint_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
stack->m_obj
 = v_res_2777_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_2778_, lean_object* v_declHint_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12(v_msg_2778_, v_declHint_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
return v_res_2785_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_2786_, lean_object* v_ref_2787_, lean_object* v_msg_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___redArg(v_ref_2787_, v_msg_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
return v___x_2794_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2787_ = stack[1].m_obj;
lean_object* v_msg_2788_ = stack[2].m_obj;
lean_object* v___y_2789_ = stack[3].m_obj;
lean_object* v___y_2790_ = stack[4].m_obj;
lean_object* v___y_2791_ = stack[5].m_obj;
lean_object* v___y_2792_ = stack[6].m_obj;
lean_object* v_res_2795_;
v_res_2795_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(lean_box(0), v_ref_2787_, v_msg_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
stack->m_obj
 = v_res_2795_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_2796_, lean_object* v_ref_2797_, lean_object* v_msg_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__12(v_00_u03b1_2796_, v_ref_2797_, v_msg_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v_ref_2797_);
return v_res_2804_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(lean_object* v_msg_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___f_2815_; lean_object* v___x_34395__overap_2816_; lean_object* v___x_2817_; 
v___f_2815_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___closed__0));
v___x_34395__overap_2816_ = lean_panic_fn_borrowed(v___f_2815_, v_msg_2806_);
lean_inc(v___y_2813_);
lean_inc_ref(v___y_2812_);
lean_inc(v___y_2811_);
lean_inc_ref(v___y_2810_);
lean_inc(v___y_2809_);
lean_inc_ref(v___y_2808_);
lean_inc(v___y_2807_);
v___x_2817_ = lean_apply_8(v___x_34395__overap_2816_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, lean_box(0));
return v___x_2817_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2806_ = stack[0].m_obj;
lean_object* v___y_2807_ = stack[1].m_obj;
lean_object* v___y_2808_ = stack[2].m_obj;
lean_object* v___y_2809_ = stack[3].m_obj;
lean_object* v___y_2810_ = stack[4].m_obj;
lean_object* v___y_2811_ = stack[5].m_obj;
lean_object* v___y_2812_ = stack[6].m_obj;
lean_object* v___y_2813_ = stack[7].m_obj;
lean_object* v_res_2818_;
v_res_2818_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v_msg_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
stack->m_obj
 = v_res_2818_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2___boxed(lean_object* v_msg_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v_msg_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
return v_res_2828_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(lean_object* v_k_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v_b_2833_, lean_object* v_c_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; 
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
lean_inc(v___y_2832_);
lean_inc_ref(v___y_2831_);
lean_inc(v___y_2830_);
v___x_2840_ = lean_apply_10(v_k_2829_, v_b_2833_, v_c_2834_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, lean_box(0));
return v___x_2840_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2829_ = stack[0].m_obj;
lean_object* v___y_2830_ = stack[1].m_obj;
lean_object* v___y_2831_ = stack[2].m_obj;
lean_object* v___y_2832_ = stack[3].m_obj;
lean_object* v_b_2833_ = stack[4].m_obj;
lean_object* v_c_2834_ = stack[5].m_obj;
lean_object* v___y_2835_ = stack[6].m_obj;
lean_object* v___y_2836_ = stack[7].m_obj;
lean_object* v___y_2837_ = stack[8].m_obj;
lean_object* v___y_2838_ = stack[9].m_obj;
lean_object* v_res_2841_;
v_res_2841_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(v_k_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v_b_2833_, v_c_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
stack->m_obj
 = v_res_2841_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed(lean_object* v_k_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v_b_2846_, lean_object* v_c_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0(v_k_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v_b_2846_, v_c_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
return v_res_2853_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(lean_object* v_e_2854_, lean_object* v_k_2855_, uint8_t v_cleanupAnnotations_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v___f_2865_; uint8_t v___x_2866_; uint8_t v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_inc(v___y_2859_);
lean_inc_ref(v___y_2858_);
lean_inc(v___y_2857_);
v___f_2865_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2865_, 0, v_k_2855_);
lean_closure_set(v___f_2865_, 1, v___y_2857_);
lean_closure_set(v___f_2865_, 2, v___y_2858_);
lean_closure_set(v___f_2865_, 3, v___y_2859_);
v___x_2866_ = 1;
v___x_2867_ = 0;
v___x_2868_ = lean_box(0);
v___x_2869_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2854_, v___x_2866_, v___x_2867_, v___x_2866_, v___x_2867_, v___x_2868_, v___f_2865_, v_cleanupAnnotations_2856_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2869_) == 0)
{
return v___x_2869_;
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
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
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2854_ = stack[0].m_obj;
lean_object* v_k_2855_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_2856_ = stack[2].m_num;
lean_object* v___y_2857_ = stack[3].m_obj;
lean_object* v___y_2858_ = stack[4].m_obj;
lean_object* v___y_2859_ = stack[5].m_obj;
lean_object* v___y_2860_ = stack[6].m_obj;
lean_object* v___y_2861_ = stack[7].m_obj;
lean_object* v___y_2862_ = stack[8].m_obj;
lean_object* v___y_2863_ = stack[9].m_obj;
lean_object* v_res_2878_;
v_res_2878_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2854_, v_k_2855_, v_cleanupAnnotations_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
stack->m_obj
 = v_res_2878_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg___boxed(lean_object* v_e_2879_, lean_object* v_k_2880_, lean_object* v_cleanupAnnotations_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2890_; lean_object* v_res_2891_; 
v_cleanupAnnotations_boxed_2890_ = lean_unbox(v_cleanupAnnotations_2881_);
v_res_2891_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2879_, v_k_2880_, v_cleanupAnnotations_boxed_2890_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
return v_res_2891_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(lean_object* v_00_u03b1_2892_, lean_object* v_e_2893_, lean_object* v_k_2894_, uint8_t v_cleanupAnnotations_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_e_2893_, v_k_2894_, v_cleanupAnnotations_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
return v___x_2904_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2893_ = stack[1].m_obj;
lean_object* v_k_2894_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2895_ = stack[3].m_num;
lean_object* v___y_2896_ = stack[4].m_obj;
lean_object* v___y_2897_ = stack[5].m_obj;
lean_object* v___y_2898_ = stack[6].m_obj;
lean_object* v___y_2899_ = stack[7].m_obj;
lean_object* v___y_2900_ = stack[8].m_obj;
lean_object* v___y_2901_ = stack[9].m_obj;
lean_object* v___y_2902_ = stack[10].m_obj;
lean_object* v_res_2905_;
v_res_2905_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(lean_box(0), v_e_2893_, v_k_2894_, v_cleanupAnnotations_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
stack->m_obj
 = v_res_2905_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___boxed(lean_object* v_00_u03b1_2906_, lean_object* v_e_2907_, lean_object* v_k_2908_, lean_object* v_cleanupAnnotations_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2918_; lean_object* v_res_2919_; 
v_cleanupAnnotations_boxed_2918_ = lean_unbox(v_cleanupAnnotations_2909_);
v_res_2919_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3(v_00_u03b1_2906_, v_e_2907_, v_k_2908_, v_cleanupAnnotations_boxed_2918_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
return v_res_2919_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(uint8_t v___x_2920_, uint8_t v___x_2921_, uint8_t v___x_2922_, lean_object* v_xs_2923_, lean_object* v_motiveBody_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; lean_object* v___x_2940_; 
v___x_2933_ = l_Lean_Expr_bindingDomain_x21(v_motiveBody_2924_);
v___x_2934_ = l_Lean_Expr_bindingName_x21(v___x_2933_);
v___x_2935_ = l_Lean_Expr_bindingDomain_x21(v___x_2933_);
v___x_2936_ = l_Lean_Expr_bindingBody_x21(v___x_2933_);
lean_dec_ref(v___x_2933_);
v___x_2937_ = l_Lean_Expr_bindingDomain_x21(v___x_2936_);
lean_dec_ref(v___x_2936_);
v___x_2938_ = l_Lean_Expr_lam___override(v___x_2934_, v___x_2935_, v___x_2937_, v___x_2920_);
v___x_2939_ = 1;
v___x_2940_ = l_Lean_Meta_mkLambdaFVars(v_xs_2923_, v___x_2938_, v___x_2921_, v___x_2922_, v___x_2921_, v___x_2922_, v___x_2939_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
return v___x_2940_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2920_ = stack[0].m_num;
uint8_t v___x_2921_ = stack[1].m_num;
uint8_t v___x_2922_ = stack[2].m_num;
lean_object* v_xs_2923_ = stack[3].m_obj;
lean_object* v_motiveBody_2924_ = stack[4].m_obj;
lean_object* v___y_2925_ = stack[5].m_obj;
lean_object* v___y_2926_ = stack[6].m_obj;
lean_object* v___y_2927_ = stack[7].m_obj;
lean_object* v___y_2928_ = stack[8].m_obj;
lean_object* v___y_2929_ = stack[9].m_obj;
lean_object* v___y_2930_ = stack[10].m_obj;
lean_object* v___y_2931_ = stack[11].m_obj;
lean_object* v_res_2941_;
v_res_2941_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(v___x_2920_, v___x_2921_, v___x_2922_, v_xs_2923_, v_motiveBody_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
stack->m_obj
 = v_res_2941_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed(lean_object* v___x_2942_, lean_object* v___x_2943_, lean_object* v___x_2944_, lean_object* v_xs_2945_, lean_object* v_motiveBody_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
uint8_t v___x_42222__boxed_2955_; uint8_t v___x_42223__boxed_2956_; uint8_t v___x_42224__boxed_2957_; lean_object* v_res_2958_; 
v___x_42222__boxed_2955_ = lean_unbox(v___x_2942_);
v___x_42223__boxed_2956_ = lean_unbox(v___x_2943_);
v___x_42224__boxed_2957_ = lean_unbox(v___x_2944_);
v_res_2958_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0(v___x_42222__boxed_2955_, v___x_42223__boxed_2956_, v___x_42224__boxed_2957_, v_xs_2945_, v_motiveBody_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v_motiveBody_2946_);
lean_dec_ref(v_xs_2945_);
return v_res_2958_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(size_t v_sz_2959_, size_t v_i_2960_, lean_object* v_bs_2961_){
_start:
{
uint8_t v___x_2962_; 
v___x_2962_ = lean_usize_dec_lt(v_i_2960_, v_sz_2959_);
if (v___x_2962_ == 0)
{
return v_bs_2961_;
}
else
{
lean_object* v_v_2963_; lean_object* v___x_2964_; lean_object* v_bs_x27_2965_; lean_object* v___x_2966_; size_t v___x_2967_; size_t v___x_2968_; lean_object* v___x_2969_; 
v_v_2963_ = lean_array_uget(v_bs_2961_, v_i_2960_);
v___x_2964_ = lean_unsigned_to_nat(0u);
v_bs_x27_2965_ = lean_array_uset(v_bs_2961_, v_i_2960_, v___x_2964_);
v___x_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2966_, 0, v_v_2963_);
v___x_2967_ = ((size_t)1ULL);
v___x_2968_ = lean_usize_add(v_i_2960_, v___x_2967_);
v___x_2969_ = lean_array_uset(v_bs_x27_2965_, v_i_2960_, v___x_2966_);
v_i_2960_ = v___x_2968_;
v_bs_2961_ = v___x_2969_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2959_ = stack[0].m_num;
size_t v_i_2960_ = stack[1].m_num;
lean_object* v_bs_2961_ = stack[2].m_obj;
lean_object* v_res_2971_;
v_res_2971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_2959_, v_i_2960_, v_bs_2961_);
stack->m_obj
 = v_res_2971_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4___boxed(lean_object* v_sz_2972_, lean_object* v_i_2973_, lean_object* v_bs_2974_){
_start:
{
size_t v_sz_boxed_2975_; size_t v_i_boxed_2976_; lean_object* v_res_2977_; 
v_sz_boxed_2975_ = lean_unbox_usize(v_sz_2972_);
lean_dec(v_sz_2972_);
v_i_boxed_2976_ = lean_unbox_usize(v_i_2973_);
lean_dec(v_i_2973_);
v_res_2977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_boxed_2975_, v_i_boxed_2976_, v_bs_2974_);
return v_res_2977_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(lean_object* v_msg_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v_ref_2984_; lean_object* v___x_2985_; lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2994_; 
v_ref_2984_ = lean_ctor_get(v___y_2981_, 2);
v___x_2985_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_2994_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2994_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2992_; 
lean_inc(v_ref_2984_);
v___x_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2990_, 0, v_ref_2984_);
lean_ctor_set(v___x_2990_, 1, v_a_2986_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set_tag(v___x_2988_, 1);
lean_ctor_set(v___x_2988_, 0, v___x_2990_);
v___x_2992_ = v___x_2988_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2978_ = stack[0].m_obj;
lean_object* v___y_2979_ = stack[1].m_obj;
lean_object* v___y_2980_ = stack[2].m_obj;
lean_object* v___y_2981_ = stack[3].m_obj;
lean_object* v___y_2982_ = stack[4].m_obj;
lean_object* v_res_2995_;
v_res_2995_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
stack->m_obj
 = v_res_2995_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg___boxed(lean_object* v_msg_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
return v_res_3002_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(lean_object* v_declName_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; lean_object* v_env_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3006_ = lean_st_ref_get(v___y_3004_);
v_env_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc_ref(v_env_3007_);
lean_dec(v___x_3006_);
v___x_3008_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_3007_, v_declName_3003_);
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3003_ = stack[0].m_obj;
lean_object* v___y_3004_ = stack[1].m_obj;
lean_object* v_res_3010_;
v_res_3010_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3003_, v___y_3004_);
stack->m_obj
 = v_res_3010_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg___boxed(lean_object* v_declName_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3011_, v___y_3012_);
lean_dec(v___y_3012_);
return v_res_3014_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(lean_object* v_ref_3015_, lean_object* v_msg_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_toCold_3025_; lean_object* v_currRecDepth_3026_; lean_object* v_ref_3027_; uint16_t v_optionFlags_3028_; uint8_t v_suppressElabErrors_3029_; uint8_t v_isRecordingDeps_3030_; lean_object* v_ref_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_toCold_3025_ = lean_ctor_get(v___y_3022_, 0);
v_currRecDepth_3026_ = lean_ctor_get(v___y_3022_, 1);
v_ref_3027_ = lean_ctor_get(v___y_3022_, 2);
v_optionFlags_3028_ = lean_ctor_get_uint16(v___y_3022_, sizeof(void*)*3);
v_suppressElabErrors_3029_ = lean_ctor_get_uint8(v___y_3022_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3030_ = lean_ctor_get_uint8(v___y_3022_, sizeof(void*)*3 + 3);
v_ref_3031_ = l_Lean_replaceRef(v_ref_3015_, v_ref_3027_);
lean_inc(v_currRecDepth_3026_);
lean_inc_ref(v_toCold_3025_);
v___x_3032_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3032_, 0, v_toCold_3025_);
lean_ctor_set(v___x_3032_, 1, v_currRecDepth_3026_);
lean_ctor_set(v___x_3032_, 2, v_ref_3031_);
lean_ctor_set_uint16(v___x_3032_, sizeof(void*)*3, v_optionFlags_3028_);
lean_ctor_set_uint8(v___x_3032_, sizeof(void*)*3 + 2, v_suppressElabErrors_3029_);
lean_ctor_set_uint8(v___x_3032_, sizeof(void*)*3 + 3, v_isRecordingDeps_3030_);
v___x_3033_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_3016_, v___y_3020_, v___y_3021_, v___x_3032_, v___y_3023_);
lean_dec_ref_known(v___x_3032_, 3);
return v___x_3033_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3015_ = stack[0].m_obj;
lean_object* v_msg_3016_ = stack[1].m_obj;
lean_object* v___y_3017_ = stack[2].m_obj;
lean_object* v___y_3018_ = stack[3].m_obj;
lean_object* v___y_3019_ = stack[4].m_obj;
lean_object* v___y_3020_ = stack[5].m_obj;
lean_object* v___y_3021_ = stack[6].m_obj;
lean_object* v___y_3022_ = stack[7].m_obj;
lean_object* v___y_3023_ = stack[8].m_obj;
lean_object* v_res_3034_;
v_res_3034_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3015_, v_msg_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
stack->m_obj
 = v_res_3034_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg___boxed(lean_object* v_ref_3035_, lean_object* v_msg_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3035_, v_msg_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec(v_ref_3035_);
return v_res_3045_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_3046_, lean_object* v_declHint_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v_env_3052_; uint8_t v___x_3053_; 
v___x_3050_ = lean_box(0);
v___x_3051_ = lean_st_ref_get(v___y_3048_);
v_env_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc_ref(v_env_3052_);
lean_dec(v___x_3051_);
v___x_3053_ = l_Lean_Name_isAnonymous(v_declHint_3047_);
if (v___x_3053_ == 0)
{
uint8_t v_isExporting_3054_; 
v_isExporting_3054_ = lean_ctor_get_uint8(v_env_3052_, sizeof(void*)*13);
if (v_isExporting_3054_ == 0)
{
lean_object* v___x_3055_; 
lean_dec_ref(v_env_3052_);
lean_dec(v_declHint_3047_);
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v_msg_3046_);
return v___x_3055_;
}
else
{
lean_object* v___x_3056_; uint8_t v___x_3057_; 
lean_inc_ref(v_env_3052_);
v___x_3056_ = l_Lean_Environment_setExporting(v_env_3052_, v___x_3053_);
lean_inc(v_declHint_3047_);
lean_inc_ref(v___x_3056_);
v___x_3057_ = l_Lean_Environment_contains(v___x_3056_, v_declHint_3047_, v_isExporting_3054_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; 
lean_dec_ref(v___x_3056_);
lean_dec_ref(v_env_3052_);
lean_dec(v_declHint_3047_);
v___x_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3058_, 0, v_msg_3046_);
return v___x_3058_;
}
else
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v_c_3066_; lean_object* v___x_3067_; 
v___x_3059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_3060_ = lean_unsigned_to_nat(32u);
v___x_3061_ = lean_mk_empty_array_with_capacity(v___x_3060_);
lean_dec_ref(v___x_3061_);
v___x_3062_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__5);
v___x_3063_ = l_Lean_Options_empty;
v___x_3064_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3056_);
lean_ctor_set(v___x_3064_, 1, v___x_3059_);
lean_ctor_set(v___x_3064_, 2, v___x_3062_);
lean_ctor_set(v___x_3064_, 3, v___x_3063_);
lean_inc(v_declHint_3047_);
v___x_3065_ = l_Lean_MessageData_ofConstName(v_declHint_3047_, v___x_3053_);
v_c_3066_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3066_, 0, v___x_3064_);
lean_ctor_set(v_c_3066_, 1, v___x_3065_);
v___x_3067_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3052_, v_declHint_3047_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_dec_ref(v_env_3052_);
lean_dec(v_declHint_3047_);
v___x_3068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_3069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
lean_ctor_set(v___x_3069_, 1, v_c_3066_);
v___x_3070_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__9);
v___x_3071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = l_Lean_MessageData_note(v___x_3071_);
v___x_3073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3073_, 0, v_msg_3046_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
return v___x_3074_;
}
else
{
lean_object* v_val_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3131_; 
v_val_3075_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3077_ = v___x_3067_;
v_isShared_3078_ = v_isSharedCheck_3131_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_val_3075_);
lean_dec(v___x_3067_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3131_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; lean_object* v_modules_3080_; lean_object* v_moduleNames_3081_; lean_object* v_mod_3082_; uint8_t v___y_3084_; uint8_t v___x_3114_; 
v___x_3079_ = l_Lean_Environment_header(v_env_3052_);
lean_dec_ref(v_env_3052_);
v_modules_3080_ = lean_ctor_get(v___x_3079_, 3);
lean_inc_ref(v_modules_3080_);
v_moduleNames_3081_ = lean_ctor_get(v___x_3079_, 4);
lean_inc_ref(v_moduleNames_3081_);
lean_dec_ref(v___x_3079_);
v_mod_3082_ = lean_array_get(v___x_3050_, v_moduleNames_3081_, v_val_3075_);
lean_dec_ref(v_moduleNames_3081_);
v___x_3114_ = l_Lean_isPrivateName(v_declHint_3047_);
lean_dec(v_declHint_3047_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3115_ = lean_array_get_size(v_modules_3080_);
v___x_3116_ = lean_nat_dec_lt(v_val_3075_, v___x_3115_);
if (v___x_3116_ == 0)
{
lean_dec_ref(v_modules_3080_);
lean_dec(v_val_3075_);
v___y_3084_ = v___x_3114_;
goto v___jp_3083_;
}
else
{
lean_object* v___x_3117_; lean_object* v_toImport_3118_; uint8_t v_isExported_3119_; 
v___x_3117_ = lean_array_fget(v_modules_3080_, v_val_3075_);
lean_dec(v_val_3075_);
lean_dec_ref(v_modules_3080_);
v_toImport_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc_ref(v_toImport_3118_);
lean_dec(v___x_3117_);
v_isExported_3119_ = lean_ctor_get_uint8(v_toImport_3118_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_3118_);
v___y_3084_ = v_isExported_3119_;
goto v___jp_3083_;
}
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec_ref(v_modules_3080_);
lean_del_object(v___x_3077_);
lean_dec(v_val_3075_);
v___x_3120_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__7);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3120_);
lean_ctor_set(v___x_3121_, 1, v_c_3066_);
v___x_3122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__25);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_MessageData_ofName(v_mod_3082_);
v___x_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3123_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__27);
v___x_3127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3125_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = l_Lean_MessageData_note(v___x_3127_);
v___x_3129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3129_, 0, v_msg_3046_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
return v___x_3130_;
}
v___jp_3083_:
{
if (v___y_3084_ == 0)
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3085_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__11);
v___x_3086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
lean_ctor_set(v___x_3086_, 1, v_c_3066_);
v___x_3087_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__13);
v___x_3088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3086_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = l_Lean_MessageData_ofName(v_mod_3082_);
v___x_3090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3088_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
v___x_3091_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__15);
v___x_3092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3090_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
v___x_3093_ = l_Lean_MessageData_note(v___x_3092_);
v___x_3094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3094_, 0, v_msg_3046_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set_tag(v___x_3077_, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3094_);
v___x_3096_ = v___x_3077_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3098_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__17);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
lean_ctor_set(v___x_3099_, 1, v_c_3066_);
v___x_3100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__19);
v___x_3101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3099_);
lean_ctor_set(v___x_3101_, 1, v___x_3100_);
v___x_3102_ = l_Lean_MessageData_ofName(v_mod_3082_);
lean_inc_ref(v___x_3102_);
v___x_3103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3101_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__21);
v___x_3105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3103_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set(v___x_3106_, 1, v___x_3102_);
v___x_3107_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__23);
v___x_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = l_Lean_MessageData_note(v___x_3108_);
v___x_3110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3110_, 0, v_msg_3046_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set_tag(v___x_3077_, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3110_);
v___x_3112_ = v___x_3077_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
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
lean_object* v___x_3132_; 
lean_dec_ref(v_env_3052_);
lean_dec(v_declHint_3047_);
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v_msg_3046_);
return v___x_3132_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3046_ = stack[0].m_obj;
lean_object* v_declHint_3047_ = stack[1].m_obj;
lean_object* v___y_3048_ = stack[2].m_obj;
lean_object* v_res_3133_;
v_res_3133_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3046_, v_declHint_3047_, v___y_3048_);
stack->m_obj
 = v_res_3133_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_3134_, lean_object* v_declHint_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3134_, v_declHint_3135_, v___y_3136_);
lean_dec(v___y_3136_);
return v_res_3138_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(lean_object* v_msg_3139_, lean_object* v_declHint_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3159_; 
v___x_3149_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_3139_, v_declHint_3140_, v___y_3147_);
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3152_ = v___x_3149_;
v_isShared_3153_ = v_isSharedCheck_3159_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3159_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3154_ = l_Lean_unknownIdentifierMessageTag;
v___x_3155_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
lean_ctor_set(v___x_3155_, 1, v_a_3150_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 0, v___x_3155_);
v___x_3157_ = v___x_3152_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3139_ = stack[0].m_obj;
lean_object* v_declHint_3140_ = stack[1].m_obj;
lean_object* v___y_3141_ = stack[2].m_obj;
lean_object* v___y_3142_ = stack[3].m_obj;
lean_object* v___y_3143_ = stack[4].m_obj;
lean_object* v___y_3144_ = stack[5].m_obj;
lean_object* v___y_3145_ = stack[6].m_obj;
lean_object* v___y_3146_ = stack[7].m_obj;
lean_object* v___y_3147_ = stack[8].m_obj;
lean_object* v_res_3160_;
v_res_3160_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3139_, v_declHint_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
stack->m_obj
 = v_res_3160_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11___boxed(lean_object* v_msg_3161_, lean_object* v_declHint_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3161_, v_declHint_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
return v_res_3171_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object* v_ref_3172_, lean_object* v_msg_3173_, lean_object* v_declHint_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; lean_object* v_a_3184_; lean_object* v___x_3185_; 
v___x_3183_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11(v_msg_3173_, v_declHint_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref(v___x_3183_);
v___x_3185_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_3172_, v_a_3184_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3185_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3172_ = stack[0].m_obj;
lean_object* v_msg_3173_ = stack[1].m_obj;
lean_object* v_declHint_3174_ = stack[2].m_obj;
lean_object* v___y_3175_ = stack[3].m_obj;
lean_object* v___y_3176_ = stack[4].m_obj;
lean_object* v___y_3177_ = stack[5].m_obj;
lean_object* v___y_3178_ = stack[6].m_obj;
lean_object* v___y_3179_ = stack[7].m_obj;
lean_object* v___y_3180_ = stack[8].m_obj;
lean_object* v___y_3181_ = stack[9].m_obj;
lean_object* v_res_3186_;
v_res_3186_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3172_, v_msg_3173_, v_declHint_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
stack->m_obj
 = v_res_3186_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_ref_3187_, lean_object* v_msg_3188_, lean_object* v_declHint_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3187_, v_msg_3188_, v_declHint_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec(v_ref_3187_);
return v_res_3198_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(lean_object* v_ref_3199_, lean_object* v_constName_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v___x_3209_; uint8_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3209_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3210_ = 0;
lean_inc(v_constName_3200_);
v___x_3211_ = l_Lean_MessageData_ofConstName(v_constName_3200_, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3209_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3212_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_3199_, v___x_3214_, v_constName_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
return v___x_3215_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3199_ = stack[0].m_obj;
lean_object* v_constName_3200_ = stack[1].m_obj;
lean_object* v___y_3201_ = stack[2].m_obj;
lean_object* v___y_3202_ = stack[3].m_obj;
lean_object* v___y_3203_ = stack[4].m_obj;
lean_object* v___y_3204_ = stack[5].m_obj;
lean_object* v___y_3205_ = stack[6].m_obj;
lean_object* v___y_3206_ = stack[7].m_obj;
lean_object* v___y_3207_ = stack[8].m_obj;
lean_object* v_res_3216_;
v_res_3216_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3199_, v_constName_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
stack->m_obj
 = v_res_3216_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_ref_3217_, lean_object* v_constName_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3217_, v_constName_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec(v_ref_3217_);
return v_res_3227_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_ref_3237_; lean_object* v___x_3238_; 
v_ref_3237_ = lean_ctor_get(v___y_3234_, 2);
v___x_3238_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_3237_, v_constName_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3238_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3228_ = stack[0].m_obj;
lean_object* v___y_3229_ = stack[1].m_obj;
lean_object* v___y_3230_ = stack[2].m_obj;
lean_object* v___y_3231_ = stack[3].m_obj;
lean_object* v___y_3232_ = stack[4].m_obj;
lean_object* v___y_3233_ = stack[5].m_obj;
lean_object* v___y_3234_ = stack[6].m_obj;
lean_object* v___y_3235_ = stack[7].m_obj;
lean_object* v_res_3239_;
v_res_3239_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
stack->m_obj
 = v_res_3239_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
return v_res_3249_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(lean_object* v_constName_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; lean_object* v_env_3260_; uint8_t v___x_3261_; lean_object* v___x_3262_; 
v___x_3259_ = lean_st_ref_get(v___y_3257_);
v_env_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc_ref(v_env_3260_);
lean_dec(v___x_3259_);
v___x_3261_ = 0;
lean_inc(v_constName_3250_);
v___x_3262_ = l_Lean_Environment_find_x3f(v_env_3260_, v_constName_3250_, v___x_3261_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
return v___x_3263_;
}
else
{
lean_object* v_val_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec(v_constName_3250_);
v_val_3264_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3262_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_val_3264_);
lean_dec(v___x_3262_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
lean_ctor_set_tag(v___x_3266_, 0);
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_val_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3250_ = stack[0].m_obj;
lean_object* v___y_3251_ = stack[1].m_obj;
lean_object* v___y_3252_ = stack[2].m_obj;
lean_object* v___y_3253_ = stack[3].m_obj;
lean_object* v___y_3254_ = stack[4].m_obj;
lean_object* v___y_3255_ = stack[5].m_obj;
lean_object* v___y_3256_ = stack[6].m_obj;
lean_object* v___y_3257_ = stack[7].m_obj;
lean_object* v_res_3272_;
v_res_3272_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_constName_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
stack->m_obj
 = v_res_3272_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0___boxed(lean_object* v_constName_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_constName_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
return v_res_3282_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_instMonadEIO___redArg();
return v___x_3283_;
}
}
lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(lean_object* v_msg_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v_toApplicative_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3363_; 
v___x_3297_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__0);
v___x_3298_ = l_StateRefT_x27_instMonad___redArg(v___x_3297_);
v_toApplicative_3299_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3363_ == 0)
{
lean_object* v_unused_3364_; 
v_unused_3364_ = lean_ctor_get(v___x_3298_, 1);
lean_dec(v_unused_3364_);
v___x_3301_ = v___x_3298_;
v_isShared_3302_ = v_isSharedCheck_3363_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_toApplicative_3299_);
lean_dec(v___x_3298_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3363_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v_toFunctor_3303_; lean_object* v_toSeq_3304_; lean_object* v_toSeqLeft_3305_; lean_object* v_toSeqRight_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3361_; 
v_toFunctor_3303_ = lean_ctor_get(v_toApplicative_3299_, 0);
v_toSeq_3304_ = lean_ctor_get(v_toApplicative_3299_, 2);
v_toSeqLeft_3305_ = lean_ctor_get(v_toApplicative_3299_, 3);
v_toSeqRight_3306_ = lean_ctor_get(v_toApplicative_3299_, 4);
v_isSharedCheck_3361_ = !lean_is_exclusive(v_toApplicative_3299_);
if (v_isSharedCheck_3361_ == 0)
{
lean_object* v_unused_3362_; 
v_unused_3362_ = lean_ctor_get(v_toApplicative_3299_, 1);
lean_dec(v_unused_3362_);
v___x_3308_ = v_toApplicative_3299_;
v_isShared_3309_ = v_isSharedCheck_3361_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_toSeqRight_3306_);
lean_inc(v_toSeqLeft_3305_);
lean_inc(v_toSeq_3304_);
lean_inc(v_toFunctor_3303_);
lean_dec(v_toApplicative_3299_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3361_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___f_3310_; lean_object* v___f_3311_; lean_object* v___f_3312_; lean_object* v___f_3313_; lean_object* v___x_3314_; lean_object* v___f_3315_; lean_object* v___f_3316_; lean_object* v___f_3317_; lean_object* v___x_3319_; 
v___f_3310_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__1));
v___f_3311_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3303_);
v___f_3312_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3312_, 0, v_toFunctor_3303_);
v___f_3313_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3313_, 0, v_toFunctor_3303_);
v___x_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___f_3312_);
lean_ctor_set(v___x_3314_, 1, v___f_3313_);
v___f_3315_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3315_, 0, v_toSeqRight_3306_);
v___f_3316_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3316_, 0, v_toSeqLeft_3305_);
v___f_3317_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3317_, 0, v_toSeq_3304_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v___f_3315_);
lean_ctor_set(v___x_3308_, 3, v___f_3316_);
lean_ctor_set(v___x_3308_, 2, v___f_3317_);
lean_ctor_set(v___x_3308_, 1, v___f_3310_);
lean_ctor_set(v___x_3308_, 0, v___x_3314_);
v___x_3319_ = v___x_3308_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3314_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___f_3310_);
lean_ctor_set(v_reuseFailAlloc_3360_, 2, v___f_3317_);
lean_ctor_set(v_reuseFailAlloc_3360_, 3, v___f_3316_);
lean_ctor_set(v_reuseFailAlloc_3360_, 4, v___f_3315_);
v___x_3319_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3321_; 
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 1, v___f_3311_);
lean_ctor_set(v___x_3301_, 0, v___x_3319_);
v___x_3321_ = v___x_3301_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3319_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v___f_3311_);
v___x_3321_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
lean_object* v___x_3322_; lean_object* v_toApplicative_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3357_; 
v___x_3322_ = l_StateRefT_x27_instMonad___redArg(v___x_3321_);
v_toApplicative_3323_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; 
v_unused_3358_ = lean_ctor_get(v___x_3322_, 1);
lean_dec(v_unused_3358_);
v___x_3325_ = v___x_3322_;
v_isShared_3326_ = v_isSharedCheck_3357_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_toApplicative_3323_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3357_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v_toFunctor_3327_; lean_object* v_toSeq_3328_; lean_object* v_toSeqLeft_3329_; lean_object* v_toSeqRight_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3355_; 
v_toFunctor_3327_ = lean_ctor_get(v_toApplicative_3323_, 0);
v_toSeq_3328_ = lean_ctor_get(v_toApplicative_3323_, 2);
v_toSeqLeft_3329_ = lean_ctor_get(v_toApplicative_3323_, 3);
v_toSeqRight_3330_ = lean_ctor_get(v_toApplicative_3323_, 4);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_toApplicative_3323_);
if (v_isSharedCheck_3355_ == 0)
{
lean_object* v_unused_3356_; 
v_unused_3356_ = lean_ctor_get(v_toApplicative_3323_, 1);
lean_dec(v_unused_3356_);
v___x_3332_ = v_toApplicative_3323_;
v_isShared_3333_ = v_isSharedCheck_3355_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_toSeqRight_3330_);
lean_inc(v_toSeqLeft_3329_);
lean_inc(v_toSeq_3328_);
lean_inc(v_toFunctor_3327_);
lean_dec(v_toApplicative_3323_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3355_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___f_3334_; lean_object* v___f_3335_; lean_object* v___f_3336_; lean_object* v___f_3337_; lean_object* v___x_3338_; lean_object* v___f_3339_; lean_object* v___f_3340_; lean_object* v___f_3341_; lean_object* v___x_3343_; 
v___f_3334_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__3));
v___f_3335_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3327_);
v___f_3336_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3336_, 0, v_toFunctor_3327_);
v___f_3337_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3337_, 0, v_toFunctor_3327_);
v___x_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___f_3336_);
lean_ctor_set(v___x_3338_, 1, v___f_3337_);
v___f_3339_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3339_, 0, v_toSeqRight_3330_);
v___f_3340_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3340_, 0, v_toSeqLeft_3329_);
v___f_3341_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3341_, 0, v_toSeq_3328_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___f_3339_);
lean_ctor_set(v___x_3332_, 3, v___f_3340_);
lean_ctor_set(v___x_3332_, 2, v___f_3341_);
lean_ctor_set(v___x_3332_, 1, v___f_3334_);
lean_ctor_set(v___x_3332_, 0, v___x_3338_);
v___x_3343_ = v___x_3332_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v___f_3334_);
lean_ctor_set(v_reuseFailAlloc_3354_, 2, v___f_3341_);
lean_ctor_set(v_reuseFailAlloc_3354_, 3, v___f_3340_);
lean_ctor_set(v_reuseFailAlloc_3354_, 4, v___f_3339_);
v___x_3343_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3345_; 
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 1, v___f_3335_);
lean_ctor_set(v___x_3325_, 0, v___x_3343_);
v___x_3345_ = v___x_3325_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v___f_3335_);
v___x_3345_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_36468__overap_3351_; lean_object* v___x_3352_; 
v___x_3346_ = l_StateRefT_x27_instMonad___redArg(v___x_3345_);
v___x_3347_ = l_ReaderT_instMonad___redArg(v___x_3346_);
v___x_3348_ = l_ReaderT_instMonad___redArg(v___x_3347_);
v___x_3349_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3350_ = l_instInhabitedOfMonad___redArg(v___x_3348_, v___x_3349_);
v___x_36468__overap_3351_ = lean_panic_fn_borrowed(v___x_3350_, v_msg_3288_);
lean_dec(v___x_3350_);
lean_inc(v___y_3295_);
lean_inc_ref(v___y_3294_);
lean_inc(v___y_3293_);
lean_inc_ref(v___y_3292_);
lean_inc(v___y_3291_);
lean_inc_ref(v___y_3290_);
lean_inc(v___y_3289_);
v___x_3352_ = lean_apply_8(v___x_36468__overap_3351_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, lean_box(0));
return v___x_3352_;
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
LEAN_EXPORT void l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3288_ = stack[0].m_obj;
lean_object* v___y_3289_ = stack[1].m_obj;
lean_object* v___y_3290_ = stack[2].m_obj;
lean_object* v___y_3291_ = stack[3].m_obj;
lean_object* v___y_3292_ = stack[4].m_obj;
lean_object* v___y_3293_ = stack[5].m_obj;
lean_object* v___y_3294_ = stack[6].m_obj;
lean_object* v___y_3295_ = stack[7].m_obj;
lean_object* v_res_3365_;
v_res_3365_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v_msg_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
stack->m_obj
 = v_res_3365_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1___boxed(lean_object* v_msg_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v_msg_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
return v_res_3375_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__2));
v___x_3380_ = lean_unsigned_to_nat(53u);
v___x_3381_ = lean_unsigned_to_nat(62u);
v___x_3382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__1));
v___x_3383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__0));
v___x_3384_ = l_mkPanicMessageWithDecl(v___x_3383_, v___x_3382_, v___x_3381_, v___x_3380_, v___x_3379_);
return v___x_3384_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(size_t v_sz_3385_, size_t v_i_3386_, lean_object* v_bs_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_usize_dec_lt(v_i_3386_, v_sz_3385_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3397_, 0, v_bs_3387_);
return v___x_3397_;
}
else
{
lean_object* v_v_3398_; lean_object* v___x_3399_; lean_object* v_bs_x27_3400_; lean_object* v_a_3402_; lean_object* v___x_3407_; 
v_v_3398_ = lean_array_uget(v_bs_3387_, v_i_3386_);
v___x_3399_ = lean_unsigned_to_nat(0u);
v_bs_x27_3400_ = lean_array_uset(v_bs_3387_, v_i_3386_, v___x_3399_);
v___x_3407_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_v_3398_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
if (lean_obj_tag(v_a_3408_) == 6)
{
lean_object* v_val_3409_; lean_object* v_numFields_3410_; uint8_t v___x_3411_; lean_object* v___x_3412_; 
v_val_3409_ = lean_ctor_get(v_a_3408_, 0);
lean_inc_ref(v_val_3409_);
lean_dec_ref_known(v_a_3408_, 1);
v_numFields_3410_ = lean_ctor_get(v_val_3409_, 4);
lean_inc(v_numFields_3410_);
lean_dec_ref(v_val_3409_);
v___x_3411_ = 0;
v___x_3412_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3412_, 0, v_numFields_3410_);
lean_ctor_set(v___x_3412_, 1, v___x_3399_);
lean_ctor_set_uint8(v___x_3412_, sizeof(void*)*2, v___x_3411_);
v_a_3402_ = v___x_3412_;
goto v___jp_3401_;
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec(v_a_3408_);
v___x_3413_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___closed__3);
v___x_3414_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__1(v___x_3413_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
v_a_3402_ = v_a_3415_;
goto v___jp_3401_;
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref(v_bs_x27_3400_);
v_a_3416_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3414_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3414_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_bs_x27_3400_);
v_a_3424_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3407_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3407_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
v___jp_3401_:
{
size_t v___x_3403_; size_t v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = ((size_t)1ULL);
v___x_3404_ = lean_usize_add(v_i_3386_, v___x_3403_);
v___x_3405_ = lean_array_uset(v_bs_x27_3400_, v_i_3386_, v_a_3402_);
v_i_3386_ = v___x_3404_;
v_bs_3387_ = v___x_3405_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3385_ = stack[0].m_num;
size_t v_i_3386_ = stack[1].m_num;
lean_object* v_bs_3387_ = stack[2].m_obj;
lean_object* v___y_3388_ = stack[3].m_obj;
lean_object* v___y_3389_ = stack[4].m_obj;
lean_object* v___y_3390_ = stack[5].m_obj;
lean_object* v___y_3391_ = stack[6].m_obj;
lean_object* v___y_3392_ = stack[7].m_obj;
lean_object* v___y_3393_ = stack[8].m_obj;
lean_object* v___y_3394_ = stack[9].m_obj;
lean_object* v_res_3432_;
v_res_3432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_3385_, v_i_3386_, v_bs_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
stack->m_obj
 = v_res_3432_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3___boxed(lean_object* v_sz_3433_, lean_object* v_i_3434_, lean_object* v_bs_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
size_t v_sz_boxed_3444_; size_t v_i_boxed_3445_; lean_object* v_res_3446_; 
v_sz_boxed_3444_ = lean_unbox_usize(v_sz_3433_);
lean_dec(v_sz_3433_);
v_i_boxed_3445_ = lean_unbox_usize(v_i_3434_);
lean_dec(v_i_3434_);
v_res_3446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_boxed_3444_, v_i_boxed_3445_, v_bs_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
return v_res_3446_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = lean_box(0);
v___x_3448_ = lean_unsigned_to_nat(16u);
v___x_3449_ = lean_mk_array(v___x_3448_, v___x_3447_);
return v___x_3449_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__0);
v___x_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_ctor_set(v___x_3452_, 1, v___x_3450_);
return v___x_3452_;
}
}
lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(lean_object* v_e_3455_, uint8_t v_alsoCasesOn_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
uint8_t v___x_3468_; 
v___x_3468_ = l_Lean_Expr_isApp(v_e_3455_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_dec_ref(v_e_3455_);
v___x_3469_ = lean_box(0);
v___x_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_Expr_getAppFn(v_e_3455_);
if (lean_obj_tag(v___x_3471_) == 4)
{
lean_object* v_declName_3472_; lean_object* v_us_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3628_; 
v_declName_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc_n(v_declName_3472_, 2);
v_us_3473_ = lean_ctor_get(v___x_3471_, 1);
lean_inc(v_us_3473_);
lean_dec_ref_known(v___x_3471_, 2);
v___x_3474_ = l_Lean_instInhabitedExpr;
v___x_3475_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3472_, v___y_3463_);
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3478_ = v___x_3475_;
v_isShared_3479_ = v_isSharedCheck_3628_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3475_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3628_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
if (lean_obj_tag(v_a_3476_) == 1)
{
lean_object* v_val_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3521_; 
v_val_3480_ = lean_ctor_get(v_a_3476_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_a_3476_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3482_ = v_a_3476_;
v_isShared_3483_ = v_isSharedCheck_3521_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_val_3480_);
lean_dec(v_a_3476_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3521_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v_dummy_3484_; lean_object* v_nargs_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v_args_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v_dummy_3484_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
v_nargs_3485_ = l_Lean_Expr_getAppNumArgs(v_e_3455_);
lean_inc(v_nargs_3485_);
v___x_3486_ = lean_mk_array(v_nargs_3485_, v_dummy_3484_);
v___x_3487_ = lean_unsigned_to_nat(1u);
v___x_3488_ = lean_nat_sub(v_nargs_3485_, v___x_3487_);
lean_dec(v_nargs_3485_);
v_args_3489_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3455_, v___x_3486_, v___x_3488_);
v___x_3490_ = lean_array_get_size(v_args_3489_);
v___x_3491_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_3480_);
v___x_3492_ = lean_nat_dec_lt(v___x_3490_, v___x_3491_);
lean_dec(v___x_3491_);
if (v___x_3492_ == 0)
{
lean_object* v_numParams_3493_; lean_object* v_numDiscrs_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3512_; 
v_numParams_3493_ = lean_ctor_get(v_val_3480_, 0);
v_numDiscrs_3494_ = lean_ctor_get(v_val_3480_, 1);
v___x_3495_ = lean_array_mk(v_us_3473_);
v___x_3496_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3493_);
v___x_3497_ = l_Array_extract___redArg(v_args_3489_, v___x_3496_, v_numParams_3493_);
v___x_3498_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3480_);
v___x_3499_ = lean_array_get(v___x_3474_, v_args_3489_, v___x_3498_);
lean_dec(v___x_3498_);
v___x_3500_ = lean_nat_add(v_numParams_3493_, v___x_3487_);
v___x_3501_ = lean_nat_add(v___x_3500_, v_numDiscrs_3494_);
lean_inc(v___x_3501_);
lean_inc_ref_n(v_args_3489_, 2);
v___x_3502_ = l_Array_toSubarray___redArg(v_args_3489_, v___x_3500_, v___x_3501_);
v___x_3503_ = l_Subarray_copy___redArg(v___x_3502_);
v___x_3504_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3480_);
v___x_3505_ = lean_nat_add(v___x_3501_, v___x_3504_);
lean_dec(v___x_3504_);
lean_inc(v___x_3505_);
v___x_3506_ = l_Array_toSubarray___redArg(v_args_3489_, v___x_3501_, v___x_3505_);
v___x_3507_ = l_Subarray_copy___redArg(v___x_3506_);
v___x_3508_ = l_Array_toSubarray___redArg(v_args_3489_, v___x_3505_, v___x_3490_);
v___x_3509_ = l_Subarray_copy___redArg(v___x_3508_);
v___x_3510_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3510_, 0, v_val_3480_);
lean_ctor_set(v___x_3510_, 1, v_declName_3472_);
lean_ctor_set(v___x_3510_, 2, v___x_3495_);
lean_ctor_set(v___x_3510_, 3, v___x_3497_);
lean_ctor_set(v___x_3510_, 4, v___x_3499_);
lean_ctor_set(v___x_3510_, 5, v___x_3503_);
lean_ctor_set(v___x_3510_, 6, v___x_3507_);
lean_ctor_set(v___x_3510_, 7, v___x_3509_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v___x_3510_);
v___x_3512_ = v___x_3482_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3514_; 
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3512_);
v___x_3514_ = v___x_3478_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
lean_dec_ref(v_args_3489_);
lean_del_object(v___x_3482_);
lean_dec(v_val_3480_);
lean_dec(v_us_3473_);
lean_dec(v_declName_3472_);
v___x_3517_ = lean_box(0);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3517_);
v___x_3519_ = v___x_3478_;
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
lean_object* v___x_3522_; 
lean_del_object(v___x_3478_);
lean_dec(v_a_3476_);
v___x_3522_ = lean_st_ref_get(v___y_3463_);
if (v_alsoCasesOn_3456_ == 0)
{
lean_dec(v___x_3522_);
lean_dec(v_us_3473_);
lean_dec(v_declName_3472_);
lean_dec_ref(v_e_3455_);
goto v___jp_3465_;
}
else
{
lean_object* v_env_3523_; uint8_t v___x_3524_; 
v_env_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc_ref(v_env_3523_);
lean_dec(v___x_3522_);
lean_inc(v_declName_3472_);
v___x_3524_ = l_Lean_isCasesOnRecursor(v_env_3523_, v_declName_3472_);
if (v___x_3524_ == 0)
{
lean_dec(v_us_3473_);
lean_dec(v_declName_3472_);
lean_dec_ref(v_e_3455_);
goto v___jp_3465_;
}
else
{
lean_object* v_indName_3525_; lean_object* v___x_3526_; 
v_indName_3525_ = l_Lean_Name_getPrefix(v_declName_3472_);
v___x_3526_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0(v_indName_3525_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3619_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3619_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3619_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
if (lean_obj_tag(v_a_3527_) == 5)
{
lean_object* v_val_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3614_; 
v_val_3531_ = lean_ctor_get(v_a_3527_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v_a_3527_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3533_ = v_a_3527_;
v_isShared_3534_ = v_isSharedCheck_3614_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_val_3531_);
lean_dec(v_a_3527_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3614_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v_toConstantVal_3535_; lean_object* v_numParams_3536_; lean_object* v_numIndices_3537_; lean_object* v_ctors_3538_; lean_object* v_nargs_3539_; lean_object* v_dummy_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v_args_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v_toConstantVal_3535_ = lean_ctor_get(v_val_3531_, 0);
lean_inc_ref(v_toConstantVal_3535_);
v_numParams_3536_ = lean_ctor_get(v_val_3531_, 1);
lean_inc(v_numParams_3536_);
v_numIndices_3537_ = lean_ctor_get(v_val_3531_, 2);
lean_inc(v_numIndices_3537_);
v_ctors_3538_ = lean_ctor_get(v_val_3531_, 4);
lean_inc(v_ctors_3538_);
v_nargs_3539_ = l_Lean_Expr_getAppNumArgs(v_e_3455_);
v_dummy_3540_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
lean_inc(v_nargs_3539_);
v___x_3541_ = lean_mk_array(v_nargs_3539_, v_dummy_3540_);
v___x_3542_ = lean_unsigned_to_nat(1u);
v___x_3543_ = lean_nat_sub(v_nargs_3539_, v___x_3542_);
lean_dec(v_nargs_3539_);
v_args_3544_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3455_, v___x_3541_, v___x_3543_);
v___x_3545_ = lean_nat_add(v_numParams_3536_, v___x_3542_);
v___x_3546_ = lean_nat_add(v___x_3545_, v_numIndices_3537_);
v___x_3547_ = lean_nat_add(v___x_3546_, v___x_3542_);
lean_dec(v___x_3546_);
v___x_3548_ = l_Lean_InductiveVal_numCtors(v_val_3531_);
lean_dec_ref(v_val_3531_);
v___x_3549_ = lean_nat_add(v___x_3547_, v___x_3548_);
lean_dec(v___x_3548_);
v___x_3550_ = lean_array_get_size(v_args_3544_);
v___x_3551_ = lean_nat_dec_le(v___x_3549_, v___x_3550_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; lean_object* v___x_3554_; 
lean_dec(v___x_3549_);
lean_dec(v___x_3547_);
lean_dec(v___x_3545_);
lean_dec_ref(v_args_3544_);
lean_dec(v_ctors_3538_);
lean_dec(v_numIndices_3537_);
lean_dec(v_numParams_3536_);
lean_dec_ref(v_toConstantVal_3535_);
lean_del_object(v___x_3533_);
lean_dec(v_us_3473_);
lean_dec(v_declName_3472_);
v___x_3552_ = lean_box(0);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3552_);
v___x_3554_ = v___x_3529_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
else
{
lean_object* v___x_3556_; lean_object* v_params_3557_; lean_object* v_motive_3558_; lean_object* v_discrs_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v_discrInfos_3562_; lean_object* v_alts_3563_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v_lower_3605_; lean_object* v_upper_3606_; uint8_t v___x_3613_; 
lean_del_object(v___x_3529_);
v___x_3556_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3536_);
lean_inc_ref_n(v_args_3544_, 3);
v_params_3557_ = l_Array_toSubarray___redArg(v_args_3544_, v___x_3556_, v_numParams_3536_);
v_motive_3558_ = lean_array_get(v___x_3474_, v_args_3544_, v_numParams_3536_);
lean_dec(v_numParams_3536_);
lean_inc(v___x_3547_);
v_discrs_3559_ = l_Array_toSubarray___redArg(v_args_3544_, v___x_3545_, v___x_3547_);
v___x_3560_ = lean_nat_add(v_numIndices_3537_, v___x_3542_);
lean_dec(v_numIndices_3537_);
v___x_3561_ = lean_box(0);
v_discrInfos_3562_ = lean_mk_array(v___x_3560_, v___x_3561_);
lean_inc(v___x_3549_);
v_alts_3563_ = l_Array_toSubarray___redArg(v_args_3544_, v___x_3547_, v___x_3549_);
v___x_3613_ = lean_nat_dec_le(v___x_3549_, v___x_3556_);
if (v___x_3613_ == 0)
{
v_lower_3605_ = v___x_3549_;
v_upper_3606_ = v___x_3550_;
goto v___jp_3604_;
}
else
{
lean_dec(v___x_3549_);
v_lower_3605_ = v___x_3556_;
v_upper_3606_ = v___x_3550_;
goto v___jp_3604_;
}
v___jp_3564_:
{
lean_object* v___x_3567_; size_t v_sz_3568_; size_t v___x_3569_; lean_object* v___x_3570_; 
v___x_3567_ = lean_array_mk(v_ctors_3538_);
v_sz_3568_ = lean_array_size(v___x_3567_);
v___x_3569_ = ((size_t)0ULL);
v___x_3570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__3(v_sz_3568_, v___x_3569_, v___x_3567_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3595_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3573_ = v___x_3570_;
v_isShared_3574_ = v_isSharedCheck_3595_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3595_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v_start_3575_; lean_object* v_stop_3576_; lean_object* v_start_3577_; lean_object* v_stop_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3590_; 
v_start_3575_ = lean_ctor_get(v_params_3557_, 1);
v_stop_3576_ = lean_ctor_get(v_params_3557_, 2);
v_start_3577_ = lean_ctor_get(v_discrs_3559_, 1);
v_stop_3578_ = lean_ctor_get(v_discrs_3559_, 2);
v___x_3579_ = lean_nat_sub(v_stop_3576_, v_start_3575_);
v___x_3580_ = lean_nat_sub(v_stop_3578_, v_start_3577_);
v___x_3581_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__1);
v___x_3582_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3579_);
lean_ctor_set(v___x_3582_, 1, v___x_3580_);
lean_ctor_set(v___x_3582_, 2, v_a_3571_);
lean_ctor_set(v___x_3582_, 3, v___y_3566_);
lean_ctor_set(v___x_3582_, 4, v_discrInfos_3562_);
lean_ctor_set(v___x_3582_, 5, v___x_3581_);
v___x_3583_ = lean_array_mk(v_us_3473_);
v___x_3584_ = l_Subarray_copy___redArg(v_params_3557_);
v___x_3585_ = l_Subarray_copy___redArg(v_discrs_3559_);
v___x_3586_ = l_Subarray_copy___redArg(v_alts_3563_);
v___x_3587_ = l_Subarray_copy___redArg(v___y_3565_);
v___x_3588_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3582_);
lean_ctor_set(v___x_3588_, 1, v_declName_3472_);
lean_ctor_set(v___x_3588_, 2, v___x_3583_);
lean_ctor_set(v___x_3588_, 3, v___x_3584_);
lean_ctor_set(v___x_3588_, 4, v_motive_3558_);
lean_ctor_set(v___x_3588_, 5, v___x_3585_);
lean_ctor_set(v___x_3588_, 6, v___x_3586_);
lean_ctor_set(v___x_3588_, 7, v___x_3587_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set_tag(v___x_3533_, 1);
lean_ctor_set(v___x_3533_, 0, v___x_3588_);
v___x_3590_ = v___x_3533_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3592_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3590_);
v___x_3592_ = v___x_3573_;
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
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec_ref(v_alts_3563_);
lean_dec_ref(v_discrInfos_3562_);
lean_dec_ref(v_discrs_3559_);
lean_dec(v_motive_3558_);
lean_dec_ref(v_params_3557_);
lean_del_object(v___x_3533_);
lean_dec(v_us_3473_);
lean_dec(v_declName_3472_);
v_a_3596_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3570_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3570_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
v___jp_3604_:
{
lean_object* v_levelParams_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
v_levelParams_3607_ = lean_ctor_get(v_toConstantVal_3535_, 1);
lean_inc(v_levelParams_3607_);
lean_dec_ref(v_toConstantVal_3535_);
v___x_3608_ = l_Array_toSubarray___redArg(v_args_3544_, v_lower_3605_, v_upper_3606_);
v___x_3609_ = l_List_lengthTR___redArg(v_levelParams_3607_);
lean_dec(v_levelParams_3607_);
v___x_3610_ = l_List_lengthTR___redArg(v_us_3473_);
v___x_3611_ = lean_nat_dec_eq(v___x_3609_, v___x_3610_);
lean_dec(v___x_3610_);
lean_dec(v___x_3609_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; 
v___x_3612_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___closed__2));
v___y_3565_ = v___x_3608_;
v___y_3566_ = v___x_3612_;
goto v___jp_3564_;
}
else
{
v___y_3565_ = v___x_3608_;
v___y_3566_ = v___x_3561_;
goto v___jp_3564_;
}
}
}
}
}
else
{
lean_object* v___x_3615_; lean_object* v___x_3617_; 
lean_dec(v_a_3527_);
lean_dec(v_us_3473_);
lean_dec(v_declName_3472_);
lean_dec_ref(v_e_3455_);
v___x_3615_ = lean_box(0);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3615_);
v___x_3617_ = v___x_3529_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3615_);
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
lean_dec(v_us_3473_);
lean_dec(v_declName_3472_);
lean_dec_ref(v_e_3455_);
v_a_3620_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3526_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3526_);
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
}
}
}
else
{
lean_dec_ref(v___x_3471_);
lean_dec_ref(v_e_3455_);
goto v___jp_3465_;
}
}
v___jp_3465_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = lean_box(0);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
return v___x_3467_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3455_ = stack[0].m_obj;
uint8_t v_alsoCasesOn_3456_ = stack[1].m_num;
lean_object* v___y_3457_ = stack[2].m_obj;
lean_object* v___y_3458_ = stack[3].m_obj;
lean_object* v___y_3459_ = stack[4].m_obj;
lean_object* v___y_3460_ = stack[5].m_obj;
lean_object* v___y_3461_ = stack[6].m_obj;
lean_object* v___y_3462_ = stack[7].m_obj;
lean_object* v___y_3463_ = stack[8].m_obj;
lean_object* v_res_3629_;
v_res_3629_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3455_, v_alsoCasesOn_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
stack->m_obj
 = v_res_3629_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0___boxed(lean_object* v_e_3630_, lean_object* v_alsoCasesOn_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
uint8_t v_alsoCasesOn_boxed_3640_; lean_object* v_res_3641_; 
v_alsoCasesOn_boxed_3640_ = lean_unbox(v_alsoCasesOn_3631_);
v_res_3641_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3630_, v_alsoCasesOn_boxed_3640_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
return v_res_3641_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__1));
v___x_3646_ = l_Lean_stringToMessageData(v___x_3645_);
return v___x_3646_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = lean_unsigned_to_nat(1u);
v___x_3648_ = l_Lean_Expr_bvar___override(v___x_3647_);
return v___x_3648_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3651_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__5));
v___x_3652_ = lean_unsigned_to_nat(2u);
v___x_3653_ = lean_unsigned_to_nat(182u);
v___x_3654_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__4));
v___x_3655_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2));
v___x_3656_ = l_mkPanicMessageWithDecl(v___x_3655_, v___x_3654_, v___x_3653_, v___x_3652_, v___x_3651_);
return v___x_3656_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(lean_object* v_e_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_){
_start:
{
lean_object* v_e_3666_; uint8_t v___x_3667_; lean_object* v___x_3668_; 
v_e_3666_ = l_Lean_Expr_headBeta(v_e_3657_);
v___x_3667_ = 1;
v___x_3668_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0(v_e_3666_, v___x_3667_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3918_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3918_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3918_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
if (lean_obj_tag(v_a_3669_) == 1)
{
lean_object* v_val_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3913_; 
v_val_3673_ = lean_ctor_get(v_a_3669_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_a_3669_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3675_ = v_a_3669_;
v_isShared_3676_ = v_isSharedCheck_3913_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_val_3673_);
lean_dec(v_a_3669_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3913_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v_toMatcherInfo_3677_; lean_object* v_matcherName_3678_; lean_object* v_params_3679_; lean_object* v_motive_3680_; lean_object* v_discrs_3681_; lean_object* v_alts_3682_; lean_object* v_remaining_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
v_toMatcherInfo_3677_ = lean_ctor_get(v_val_3673_, 0);
lean_inc_ref(v_toMatcherInfo_3677_);
v_matcherName_3678_ = lean_ctor_get(v_val_3673_, 1);
lean_inc(v_matcherName_3678_);
v_params_3679_ = lean_ctor_get(v_val_3673_, 3);
lean_inc_ref(v_params_3679_);
v_motive_3680_ = lean_ctor_get(v_val_3673_, 4);
lean_inc_ref(v_motive_3680_);
v_discrs_3681_ = lean_ctor_get(v_val_3673_, 5);
lean_inc_ref(v_discrs_3681_);
v_alts_3682_ = lean_ctor_get(v_val_3673_, 6);
lean_inc_ref(v_alts_3682_);
v_remaining_3683_ = lean_ctor_get(v_val_3673_, 7);
lean_inc_ref(v_remaining_3683_);
v___x_3684_ = lean_unsigned_to_nat(0u);
v___x_3685_ = lean_array_get_size(v_remaining_3683_);
v___x_3686_ = lean_nat_dec_lt(v___x_3684_, v___x_3685_);
if (v___x_3686_ == 0)
{
lean_object* v___x_3687_; lean_object* v___x_3689_; 
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
lean_dec(v_val_3673_);
v___x_3687_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3687_);
v___x_3689_ = v___x_3671_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
else
{
lean_object* v___x_3691_; uint8_t v___x_3692_; 
v___x_3691_ = lean_array_fget_borrowed(v_remaining_3683_, v___x_3684_);
v___x_3692_ = l_Lean_Expr_isLambda(v___x_3691_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3693_; lean_object* v___x_3695_; 
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
lean_dec(v_val_3673_);
v___x_3693_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3693_);
v___x_3695_ = v___x_3671_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3693_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
else
{
lean_object* v___x_3697_; uint8_t v___x_3698_; 
v___x_3697_ = l_Lean_Expr_bindingBody_x21(v___x_3691_);
v___x_3698_ = l_Lean_Expr_isLambda(v___x_3697_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; lean_object* v___x_3701_; 
lean_dec_ref(v___x_3697_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
lean_dec(v_val_3673_);
v___x_3699_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3699_);
v___x_3701_ = v___x_3671_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
else
{
lean_object* v___x_3703_; uint8_t v___x_3704_; 
v___x_3703_ = l_Lean_Expr_bindingBody_x21(v___x_3697_);
lean_dec_ref(v___x_3697_);
v___x_3704_ = l_Lean_Expr_isApp(v___x_3703_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; lean_object* v___x_3707_; 
lean_dec_ref(v___x_3703_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
lean_dec(v_val_3673_);
v___x_3705_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3705_);
v___x_3707_ = v___x_3671_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
else
{
uint8_t v___x_3709_; 
v___x_3709_ = lean_expr_has_loose_bvar(v___x_3703_, v___x_3684_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___y_3713_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3710_ = l_Lean_Expr_appArg_x21(v___x_3703_);
v___x_3711_ = lean_unsigned_to_nat(1u);
v___x_3776_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__3);
v___x_3777_ = lean_expr_eqv(v___x_3710_, v___x_3776_);
lean_dec_ref(v___x_3710_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; lean_object* v___x_3780_; 
lean_dec_ref(v___x_3703_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
lean_dec(v_val_3673_);
v___x_3778_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3778_);
v___x_3780_ = v___x_3671_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
else
{
lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3782_ = l_Lean_Expr_appFn_x21(v___x_3703_);
lean_dec_ref(v___x_3703_);
v___x_3783_ = lean_expr_has_loose_bvar(v___x_3782_, v___x_3711_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; 
lean_del_object(v___x_3671_);
lean_inc(v_a_3664_);
lean_inc_ref(v_a_3663_);
lean_inc(v_a_3662_);
lean_inc_ref(v_a_3661_);
lean_inc_ref(v___x_3782_);
v___x_3784_ = lean_infer_type(v___x_3782_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3786_; uint8_t v_transparency_3787_; uint8_t v___x_3788_; lean_object* v___y_3790_; uint8_t v___x_3881_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
v___x_3786_ = l_Lean_Meta_Context_config(v_a_3661_);
v_transparency_3787_ = lean_ctor_get_uint8(v___x_3786_, 9);
v___x_3788_ = 0;
v___x_3881_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3787_, v___x_3788_);
if (v___x_3881_ == 0)
{
lean_object* v_keyedConfig_3882_; uint8_t v_trackZetaDelta_3883_; lean_object* v_zetaDeltaSet_3884_; lean_object* v_lctx_3885_; lean_object* v_localInstances_3886_; lean_object* v_defEqCtx_x3f_3887_; lean_object* v_synthPendingDepth_3888_; lean_object* v_customCanUnfoldPredicate_x3f_3889_; uint8_t v_univApprox_3890_; uint8_t v_inTypeClassResolution_3891_; uint8_t v_cacheInferType_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_keyedConfig_3882_ = lean_ctor_get(v_a_3661_, 0);
v_trackZetaDelta_3883_ = lean_ctor_get_uint8(v_a_3661_, sizeof(void*)*7);
v_zetaDeltaSet_3884_ = lean_ctor_get(v_a_3661_, 1);
v_lctx_3885_ = lean_ctor_get(v_a_3661_, 2);
v_localInstances_3886_ = lean_ctor_get(v_a_3661_, 3);
v_defEqCtx_x3f_3887_ = lean_ctor_get(v_a_3661_, 4);
v_synthPendingDepth_3888_ = lean_ctor_get(v_a_3661_, 5);
v_customCanUnfoldPredicate_x3f_3889_ = lean_ctor_get(v_a_3661_, 6);
v_univApprox_3890_ = lean_ctor_get_uint8(v_a_3661_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3891_ = lean_ctor_get_uint8(v_a_3661_, sizeof(void*)*7 + 2);
v_cacheInferType_3892_ = lean_ctor_get_uint8(v_a_3661_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3882_);
v___x_3893_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3788_, v_keyedConfig_3882_);
lean_inc(v_customCanUnfoldPredicate_x3f_3889_);
lean_inc(v_synthPendingDepth_3888_);
lean_inc(v_defEqCtx_x3f_3887_);
lean_inc_ref(v_localInstances_3886_);
lean_inc_ref(v_lctx_3885_);
lean_inc(v_zetaDeltaSet_3884_);
v___x_3894_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
lean_ctor_set(v___x_3894_, 1, v_zetaDeltaSet_3884_);
lean_ctor_set(v___x_3894_, 2, v_lctx_3885_);
lean_ctor_set(v___x_3894_, 3, v_localInstances_3886_);
lean_ctor_set(v___x_3894_, 4, v_defEqCtx_x3f_3887_);
lean_ctor_set(v___x_3894_, 5, v_synthPendingDepth_3888_);
lean_ctor_set(v___x_3894_, 6, v_customCanUnfoldPredicate_x3f_3889_);
lean_ctor_set_uint8(v___x_3894_, sizeof(void*)*7, v_trackZetaDelta_3883_);
lean_ctor_set_uint8(v___x_3894_, sizeof(void*)*7 + 1, v_univApprox_3890_);
lean_ctor_set_uint8(v___x_3894_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3891_);
lean_ctor_set_uint8(v___x_3894_, sizeof(void*)*7 + 3, v_cacheInferType_3892_);
v___x_3895_ = l_Lean_Meta_whnfForall(v_a_3785_, v___x_3894_, v_a_3662_, v_a_3663_, v_a_3664_);
lean_dec_ref_known(v___x_3894_, 7);
v___y_3790_ = v___x_3895_;
goto v___jp_3789_;
}
else
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Lean_Meta_whnfForall(v_a_3785_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
v___y_3790_ = v___x_3896_;
goto v___jp_3789_;
}
v___jp_3789_:
{
if (lean_obj_tag(v___y_3790_) == 0)
{
lean_object* v_a_3791_; uint8_t v___x_3792_; 
v_a_3791_ = lean_ctor_get(v___y_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___y_3790_, 1);
v___x_3792_ = l_Lean_Expr_isForall(v_a_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
lean_dec(v_a_3791_);
lean_dec_ref(v___x_3786_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
lean_dec(v_val_3673_);
v___x_3793_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__6);
v___x_3794_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__2(v___x_3793_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
return v___x_3794_;
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___f_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3795_ = l_Lean_Expr_bindingDomain_x21(v_a_3791_);
v___x_3796_ = l_Lean_Expr_bindingName_x21(v_a_3791_);
v___x_3797_ = l_Lean_Expr_bindingBody_x21(v_a_3791_);
lean_dec(v_a_3791_);
v___x_3798_ = 0;
v___x_3799_ = lean_box(v___x_3798_);
v___x_3800_ = lean_box(v___x_3783_);
v___x_3801_ = lean_box(v___x_3667_);
v___f_3802_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3802_, 0, v___x_3799_);
lean_closure_set(v___f_3802_, 1, v___x_3800_);
lean_closure_set(v___f_3802_, 2, v___x_3801_);
lean_inc_ref(v___x_3795_);
v___x_3803_ = l_Lean_Expr_lam___override(v___x_3796_, v___x_3795_, v___x_3797_, v___x_3798_);
v___x_3804_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_isForallMotive(v_val_3673_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3864_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3864_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3864_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
if (lean_obj_tag(v_a_3805_) == 1)
{
lean_object* v_val_3809_; lean_object* v___x_3810_; 
lean_del_object(v___x_3807_);
v_val_3809_ = lean_ctor_get(v_a_3805_, 0);
lean_inc(v_val_3809_);
lean_dec_ref_known(v_a_3805_, 1);
v___x_3810_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__3___redArg(v_motive_3680_, v___f_3802_, v___x_3783_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3812_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3811_);
lean_dec_ref_known(v___x_3810_, 1);
v___x_3812_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher(v_matcherName_3678_, v_toMatcherInfo_3677_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; uint8_t v_transparency_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; size_t v_sz_3825_; size_t v___x_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v___x_3812_, 1);
v_transparency_3814_ = lean_ctor_get_uint8(v___x_3786_, 9);
lean_dec_ref(v___x_3786_);
v___x_3815_ = lean_unsigned_to_nat(5u);
v___x_3816_ = lean_mk_empty_array_with_capacity(v___x_3815_);
v___x_3817_ = lean_array_push(v___x_3816_, v_val_3809_);
v___x_3818_ = lean_array_push(v___x_3817_, v___x_3795_);
v___x_3819_ = lean_array_push(v___x_3818_, v___x_3803_);
v___x_3820_ = lean_array_push(v___x_3819_, v___x_3782_);
v___x_3821_ = lean_array_push(v___x_3820_, v_a_3811_);
v___x_3822_ = l_Array_append___redArg(v_params_3679_, v___x_3821_);
lean_dec_ref(v___x_3821_);
v___x_3823_ = l_Array_append___redArg(v___x_3822_, v_discrs_3681_);
lean_dec_ref(v_discrs_3681_);
v___x_3824_ = l_Array_append___redArg(v___x_3823_, v_alts_3682_);
lean_dec_ref(v_alts_3682_);
v_sz_3825_ = lean_array_size(v___x_3824_);
v___x_3826_ = ((size_t)0ULL);
v___x_3827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__4(v_sz_3825_, v___x_3826_, v___x_3824_);
v___x_3828_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3814_, v___x_3788_);
if (v___x_3828_ == 0)
{
lean_object* v_keyedConfig_3829_; uint8_t v_trackZetaDelta_3830_; lean_object* v_zetaDeltaSet_3831_; lean_object* v_lctx_3832_; lean_object* v_localInstances_3833_; lean_object* v_defEqCtx_x3f_3834_; lean_object* v_synthPendingDepth_3835_; lean_object* v_customCanUnfoldPredicate_x3f_3836_; uint8_t v_univApprox_3837_; uint8_t v_inTypeClassResolution_3838_; uint8_t v_cacheInferType_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v_keyedConfig_3829_ = lean_ctor_get(v_a_3661_, 0);
v_trackZetaDelta_3830_ = lean_ctor_get_uint8(v_a_3661_, sizeof(void*)*7);
v_zetaDeltaSet_3831_ = lean_ctor_get(v_a_3661_, 1);
v_lctx_3832_ = lean_ctor_get(v_a_3661_, 2);
v_localInstances_3833_ = lean_ctor_get(v_a_3661_, 3);
v_defEqCtx_x3f_3834_ = lean_ctor_get(v_a_3661_, 4);
v_synthPendingDepth_3835_ = lean_ctor_get(v_a_3661_, 5);
v_customCanUnfoldPredicate_x3f_3836_ = lean_ctor_get(v_a_3661_, 6);
v_univApprox_3837_ = lean_ctor_get_uint8(v_a_3661_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3838_ = lean_ctor_get_uint8(v_a_3661_, sizeof(void*)*7 + 2);
v_cacheInferType_3839_ = lean_ctor_get_uint8(v_a_3661_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3829_);
v___x_3840_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3788_, v_keyedConfig_3829_);
lean_inc(v_customCanUnfoldPredicate_x3f_3836_);
lean_inc(v_synthPendingDepth_3835_);
lean_inc(v_defEqCtx_x3f_3834_);
lean_inc_ref(v_localInstances_3833_);
lean_inc_ref(v_lctx_3832_);
lean_inc(v_zetaDeltaSet_3831_);
v___x_3841_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
lean_ctor_set(v___x_3841_, 1, v_zetaDeltaSet_3831_);
lean_ctor_set(v___x_3841_, 2, v_lctx_3832_);
lean_ctor_set(v___x_3841_, 3, v_localInstances_3833_);
lean_ctor_set(v___x_3841_, 4, v_defEqCtx_x3f_3834_);
lean_ctor_set(v___x_3841_, 5, v_synthPendingDepth_3835_);
lean_ctor_set(v___x_3841_, 6, v_customCanUnfoldPredicate_x3f_3836_);
lean_ctor_set_uint8(v___x_3841_, sizeof(void*)*7, v_trackZetaDelta_3830_);
lean_ctor_set_uint8(v___x_3841_, sizeof(void*)*7 + 1, v_univApprox_3837_);
lean_ctor_set_uint8(v___x_3841_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3838_);
lean_ctor_set_uint8(v___x_3841_, sizeof(void*)*7 + 3, v_cacheInferType_3839_);
v___x_3842_ = l_Lean_Meta_mkAppOptM(v_a_3813_, v___x_3827_, v___x_3841_, v_a_3662_, v_a_3663_, v_a_3664_);
lean_dec_ref_known(v___x_3841_, 7);
v___y_3713_ = v___x_3842_;
goto v___jp_3712_;
}
else
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Lean_Meta_mkAppOptM(v_a_3813_, v___x_3827_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
v___y_3713_ = v___x_3843_;
goto v___jp_3712_;
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec(v_a_3811_);
lean_dec(v_val_3809_);
lean_dec_ref(v___x_3803_);
lean_dec_ref(v___x_3795_);
lean_dec_ref(v___x_3786_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_params_3679_);
lean_del_object(v___x_3675_);
v_a_3844_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3812_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3812_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_dec(v_val_3809_);
lean_dec_ref(v___x_3803_);
lean_dec_ref(v___x_3795_);
lean_dec_ref(v___x_3786_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
v_a_3852_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3810_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3810_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
else
{
lean_object* v___x_3860_; lean_object* v___x_3862_; 
lean_dec(v_a_3805_);
lean_dec_ref(v___x_3803_);
lean_dec_ref(v___f_3802_);
lean_dec_ref(v___x_3795_);
lean_dec_ref(v___x_3786_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
v___x_3860_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3860_);
v___x_3862_ = v___x_3807_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3860_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
lean_dec_ref(v___x_3803_);
lean_dec_ref(v___f_3802_);
lean_dec_ref(v___x_3795_);
lean_dec_ref(v___x_3786_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
v_a_3865_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3804_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3804_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec_ref(v___x_3786_);
lean_dec_ref(v___x_3782_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
lean_dec(v_val_3673_);
v_a_3873_ = lean_ctor_get(v___y_3790_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___y_3790_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___y_3790_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___y_3790_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec_ref(v___x_3782_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
lean_dec(v_val_3673_);
v_a_3897_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3784_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3784_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
lean_dec_ref(v___x_3782_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
lean_dec(v_val_3673_);
v___x_3905_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3905_);
v___x_3907_ = v___x_3671_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
v___jp_3712_:
{
if (lean_obj_tag(v___y_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; 
v_a_3714_ = lean_ctor_get(v___y_3713_, 0);
lean_inc_n(v_a_3714_, 2);
lean_dec_ref_known(v___y_3713_, 1);
lean_inc(v_a_3664_);
lean_inc_ref(v_a_3663_);
lean_inc(v_a_3662_);
lean_inc_ref(v_a_3661_);
v___x_3715_ = lean_infer_type(v_a_3714_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1));
v___x_3718_ = lean_unsigned_to_nat(3u);
v___x_3719_ = l_Lean_Expr_isAppOfArity(v_a_3716_, v___x_3717_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; 
lean_dec(v_a_3716_);
lean_dec_ref(v_remaining_3683_);
lean_del_object(v___x_3675_);
lean_inc(v_a_3664_);
lean_inc_ref(v_a_3663_);
lean_inc(v_a_3662_);
lean_inc_ref(v_a_3661_);
v___x_3720_ = lean_infer_type(v_a_3714_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___x_3720_, 1);
v___x_3722_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__2);
v___x_3723_ = l_Lean_indentExpr(v_a_3721_);
v___x_3724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3722_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v___x_3724_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
return v___x_3725_;
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
v_a_3726_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3720_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3720_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3736_; 
v___x_3734_ = l_Lean_Expr_appArg_x21(v_a_3716_);
lean_dec(v_a_3716_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v_a_3714_);
v___x_3736_ = v___x_3675_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3714_);
v___x_3736_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3737_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3737_, 0, v___x_3734_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
lean_ctor_set_uint8(v___x_3737_, sizeof(void*)*2, v___x_3667_);
v___x_3738_ = l_Array_toSubarray___redArg(v_remaining_3683_, v___x_3711_, v___x_3685_);
v___x_3739_ = l_Subarray_copy___redArg(v___x_3738_);
v___x_3740_ = l_Lean_Meta_Simp_Result_addExtraArgs(v___x_3737_, v___x_3739_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
lean_dec_ref(v___x_3739_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3750_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3743_ = v___x_3740_;
v_isShared_3744_ = v_isSharedCheck_3750_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3740_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3750_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3748_; 
v___x_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3745_, 0, v_a_3741_);
v___x_3746_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v___x_3746_);
v___x_3748_ = v___x_3743_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
v_a_3751_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3740_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3740_);
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
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_dec(v_a_3714_);
lean_dec_ref(v_remaining_3683_);
lean_del_object(v___x_3675_);
v_a_3760_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3715_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3715_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v_remaining_3683_);
lean_del_object(v___x_3675_);
v_a_3768_ = lean_ctor_get(v___y_3713_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___y_3713_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___y_3713_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___y_3713_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
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
else
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
lean_dec_ref(v___x_3703_);
lean_dec_ref(v_remaining_3683_);
lean_dec_ref(v_alts_3682_);
lean_dec_ref(v_discrs_3681_);
lean_dec_ref(v_motive_3680_);
lean_dec_ref(v_params_3679_);
lean_dec(v_matcherName_3678_);
lean_dec_ref(v_toMatcherInfo_3677_);
lean_del_object(v___x_3675_);
lean_dec(v_val_3673_);
v___x_3909_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3909_);
v___x_3911_ = v___x_3671_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
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
lean_object* v___x_3914_; lean_object* v___x_3916_; 
lean_dec(v_a_3669_);
v___x_3914_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___closed__0));
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___x_3914_);
v___x_3916_ = v___x_3671_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
v_a_3919_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3668_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3668_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3657_ = stack[0].m_obj;
lean_object* v_a_3658_ = stack[1].m_obj;
lean_object* v_a_3659_ = stack[2].m_obj;
lean_object* v_a_3660_ = stack[3].m_obj;
lean_object* v_a_3661_ = stack[4].m_obj;
lean_object* v_a_3662_ = stack[5].m_obj;
lean_object* v_a_3663_ = stack[6].m_obj;
lean_object* v_a_3664_ = stack[7].m_obj;
lean_object* v_res_3927_;
v_res_3927_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(v_e_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
stack->m_obj
 = v_res_3927_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed(lean_object* v_e_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg(v_e_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
return v_res_3937_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(lean_object* v_declName_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___redArg(v_declName_3938_, v___y_3945_);
return v___x_3947_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3938_ = stack[0].m_obj;
lean_object* v___y_3939_ = stack[1].m_obj;
lean_object* v___y_3940_ = stack[2].m_obj;
lean_object* v___y_3941_ = stack[3].m_obj;
lean_object* v___y_3942_ = stack[4].m_obj;
lean_object* v___y_3943_ = stack[5].m_obj;
lean_object* v___y_3944_ = stack[6].m_obj;
lean_object* v___y_3945_ = stack[7].m_obj;
lean_object* v_res_3948_;
v_res_3948_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(v_declName_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
stack->m_obj
 = v_res_3948_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2___boxed(lean_object* v_declName_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__2(v_declName_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
return v_res_3958_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(lean_object* v_00_u03b1_3959_, lean_object* v_msg_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v___x_3969_; 
v___x_3969_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___redArg(v_msg_3960_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
return v___x_3969_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3960_ = stack[1].m_obj;
lean_object* v___y_3961_ = stack[2].m_obj;
lean_object* v___y_3962_ = stack[3].m_obj;
lean_object* v___y_3963_ = stack[4].m_obj;
lean_object* v___y_3964_ = stack[5].m_obj;
lean_object* v___y_3965_ = stack[6].m_obj;
lean_object* v___y_3966_ = stack[7].m_obj;
lean_object* v___y_3967_ = stack[8].m_obj;
lean_object* v_res_3970_;
v_res_3970_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(lean_box(0), v_msg_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
stack->m_obj
 = v_res_3970_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1___boxed(lean_object* v_00_u03b1_3971_, lean_object* v_msg_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__1(v_00_u03b1_3971_, v_msg_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
return v_res_3981_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3982_, lean_object* v_constName_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___redArg(v_constName_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
return v___x_3992_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3983_ = stack[1].m_obj;
lean_object* v___y_3984_ = stack[2].m_obj;
lean_object* v___y_3985_ = stack[3].m_obj;
lean_object* v___y_3986_ = stack[4].m_obj;
lean_object* v___y_3987_ = stack[5].m_obj;
lean_object* v___y_3988_ = stack[6].m_obj;
lean_object* v___y_3989_ = stack[7].m_obj;
lean_object* v___y_3990_ = stack[8].m_obj;
lean_object* v_res_3993_;
v_res_3993_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(lean_box(0), v_constName_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
stack->m_obj
 = v_res_3993_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3994_, lean_object* v_constName_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3(v_00_u03b1_3994_, v_constName_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
return v_res_4004_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b1_4005_, lean_object* v_ref_4006_, lean_object* v_constName_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v___x_4016_; 
v___x_4016_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___redArg(v_ref_4006_, v_constName_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
return v___x_4016_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4006_ = stack[1].m_obj;
lean_object* v_constName_4007_ = stack[2].m_obj;
lean_object* v___y_4008_ = stack[3].m_obj;
lean_object* v___y_4009_ = stack[4].m_obj;
lean_object* v___y_4010_ = stack[5].m_obj;
lean_object* v___y_4011_ = stack[6].m_obj;
lean_object* v___y_4012_ = stack[7].m_obj;
lean_object* v___y_4013_ = stack[8].m_obj;
lean_object* v___y_4014_ = stack[9].m_obj;
lean_object* v_res_4017_;
v_res_4017_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(lean_box(0), v_ref_4006_, v_constName_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
stack->m_obj
 = v_res_4017_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b1_4018_, lean_object* v_ref_4019_, lean_object* v_constName_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8(v_00_u03b1_4018_, v_ref_4019_, v_constName_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec(v_ref_4019_);
return v_res_4029_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_4030_, lean_object* v_ref_4031_, lean_object* v_msg_4032_, lean_object* v_declHint_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_ref_4031_, v_msg_4032_, v_declHint_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
return v___x_4042_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4031_ = stack[1].m_obj;
lean_object* v_msg_4032_ = stack[2].m_obj;
lean_object* v_declHint_4033_ = stack[3].m_obj;
lean_object* v___y_4034_ = stack[4].m_obj;
lean_object* v___y_4035_ = stack[5].m_obj;
lean_object* v___y_4036_ = stack[6].m_obj;
lean_object* v___y_4037_ = stack[7].m_obj;
lean_object* v___y_4038_ = stack[8].m_obj;
lean_object* v___y_4039_ = stack[9].m_obj;
lean_object* v___y_4040_ = stack[10].m_obj;
lean_object* v_res_4043_;
v_res_4043_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(lean_box(0), v_ref_4031_, v_msg_4032_, v_declHint_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
stack->m_obj
 = v_res_4043_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4044_, lean_object* v_ref_4045_, lean_object* v_msg_4046_, lean_object* v_declHint_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_4044_, v_ref_4045_, v_msg_4046_, v_declHint_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec(v_ref_4045_);
return v_res_4056_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(lean_object* v_msg_4057_, lean_object* v_declHint_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___redArg(v_msg_4057_, v_declHint_4058_, v___y_4065_);
return v___x_4067_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4057_ = stack[0].m_obj;
lean_object* v_declHint_4058_ = stack[1].m_obj;
lean_object* v___y_4059_ = stack[2].m_obj;
lean_object* v___y_4060_ = stack[3].m_obj;
lean_object* v___y_4061_ = stack[4].m_obj;
lean_object* v___y_4062_ = stack[5].m_obj;
lean_object* v___y_4063_ = stack[6].m_obj;
lean_object* v___y_4064_ = stack[7].m_obj;
lean_object* v___y_4065_ = stack[8].m_obj;
lean_object* v_res_4068_;
v_res_4068_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(v_msg_4057_, v_declHint_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
stack->m_obj
 = v_res_4068_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_4069_, lean_object* v_declHint_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__11_spec__12(v_msg_4069_, v_declHint_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v___y_4071_);
return v_res_4079_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(lean_object* v_00_u03b1_4080_, lean_object* v_ref_4081_, lean_object* v_msg_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___redArg(v_ref_4081_, v_msg_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
return v___x_4091_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4081_ = stack[1].m_obj;
lean_object* v_msg_4082_ = stack[2].m_obj;
lean_object* v___y_4083_ = stack[3].m_obj;
lean_object* v___y_4084_ = stack[4].m_obj;
lean_object* v___y_4085_ = stack[5].m_obj;
lean_object* v___y_4086_ = stack[6].m_obj;
lean_object* v___y_4087_ = stack[7].m_obj;
lean_object* v___y_4088_ = stack[8].m_obj;
lean_object* v___y_4089_ = stack[9].m_obj;
lean_object* v_res_4092_;
v_res_4092_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(lean_box(0), v_ref_4081_, v_msg_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
stack->m_obj
 = v_res_4092_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12___boxed(lean_object* v_00_u03b1_4093_, lean_object* v_ref_4094_, lean_object* v_msg_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_spec__0_spec__0_spec__3_spec__8_spec__10_spec__12(v_00_u03b1_4093_, v_ref_4094_, v_msg_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec(v_ref_4094_);
return v_res_4104_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4150_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4151_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4152_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg___boxed), 9, 0);
v___x_4153_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4150_, v___x_4151_, v___x_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4154_;
v_res_4154_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_();
stack->m_obj
 = v_res_4154_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10____boxed(lean_object* v_a_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_();
return v_res_4156_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0(void){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4157_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
return v___x_4158_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4159_ = lean_unsigned_to_nat(32u);
v___x_4160_ = lean_mk_empty_array_with_capacity(v___x_4159_);
v___x_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
return v___x_4161_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4163_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__2));
v___x_4164_ = l_Lean_stringToMessageData(v___x_4163_);
return v___x_4164_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(lean_object* v___x_4165_, lean_object* v___x_4166_, lean_object* v___x_4167_, lean_object* v___x_4168_, lean_object* v___x_4169_, uint8_t v___x_4170_, lean_object* v_mvarId_4171_, uint8_t v___x_4172_, lean_object* v_declName_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v___x_4179_; 
v___x_4179_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_4165_, v___x_4166_, v___x_4167_, v___x_4168_, v___y_4174_, v___y_4176_, v___y_4177_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
v___x_4181_ = lean_mk_empty_array_with_capacity(v___x_4169_);
v___x_4182_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4183_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4184_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4185_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
lean_inc(v___x_4169_);
v___x_4186_ = l_Lean_Name_num___override(v___x_4185_, v___x_4169_);
v___x_4187_ = l_Lean_Name_str___override(v___x_4186_, v___x_4182_);
v___x_4188_ = l_Lean_Name_str___override(v___x_4187_, v___x_4183_);
v___x_4189_ = l_Lean_Name_str___override(v___x_4188_, v___x_4184_);
v___x_4190_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0____regBuiltin___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_matcherPushArg_declare__19___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_300889135____hygCtx___hyg_10_));
v___x_4191_ = l_Lean_Name_str___override(v___x_4189_, v___x_4190_);
v___x_4192_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_4181_, v___x_4191_, v___x_4170_, v___y_4176_, v___y_4177_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; size_t v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4192_, 1);
v___x_4194_ = lean_box(0);
v___x_4195_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__0);
lean_inc_n(v___x_4169_, 2);
v___x_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
lean_ctor_set(v___x_4196_, 1, v___x_4169_);
v___x_4197_ = lean_unsigned_to_nat(32u);
v___x_4198_ = lean_mk_empty_array_with_capacity(v___x_4197_);
v___x_4199_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__1);
v___x_4200_ = ((size_t)5ULL);
v___x_4201_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4201_, 0, v___x_4199_);
lean_ctor_set(v___x_4201_, 1, v___x_4198_);
lean_ctor_set(v___x_4201_, 2, v___x_4169_);
lean_ctor_set(v___x_4201_, 3, v___x_4169_);
lean_ctor_set_usize(v___x_4201_, 4, v___x_4200_);
v___x_4202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4195_);
lean_ctor_set(v___x_4202_, 1, v___x_4195_);
lean_ctor_set(v___x_4202_, 2, v___x_4195_);
lean_ctor_set(v___x_4202_, 3, v___x_4201_);
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4196_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = l_Lean_Meta_simpTarget(v_mvarId_4171_, v_a_4180_, v_a_4193_, v___x_4194_, v___x_4172_, v___x_4203_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4247_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4207_ = v___x_4204_;
v_isShared_4208_ = v_isSharedCheck_4247_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4204_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4247_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v_fst_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4245_; 
v_fst_4209_ = lean_ctor_get(v_a_4205_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v_a_4205_);
if (v_isSharedCheck_4245_ == 0)
{
lean_object* v_unused_4246_; 
v_unused_4246_ = lean_ctor_get(v_a_4205_, 1);
lean_dec(v_unused_4246_);
v___x_4211_ = v_a_4205_;
v_isShared_4212_ = v_isSharedCheck_4245_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_fst_4209_);
lean_dec(v_a_4205_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4245_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
if (lean_obj_tag(v_fst_4209_) == 0)
{
lean_object* v___x_4213_; lean_object* v___x_4215_; 
lean_del_object(v___x_4211_);
lean_dec(v_declName_4173_);
v___x_4213_ = lean_box(0);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4213_);
v___x_4215_ = v___x_4207_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
else
{
lean_object* v_val_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4221_; 
lean_del_object(v___x_4207_);
v_val_4217_ = lean_ctor_get(v_fst_4209_, 0);
lean_inc(v_val_4217_);
lean_dec_ref_known(v_fst_4209_, 1);
v___x_4218_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___closed__3);
v___x_4219_ = l_Lean_MessageData_ofConstName(v_declName_4173_, v___x_4170_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set_tag(v___x_4211_, 7);
lean_ctor_set(v___x_4211_, 1, v___x_4219_);
lean_ctor_set(v___x_4211_, 0, v___x_4218_);
v___x_4221_ = v___x_4211_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4218_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___f_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4222_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_4223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4221_);
lean_ctor_set(v___x_4223_, 1, v___x_4222_);
v___f_4224_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_4224_, 0, v___x_4223_);
v___x_4225_ = lean_box(v___x_4172_);
v___x_4226_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___boxed), 7, 2);
lean_closure_set(v___x_4226_, 0, v_val_4217_);
lean_closure_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4226_, v___f_4224_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4227_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4227_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
v_a_4236_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4227_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4227_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
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
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_dec(v_declName_4173_);
v_a_4248_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4204_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4204_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec(v_a_4180_);
lean_dec(v_declName_4173_);
lean_dec(v_mvarId_4171_);
lean_dec(v___x_4169_);
v_a_4256_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4192_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4192_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec(v_declName_4173_);
lean_dec(v_mvarId_4171_);
lean_dec(v___x_4169_);
v_a_4264_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4179_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4179_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4165_ = stack[0].m_obj;
lean_object* v___x_4166_ = stack[1].m_obj;
lean_object* v___x_4167_ = stack[2].m_obj;
lean_object* v___x_4168_ = stack[3].m_obj;
lean_object* v___x_4169_ = stack[4].m_obj;
uint8_t v___x_4170_ = stack[5].m_num;
lean_object* v_mvarId_4171_ = stack[6].m_obj;
uint8_t v___x_4172_ = stack[7].m_num;
lean_object* v_declName_4173_ = stack[8].m_obj;
lean_object* v___y_4174_ = stack[9].m_obj;
lean_object* v___y_4175_ = stack[10].m_obj;
lean_object* v___y_4176_ = stack[11].m_obj;
lean_object* v___y_4177_ = stack[12].m_obj;
lean_object* v_res_4272_;
v_res_4272_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4165_, v___x_4166_, v___x_4167_, v___x_4168_, v___x_4169_, v___x_4170_, v_mvarId_4171_, v___x_4172_, v_declName_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
stack->m_obj
 = v_res_4272_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1___boxed(lean_object* v___x_4273_, lean_object* v___x_4274_, lean_object* v___x_4275_, lean_object* v___x_4276_, lean_object* v___x_4277_, lean_object* v___x_4278_, lean_object* v_mvarId_4279_, lean_object* v___x_4280_, lean_object* v_declName_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
uint8_t v___x_1412__boxed_4287_; uint8_t v___x_1413__boxed_4288_; lean_object* v_res_4289_; 
v___x_1412__boxed_4287_ = lean_unbox(v___x_4278_);
v___x_1413__boxed_4288_ = lean_unbox(v___x_4280_);
v_res_4289_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4273_, v___x_4274_, v___x_4275_, v___x_4276_, v___x_4277_, v___x_1412__boxed_4287_, v_mvarId_4279_, v___x_1413__boxed_4288_, v_declName_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
return v_res_4289_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2(void){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4299_ = lean_box(0);
v___x_4300_ = lean_unsigned_to_nat(16u);
v___x_4301_ = lean_mk_array(v___x_4300_, v___x_4299_);
return v___x_4301_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3(void){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4302_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2);
v___x_4303_ = lean_unsigned_to_nat(0u);
v___x_4304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4303_);
lean_ctor_set(v___x_4304_, 1, v___x_4302_);
return v___x_4304_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4(void){
_start:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4305_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
return v___x_4306_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5(void){
_start:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; lean_object* v___x_4310_; 
v___x_4307_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4);
v___x_4308_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3);
v___x_4309_ = 1;
v___x_4310_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4310_, 0, v___x_4308_);
lean_ctor_set(v___x_4310_, 1, v___x_4307_);
lean_ctor_set_uint8(v___x_4310_, sizeof(void*)*2, v___x_4309_);
return v___x_4310_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object* v_declName_4311_, lean_object* v_mvarId_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_){
_start:
{
lean_object* v___y_4319_; uint8_t v___x_4336_; uint8_t v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; uint8_t v_transparency_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; uint8_t v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4336_ = 0;
v___x_4337_ = 1;
v___x_4338_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0));
v___x_4339_ = l_Lean_Meta_Context_config(v_a_4313_);
v_transparency_4340_ = lean_ctor_get_uint8(v___x_4339_, 9);
lean_dec_ref(v___x_4339_);
v___x_4341_ = lean_unsigned_to_nat(0u);
v___x_4342_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1));
v___x_4343_ = 0;
v___x_4344_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
v___x_4345_ = l_Lean_Options_empty;
v___x_4346_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4340_, v___x_4343_);
if (v___x_4346_ == 0)
{
lean_object* v_keyedConfig_4347_; uint8_t v_trackZetaDelta_4348_; lean_object* v_zetaDeltaSet_4349_; lean_object* v_lctx_4350_; lean_object* v_localInstances_4351_; lean_object* v_defEqCtx_x3f_4352_; lean_object* v_synthPendingDepth_4353_; lean_object* v_customCanUnfoldPredicate_x3f_4354_; uint8_t v_univApprox_4355_; uint8_t v_inTypeClassResolution_4356_; uint8_t v_cacheInferType_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v_keyedConfig_4347_ = lean_ctor_get(v_a_4313_, 0);
v_trackZetaDelta_4348_ = lean_ctor_get_uint8(v_a_4313_, sizeof(void*)*7);
v_zetaDeltaSet_4349_ = lean_ctor_get(v_a_4313_, 1);
v_lctx_4350_ = lean_ctor_get(v_a_4313_, 2);
v_localInstances_4351_ = lean_ctor_get(v_a_4313_, 3);
v_defEqCtx_x3f_4352_ = lean_ctor_get(v_a_4313_, 4);
v_synthPendingDepth_4353_ = lean_ctor_get(v_a_4313_, 5);
v_customCanUnfoldPredicate_x3f_4354_ = lean_ctor_get(v_a_4313_, 6);
v_univApprox_4355_ = lean_ctor_get_uint8(v_a_4313_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4356_ = lean_ctor_get_uint8(v_a_4313_, sizeof(void*)*7 + 2);
v_cacheInferType_4357_ = lean_ctor_get_uint8(v_a_4313_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4347_);
v___x_4358_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4343_, v_keyedConfig_4347_);
lean_inc(v_customCanUnfoldPredicate_x3f_4354_);
lean_inc(v_synthPendingDepth_4353_);
lean_inc(v_defEqCtx_x3f_4352_);
lean_inc_ref(v_localInstances_4351_);
lean_inc_ref(v_lctx_4350_);
lean_inc(v_zetaDeltaSet_4349_);
v___x_4359_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4359_, 0, v___x_4358_);
lean_ctor_set(v___x_4359_, 1, v_zetaDeltaSet_4349_);
lean_ctor_set(v___x_4359_, 2, v_lctx_4350_);
lean_ctor_set(v___x_4359_, 3, v_localInstances_4351_);
lean_ctor_set(v___x_4359_, 4, v_defEqCtx_x3f_4352_);
lean_ctor_set(v___x_4359_, 5, v_synthPendingDepth_4353_);
lean_ctor_set(v___x_4359_, 6, v_customCanUnfoldPredicate_x3f_4354_);
lean_ctor_set_uint8(v___x_4359_, sizeof(void*)*7, v_trackZetaDelta_4348_);
lean_ctor_set_uint8(v___x_4359_, sizeof(void*)*7 + 1, v_univApprox_4355_);
lean_ctor_set_uint8(v___x_4359_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4356_);
lean_ctor_set_uint8(v___x_4359_, sizeof(void*)*7 + 3, v_cacheInferType_4357_);
v___x_4360_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4338_, v___x_4342_, v___x_4344_, v___x_4345_, v___x_4341_, v___x_4336_, v_mvarId_4312_, v___x_4337_, v_declName_4311_, v___x_4359_, v_a_4314_, v_a_4315_, v_a_4316_);
lean_dec_ref_known(v___x_4359_, 7);
v___y_4319_ = v___x_4360_;
goto v___jp_4318_;
}
else
{
lean_object* v___x_4361_; 
v___x_4361_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___lam__1(v___x_4338_, v___x_4342_, v___x_4344_, v___x_4345_, v___x_4341_, v___x_4336_, v_mvarId_4312_, v___x_4337_, v_declName_4311_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
v___y_4319_ = v___x_4361_;
goto v___jp_4318_;
}
v___jp_4318_:
{
if (lean_obj_tag(v___y_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
v_a_4320_ = lean_ctor_get(v___y_4319_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___y_4319_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___y_4319_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___y_4319_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
v_a_4328_ = lean_ctor_get(v___y_4319_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___y_4319_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___y_4319_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___y_4319_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4311_ = stack[0].m_obj;
lean_object* v_mvarId_4312_ = stack[1].m_obj;
lean_object* v_a_4313_ = stack[2].m_obj;
lean_object* v_a_4314_ = stack[3].m_obj;
lean_object* v_a_4315_ = stack[4].m_obj;
lean_object* v_a_4316_ = stack[5].m_obj;
lean_object* v_res_4362_;
v_res_4362_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4311_, v_mvarId_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
stack->m_obj
 = v_res_4362_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___boxed(lean_object* v_declName_4363_, lean_object* v_mvarId_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4363_, v_mvarId_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
lean_dec(v_a_4368_);
lean_dec_ref(v_a_4367_);
lean_dec(v_a_4366_);
lean_dec_ref(v_a_4365_);
return v_res_4370_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(lean_object* v_e_4371_, lean_object* v_k_4372_, uint8_t v_cleanupAnnotations_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v___f_4379_; uint8_t v___x_4380_; uint8_t v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___f_4379_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4379_, 0, v_k_4372_);
v___x_4380_ = 1;
v___x_4381_ = 0;
v___x_4382_ = lean_box(0);
v___x_4383_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4371_, v___x_4380_, v___x_4381_, v___x_4380_, v___x_4381_, v___x_4382_, v___f_4379_, v_cleanupAnnotations_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v___x_4383_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4383_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
if (v_isShared_4387_ == 0)
{
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4384_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
v_a_4392_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4383_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4383_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4392_);
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
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4371_ = stack[0].m_obj;
lean_object* v_k_4372_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_4373_ = stack[2].m_num;
lean_object* v___y_4374_ = stack[3].m_obj;
lean_object* v___y_4375_ = stack[4].m_obj;
lean_object* v___y_4376_ = stack[5].m_obj;
lean_object* v___y_4377_ = stack[6].m_obj;
lean_object* v_res_4400_;
v_res_4400_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4371_, v_k_4372_, v_cleanupAnnotations_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
stack->m_obj
 = v_res_4400_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg___boxed(lean_object* v_e_4401_, lean_object* v_k_4402_, lean_object* v_cleanupAnnotations_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4409_; lean_object* v_res_4410_; 
v_cleanupAnnotations_boxed_4409_ = lean_unbox(v_cleanupAnnotations_4403_);
v_res_4410_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4401_, v_k_4402_, v_cleanupAnnotations_boxed_4409_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
return v_res_4410_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_object* v_00_u03b1_4411_, lean_object* v_e_4412_, lean_object* v_k_4413_, uint8_t v_cleanupAnnotations_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_e_4412_, v_k_4413_, v_cleanupAnnotations_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
return v___x_4420_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4412_ = stack[1].m_obj;
lean_object* v_k_4413_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_4414_ = stack[3].m_num;
lean_object* v___y_4415_ = stack[4].m_obj;
lean_object* v___y_4416_ = stack[5].m_obj;
lean_object* v___y_4417_ = stack[6].m_obj;
lean_object* v___y_4418_ = stack[7].m_obj;
lean_object* v_res_4421_;
v_res_4421_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(lean_box(0), v_e_4412_, v_k_4413_, v_cleanupAnnotations_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
stack->m_obj
 = v_res_4421_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed(lean_object* v_00_u03b1_4422_, lean_object* v_e_4423_, lean_object* v_k_4424_, lean_object* v_cleanupAnnotations_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4431_; lean_object* v_res_4432_; 
v_cleanupAnnotations_boxed_4431_ = lean_unbox(v_cleanupAnnotations_4425_);
v_res_4432_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1(v_00_u03b1_4422_, v_e_4423_, v_k_4424_, v_cleanupAnnotations_boxed_4431_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(lean_object* v_opts_4433_, lean_object* v_opt_4434_){
_start:
{
lean_object* v_name_4435_; lean_object* v_defValue_4436_; lean_object* v_map_4437_; lean_object* v___x_4438_; 
v_name_4435_ = lean_ctor_get(v_opt_4434_, 0);
v_defValue_4436_ = lean_ctor_get(v_opt_4434_, 1);
v_map_4437_ = lean_ctor_get(v_opts_4433_, 0);
v___x_4438_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4437_, v_name_4435_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_inc(v_defValue_4436_);
return v_defValue_4436_;
}
else
{
lean_object* v_val_4439_; 
v_val_4439_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_val_4439_);
lean_dec_ref_known(v___x_4438_, 1);
if (lean_obj_tag(v_val_4439_) == 3)
{
lean_object* v_v_4440_; 
v_v_4440_ = lean_ctor_get(v_val_4439_, 0);
lean_inc(v_v_4440_);
lean_dec_ref_known(v_val_4439_, 1);
return v_v_4440_;
}
else
{
lean_dec(v_val_4439_);
lean_inc(v_defValue_4436_);
return v_defValue_4436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2___boxed(lean_object* v_opts_4441_, lean_object* v_opt_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v_opts_4441_, v_opt_4442_);
lean_dec_ref(v_opt_4442_);
lean_dec_ref(v_opts_4441_);
return v_res_4443_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4444_; double v___x_4445_; 
v___x_4444_ = lean_unsigned_to_nat(0u);
v___x_4445_ = lean_float_of_nat(v___x_4444_);
return v___x_4445_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(lean_object* v_cls_4449_, lean_object* v_msg_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v_ref_4456_; lean_object* v___x_4457_; lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4503_; 
v_ref_4456_ = lean_ctor_get(v___y_4453_, 2);
v___x_4457_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3_spec__4(v_msg_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4460_ = v___x_4457_;
v_isShared_4461_ = v_isSharedCheck_4503_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4457_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4503_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4462_; lean_object* v_traceState_4463_; lean_object* v_env_4464_; lean_object* v_nextMacroScope_4465_; lean_object* v_ngen_4466_; lean_object* v_auxDeclNGen_4467_; lean_object* v_cache_4468_; lean_object* v_recordedDeps_4469_; lean_object* v_messages_4470_; lean_object* v_infoState_4471_; lean_object* v_snapshotTasks_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4502_; 
v___x_4462_ = lean_st_ref_take(v___y_4454_);
v_traceState_4463_ = lean_ctor_get(v___x_4462_, 4);
v_env_4464_ = lean_ctor_get(v___x_4462_, 0);
v_nextMacroScope_4465_ = lean_ctor_get(v___x_4462_, 1);
v_ngen_4466_ = lean_ctor_get(v___x_4462_, 2);
v_auxDeclNGen_4467_ = lean_ctor_get(v___x_4462_, 3);
v_cache_4468_ = lean_ctor_get(v___x_4462_, 5);
v_recordedDeps_4469_ = lean_ctor_get(v___x_4462_, 6);
v_messages_4470_ = lean_ctor_get(v___x_4462_, 7);
v_infoState_4471_ = lean_ctor_get(v___x_4462_, 8);
v_snapshotTasks_4472_ = lean_ctor_get(v___x_4462_, 9);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4462_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4474_ = v___x_4462_;
v_isShared_4475_ = v_isSharedCheck_4502_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_snapshotTasks_4472_);
lean_inc(v_infoState_4471_);
lean_inc(v_messages_4470_);
lean_inc(v_recordedDeps_4469_);
lean_inc(v_cache_4468_);
lean_inc(v_traceState_4463_);
lean_inc(v_auxDeclNGen_4467_);
lean_inc(v_ngen_4466_);
lean_inc(v_nextMacroScope_4465_);
lean_inc(v_env_4464_);
lean_dec(v___x_4462_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4502_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
uint64_t v_tid_4476_; lean_object* v_traces_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4501_; 
v_tid_4476_ = lean_ctor_get_uint64(v_traceState_4463_, sizeof(void*)*1);
v_traces_4477_ = lean_ctor_get(v_traceState_4463_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_traceState_4463_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4479_ = v_traceState_4463_;
v_isShared_4480_ = v_isSharedCheck_4501_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_traces_4477_);
lean_dec(v_traceState_4463_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4501_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; double v___x_4483_; uint8_t v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4492_; 
v___x_4481_ = lean_box(0);
v___x_4482_ = lean_box(0);
v___x_4483_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__0);
v___x_4484_ = 0;
v___x_4485_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__1));
v___x_4486_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4486_, 0, v_cls_4449_);
lean_ctor_set(v___x_4486_, 1, v___x_4482_);
lean_ctor_set(v___x_4486_, 2, v___x_4485_);
lean_ctor_set_float(v___x_4486_, sizeof(void*)*3, v___x_4483_);
lean_ctor_set_float(v___x_4486_, sizeof(void*)*3 + 8, v___x_4483_);
lean_ctor_set_uint8(v___x_4486_, sizeof(void*)*3 + 16, v___x_4484_);
v___x_4487_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___closed__2));
v___x_4488_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4486_);
lean_ctor_set(v___x_4488_, 1, v_a_4458_);
lean_ctor_set(v___x_4488_, 2, v___x_4487_);
lean_inc(v_ref_4456_);
v___x_4489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4489_, 0, v_ref_4456_);
lean_ctor_set(v___x_4489_, 1, v___x_4488_);
v___x_4490_ = l_Lean_PersistentArray_push___redArg(v_traces_4477_, v___x_4489_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 0, v___x_4490_);
v___x_4492_ = v___x_4479_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4490_);
lean_ctor_set_uint64(v_reuseFailAlloc_4500_, sizeof(void*)*1, v_tid_4476_);
v___x_4492_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
lean_object* v___x_4494_; 
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 4, v___x_4492_);
v___x_4494_ = v___x_4474_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_env_4464_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v_nextMacroScope_4465_);
lean_ctor_set(v_reuseFailAlloc_4499_, 2, v_ngen_4466_);
lean_ctor_set(v_reuseFailAlloc_4499_, 3, v_auxDeclNGen_4467_);
lean_ctor_set(v_reuseFailAlloc_4499_, 4, v___x_4492_);
lean_ctor_set(v_reuseFailAlloc_4499_, 5, v_cache_4468_);
lean_ctor_set(v_reuseFailAlloc_4499_, 6, v_recordedDeps_4469_);
lean_ctor_set(v_reuseFailAlloc_4499_, 7, v_messages_4470_);
lean_ctor_set(v_reuseFailAlloc_4499_, 8, v_infoState_4471_);
lean_ctor_set(v_reuseFailAlloc_4499_, 9, v_snapshotTasks_4472_);
v___x_4494_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4495_; lean_object* v___x_4497_; 
v___x_4495_ = lean_st_ref_put(v___y_4454_, v___x_4494_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v___x_4481_);
v___x_4497_ = v___x_4460_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4481_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4449_ = stack[0].m_obj;
lean_object* v_msg_4450_ = stack[1].m_obj;
lean_object* v___y_4451_ = stack[2].m_obj;
lean_object* v___y_4452_ = stack[3].m_obj;
lean_object* v___y_4453_ = stack[4].m_obj;
lean_object* v___y_4454_ = stack[5].m_obj;
lean_object* v_res_4504_;
v_res_4504_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v_cls_4449_, v_msg_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
stack->m_obj
 = v_res_4504_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0___boxed(lean_object* v_cls_4505_, lean_object* v_msg_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v_cls_4505_, v_msg_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
return v_res_4512_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4523_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4524_ = l_Lean_Name_append(v___x_4523_, v___x_4522_);
return v___x_4524_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4526_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__6));
v___x_4527_ = l_Lean_stringToMessageData(v___x_4526_);
return v___x_4527_;
}
}
lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object* v_levelParams_4528_, lean_object* v_declName_4529_, lean_object* v_wfPreprocessProof_4530_, lean_object* v___x_4531_, lean_object* v_unaryPreDefName_4532_, lean_object* v_xs_4533_, lean_object* v_body_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4543_ = lean_box(0);
lean_inc(v_levelParams_4528_);
v___x_4544_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_4528_, v___x_4543_);
lean_inc(v_declName_4529_);
v___x_4545_ = l_Lean_mkConst(v_declName_4529_, v___x_4544_);
v___x_4546_ = l_Lean_mkAppN(v___x_4545_, v_xs_4533_);
v___x_4547_ = l_Lean_Meta_mkEq(v___x_4546_, v_body_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v_a_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc_n(v_a_4548_, 2);
lean_dec_ref_known(v___x_4547_, 1);
v___x_4549_ = lean_box(0);
v___x_4550_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4548_, v___x_4549_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc(v_a_4551_);
lean_dec_ref_known(v___x_4550_, 1);
v___x_4552_ = l_Lean_Expr_mvarId_x21(v_a_4551_);
v___x_4553_ = l_Lean_Meta_Simp_Result_addExtraArgs(v_wfPreprocessProof_4530_, v_xs_4533_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; uint8_t v___x_4557_; lean_object* v_mvarId_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_a_4554_);
lean_dec_ref_known(v___x_4553_, 1);
v___x_4555_ = l_Lean_Expr_appFn_x21(v_a_4548_);
v___x_4556_ = lean_box(0);
v___x_4557_ = 1;
v___x_4632_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4632_, 0, v___x_4555_);
lean_ctor_set(v___x_4632_, 1, v___x_4556_);
lean_ctor_set_uint8(v___x_4632_, sizeof(void*)*2, v___x_4557_);
v___x_4633_ = l_Lean_Meta_Simp_mkCongr(v___x_4632_, v_a_4554_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4635_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
lean_inc(v_a_4634_);
lean_dec_ref_known(v___x_4633_, 1);
v___x_4635_ = l_Lean_Meta_applySimpResultToTarget(v___x_4552_, v_a_4548_, v_a_4634_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v_a_4636_; uint8_t v___x_4637_; 
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
lean_inc(v_a_4636_);
lean_dec_ref_known(v___x_4635_, 1);
v___x_4637_ = lean_name_eq(v_declName_4529_, v_unaryPreDefName_4532_);
if (v___x_4637_ == 0)
{
lean_object* v___x_4638_; 
v___x_4638_ = l_Lean_Elab_Eqns_deltaLHS(v_a_4636_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v_a_4639_; 
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
lean_inc(v_a_4639_);
lean_dec_ref_known(v___x_4638_, 1);
v_mvarId_4559_ = v_a_4639_;
v___y_4560_ = v___y_4535_;
v___y_4561_ = v___y_4536_;
v___y_4562_ = v___y_4537_;
v___y_4563_ = v___y_4538_;
goto v___jp_4558_;
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
lean_dec(v_a_4551_);
lean_dec(v_a_4548_);
lean_dec(v___x_4531_);
lean_dec(v_declName_4529_);
lean_dec(v_levelParams_4528_);
v_a_4640_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4638_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4638_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4640_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
}
else
{
v_mvarId_4559_ = v_a_4636_;
v___y_4560_ = v___y_4535_;
v___y_4561_ = v___y_4536_;
v___y_4562_ = v___y_4537_;
v___y_4563_ = v___y_4538_;
goto v___jp_4558_;
}
}
else
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
lean_dec(v_a_4551_);
lean_dec(v_a_4548_);
lean_dec(v___x_4531_);
lean_dec(v_declName_4529_);
lean_dec(v_levelParams_4528_);
v_a_4648_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v___x_4635_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4635_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4651_ == 0)
{
v___x_4653_ = v___x_4650_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4648_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
}
}
else
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4663_; 
lean_dec(v___x_4552_);
lean_dec(v_a_4551_);
lean_dec(v_a_4548_);
lean_dec(v___x_4531_);
lean_dec(v_declName_4529_);
lean_dec(v_levelParams_4528_);
v_a_4656_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4658_ = v___x_4633_;
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4633_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v___x_4661_; 
if (v_isShared_4659_ == 0)
{
v___x_4661_ = v___x_4658_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_a_4656_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
v___jp_4558_:
{
lean_object* v___x_4564_; 
v___x_4564_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(v_mvarId_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
if (lean_obj_tag(v___x_4564_) == 0)
{
lean_object* v_a_4565_; lean_object* v___x_4566_; 
v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
lean_inc(v_a_4565_);
lean_dec_ref_known(v___x_4564_, 1);
v___x_4566_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(v_declName_4529_, v_a_4565_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v___x_4567_; lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4623_; 
lean_dec_ref_known(v___x_4566_, 1);
v___x_4567_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_4551_, v___y_4561_);
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4570_ = v___x_4567_;
v_isShared_4571_ = v_isSharedCheck_4623_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4567_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4623_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
uint8_t v___x_4572_; uint8_t v___x_4573_; lean_object* v___x_4574_; 
v___x_4572_ = 0;
v___x_4573_ = 1;
v___x_4574_ = l_Lean_Meta_mkForallFVars(v_xs_4533_, v_a_4548_, v___x_4572_, v___x_4557_, v___x_4557_, v___x_4573_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v___x_4576_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
lean_dec_ref_known(v___x_4574_, 1);
v___x_4576_ = l_Lean_Meta_letToHave(v_a_4575_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v_a_4577_; lean_object* v___x_4578_; 
v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_a_4577_);
lean_dec_ref_known(v___x_4576_, 1);
v___x_4578_ = l_Lean_Meta_mkLambdaFVars(v_xs_4533_, v_a_4568_, v___x_4572_, v___x_4557_, v___x_4572_, v___x_4557_, v___x_4573_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
if (lean_obj_tag(v___x_4578_) == 0)
{
lean_object* v_a_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4584_; 
v_a_4579_ = lean_ctor_get(v___x_4578_, 0);
lean_inc(v_a_4579_);
lean_dec_ref_known(v___x_4578_, 1);
lean_inc_n(v___x_4531_, 2);
v___x_4580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4531_);
lean_ctor_set(v___x_4580_, 1, v_levelParams_4528_);
lean_ctor_set(v___x_4580_, 2, v_a_4577_);
v___x_4581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4531_);
lean_ctor_set(v___x_4581_, 1, v___x_4543_);
v___x_4582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4580_);
lean_ctor_set(v___x_4582_, 1, v_a_4579_);
lean_ctor_set(v___x_4582_, 2, v___x_4581_);
if (v_isShared_4571_ == 0)
{
lean_ctor_set_tag(v___x_4570_, 2);
lean_ctor_set(v___x_4570_, 0, v___x_4582_);
v___x_4584_ = v___x_4570_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4582_);
v___x_4584_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
lean_object* v___x_4585_; 
v___x_4585_ = l_Lean_addDecl(v___x_4584_, v___x_4572_, v___y_4562_, v___y_4563_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_object* v___x_4586_; 
lean_dec_ref_known(v___x_4585_, 1);
lean_inc(v___x_4531_);
v___x_4586_ = l_Lean_inferDefEqAttr(v___x_4531_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_toCold_4587_; lean_object* v_options_4588_; uint8_t v_hasTrace_4589_; 
lean_dec_ref_known(v___x_4586_, 1);
v_toCold_4587_ = lean_ctor_get(v___y_4562_, 0);
v_options_4588_ = lean_ctor_get(v_toCold_4587_, 2);
v_hasTrace_4589_ = lean_ctor_get_uint8(v_options_4588_, sizeof(void*)*1);
if (v_hasTrace_4589_ == 0)
{
lean_dec(v___x_4531_);
goto v___jp_4540_;
}
else
{
lean_object* v_inheritedTraceOptions_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; uint8_t v___x_4593_; 
v_inheritedTraceOptions_4590_ = lean_ctor_get(v_toCold_4587_, 11);
v___x_4591_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_4592_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_4593_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4590_, v_options_4588_, v___x_4592_);
if (v___x_4593_ == 0)
{
lean_dec(v___x_4531_);
goto v___jp_4540_;
}
else
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4594_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__7);
v___x_4595_ = l_Lean_MessageData_ofConstName(v___x_4531_, v___x_4572_);
v___x_4596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4594_);
lean_ctor_set(v___x_4596_, 1, v___x_4595_);
v___x_4597_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_4591_, v___x_4596_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
return v___x_4597_;
}
}
}
else
{
lean_dec(v___x_4531_);
return v___x_4586_;
}
}
else
{
lean_dec(v___x_4531_);
return v___x_4585_;
}
}
}
else
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4606_; 
lean_dec(v_a_4577_);
lean_del_object(v___x_4570_);
lean_dec(v___x_4531_);
lean_dec(v_levelParams_4528_);
v_a_4599_ = lean_ctor_get(v___x_4578_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4578_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4601_ = v___x_4578_;
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4578_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4604_; 
if (v_isShared_4602_ == 0)
{
v___x_4604_ = v___x_4601_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
else
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
lean_del_object(v___x_4570_);
lean_dec(v_a_4568_);
lean_dec(v___x_4531_);
lean_dec(v_levelParams_4528_);
v_a_4607_ = lean_ctor_get(v___x_4576_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4576_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4576_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
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
else
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
lean_del_object(v___x_4570_);
lean_dec(v_a_4568_);
lean_dec(v___x_4531_);
lean_dec(v_levelParams_4528_);
v_a_4615_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4574_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4574_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
}
else
{
lean_dec(v_a_4551_);
lean_dec(v_a_4548_);
lean_dec(v___x_4531_);
lean_dec(v_levelParams_4528_);
return v___x_4566_;
}
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_dec(v_a_4551_);
lean_dec(v_a_4548_);
lean_dec(v___x_4531_);
lean_dec(v_declName_4529_);
lean_dec(v_levelParams_4528_);
v_a_4624_ = lean_ctor_get(v___x_4564_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4564_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4564_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
lean_dec(v___x_4552_);
lean_dec(v_a_4551_);
lean_dec(v_a_4548_);
lean_dec(v___x_4531_);
lean_dec(v_declName_4529_);
lean_dec(v_levelParams_4528_);
v_a_4664_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4553_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4553_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
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
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_dec(v_a_4548_);
lean_dec(v___x_4531_);
lean_dec_ref(v_wfPreprocessProof_4530_);
lean_dec(v_declName_4529_);
lean_dec(v_levelParams_4528_);
v_a_4672_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4550_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4550_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
else
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4687_; 
lean_dec(v___x_4531_);
lean_dec_ref(v_wfPreprocessProof_4530_);
lean_dec(v_declName_4529_);
lean_dec(v_levelParams_4528_);
v_a_4680_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4682_ = v___x_4547_;
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4547_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4685_; 
if (v_isShared_4683_ == 0)
{
v___x_4685_ = v___x_4682_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_a_4680_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
v___jp_4540_:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = lean_box(0);
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_mkUnfoldEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_levelParams_4528_ = stack[0].m_obj;
lean_object* v_declName_4529_ = stack[1].m_obj;
lean_object* v_wfPreprocessProof_4530_ = stack[2].m_obj;
lean_object* v___x_4531_ = stack[3].m_obj;
lean_object* v_unaryPreDefName_4532_ = stack[4].m_obj;
lean_object* v_xs_4533_ = stack[5].m_obj;
lean_object* v_body_4534_ = stack[6].m_obj;
lean_object* v___y_4535_ = stack[7].m_obj;
lean_object* v___y_4536_ = stack[8].m_obj;
lean_object* v___y_4537_ = stack[9].m_obj;
lean_object* v___y_4538_ = stack[10].m_obj;
lean_object* v_res_4688_;
v_res_4688_ = l_Lean_Elab_WF_mkUnfoldEq___lam__0(v_levelParams_4528_, v_declName_4529_, v_wfPreprocessProof_4530_, v___x_4531_, v_unaryPreDefName_4532_, v_xs_4533_, v_body_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
stack->m_obj
 = v_res_4688_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object* v_levelParams_4689_, lean_object* v_declName_4690_, lean_object* v_wfPreprocessProof_4691_, lean_object* v___x_4692_, lean_object* v_unaryPreDefName_4693_, lean_object* v_xs_4694_, lean_object* v_body_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_Elab_WF_mkUnfoldEq___lam__0(v_levelParams_4689_, v_declName_4690_, v_wfPreprocessProof_4691_, v___x_4692_, v_unaryPreDefName_4693_, v_xs_4694_, v_body_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec_ref(v_xs_4694_);
lean_dec(v_unaryPreDefName_4693_);
return v_res_4701_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(lean_object* v___y_4702_, uint8_t v_isExporting_4703_, lean_object* v___x_4704_, lean_object* v___y_4705_, lean_object* v___x_4706_, lean_object* v_a_x3f_4707_){
_start:
{
lean_object* v___x_4709_; lean_object* v_env_4710_; lean_object* v_nextMacroScope_4711_; lean_object* v_ngen_4712_; lean_object* v_auxDeclNGen_4713_; lean_object* v_traceState_4714_; lean_object* v_recordedDeps_4715_; lean_object* v_messages_4716_; lean_object* v_infoState_4717_; lean_object* v_snapshotTasks_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4743_; 
v___x_4709_ = lean_st_ref_take(v___y_4702_);
v_env_4710_ = lean_ctor_get(v___x_4709_, 0);
v_nextMacroScope_4711_ = lean_ctor_get(v___x_4709_, 1);
v_ngen_4712_ = lean_ctor_get(v___x_4709_, 2);
v_auxDeclNGen_4713_ = lean_ctor_get(v___x_4709_, 3);
v_traceState_4714_ = lean_ctor_get(v___x_4709_, 4);
v_recordedDeps_4715_ = lean_ctor_get(v___x_4709_, 6);
v_messages_4716_ = lean_ctor_get(v___x_4709_, 7);
v_infoState_4717_ = lean_ctor_get(v___x_4709_, 8);
v_snapshotTasks_4718_ = lean_ctor_get(v___x_4709_, 9);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4743_ == 0)
{
lean_object* v_unused_4744_; 
v_unused_4744_ = lean_ctor_get(v___x_4709_, 5);
lean_dec(v_unused_4744_);
v___x_4720_ = v___x_4709_;
v_isShared_4721_ = v_isSharedCheck_4743_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_snapshotTasks_4718_);
lean_inc(v_infoState_4717_);
lean_inc(v_messages_4716_);
lean_inc(v_recordedDeps_4715_);
lean_inc(v_traceState_4714_);
lean_inc(v_auxDeclNGen_4713_);
lean_inc(v_ngen_4712_);
lean_inc(v_nextMacroScope_4711_);
lean_inc(v_env_4710_);
lean_dec(v___x_4709_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4743_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4722_; lean_object* v___x_4724_; 
v___x_4722_ = l_Lean_Environment_setExporting(v_env_4710_, v_isExporting_4703_);
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 5, v___x_4704_);
lean_ctor_set(v___x_4720_, 0, v___x_4722_);
v___x_4724_ = v___x_4720_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4742_, 1, v_nextMacroScope_4711_);
lean_ctor_set(v_reuseFailAlloc_4742_, 2, v_ngen_4712_);
lean_ctor_set(v_reuseFailAlloc_4742_, 3, v_auxDeclNGen_4713_);
lean_ctor_set(v_reuseFailAlloc_4742_, 4, v_traceState_4714_);
lean_ctor_set(v_reuseFailAlloc_4742_, 5, v___x_4704_);
lean_ctor_set(v_reuseFailAlloc_4742_, 6, v_recordedDeps_4715_);
lean_ctor_set(v_reuseFailAlloc_4742_, 7, v_messages_4716_);
lean_ctor_set(v_reuseFailAlloc_4742_, 8, v_infoState_4717_);
lean_ctor_set(v_reuseFailAlloc_4742_, 9, v_snapshotTasks_4718_);
v___x_4724_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v_mctx_4727_; lean_object* v_zetaDeltaFVarIds_4728_; lean_object* v_postponed_4729_; lean_object* v_diag_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4740_; 
v___x_4725_ = lean_st_ref_put(v___y_4702_, v___x_4724_);
v___x_4726_ = lean_st_ref_take(v___y_4705_);
v_mctx_4727_ = lean_ctor_get(v___x_4726_, 0);
v_zetaDeltaFVarIds_4728_ = lean_ctor_get(v___x_4726_, 2);
v_postponed_4729_ = lean_ctor_get(v___x_4726_, 3);
v_diag_4730_ = lean_ctor_get(v___x_4726_, 4);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4740_ == 0)
{
lean_object* v_unused_4741_; 
v_unused_4741_ = lean_ctor_get(v___x_4726_, 1);
lean_dec(v_unused_4741_);
v___x_4732_ = v___x_4726_;
v_isShared_4733_ = v_isSharedCheck_4740_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_diag_4730_);
lean_inc(v_postponed_4729_);
lean_inc(v_zetaDeltaFVarIds_4728_);
lean_inc(v_mctx_4727_);
lean_dec(v___x_4726_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4740_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4734_; lean_object* v___x_4736_; 
v___x_4734_ = lean_box(0);
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 1, v___x_4706_);
v___x_4736_ = v___x_4732_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_mctx_4727_);
lean_ctor_set(v_reuseFailAlloc_4739_, 1, v___x_4706_);
lean_ctor_set(v_reuseFailAlloc_4739_, 2, v_zetaDeltaFVarIds_4728_);
lean_ctor_set(v_reuseFailAlloc_4739_, 3, v_postponed_4729_);
lean_ctor_set(v_reuseFailAlloc_4739_, 4, v_diag_4730_);
v___x_4736_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4737_ = lean_st_ref_put(v___y_4705_, v___x_4736_);
v___x_4738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4734_);
return v___x_4738_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4702_ = stack[0].m_obj;
uint8_t v_isExporting_4703_ = stack[1].m_num;
lean_object* v___x_4704_ = stack[2].m_obj;
lean_object* v___y_4705_ = stack[3].m_obj;
lean_object* v___x_4706_ = stack[4].m_obj;
lean_object* v_a_x3f_4707_ = stack[5].m_obj;
lean_object* v_res_4745_;
v_res_4745_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(v___y_4702_, v_isExporting_4703_, v___x_4704_, v___y_4705_, v___x_4706_, v_a_x3f_4707_);
stack->m_obj
 = v_res_4745_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v___y_4746_, lean_object* v_isExporting_4747_, lean_object* v___x_4748_, lean_object* v___y_4749_, lean_object* v___x_4750_, lean_object* v_a_x3f_4751_, lean_object* v___y_4752_){
_start:
{
uint8_t v_isExporting_boxed_4753_; lean_object* v_res_4754_; 
v_isExporting_boxed_4753_ = lean_unbox(v_isExporting_4747_);
v_res_4754_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(v___y_4746_, v_isExporting_boxed_4753_, v___x_4748_, v___y_4749_, v___x_4750_, v_a_x3f_4751_);
lean_dec(v_a_x3f_4751_);
lean_dec(v___y_4749_);
lean_dec(v___y_4746_);
return v_res_4754_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4755_);
return v___x_4756_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4757_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0);
v___x_4758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4757_);
lean_ctor_set(v___x_4758_, 1, v___x_4757_);
return v___x_4758_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4759_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__0);
v___x_4760_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4759_);
lean_ctor_set(v___x_4760_, 1, v___x_4759_);
lean_ctor_set(v___x_4760_, 2, v___x_4759_);
lean_ctor_set(v___x_4760_, 3, v___x_4759_);
lean_ctor_set(v___x_4760_, 4, v___x_4759_);
lean_ctor_set(v___x_4760_, 5, v___x_4759_);
return v___x_4760_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(lean_object* v_x_4761_, uint8_t v_isExporting_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v___x_4768_; lean_object* v_env_4769_; lean_object* v___x_4770_; uint8_t v_isModule_4771_; 
v___x_4768_ = lean_st_ref_get(v___y_4766_);
v_env_4769_ = lean_ctor_get(v___x_4768_, 0);
lean_inc_ref(v_env_4769_);
lean_dec(v___x_4768_);
v___x_4770_ = l_Lean_Environment_header(v_env_4769_);
v_isModule_4771_ = lean_ctor_get_uint8(v___x_4770_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4770_);
if (v_isModule_4771_ == 0)
{
lean_object* v___x_4772_; 
lean_dec_ref(v_env_4769_);
lean_inc(v___y_4766_);
lean_inc_ref(v___y_4765_);
lean_inc(v___y_4764_);
lean_inc_ref(v___y_4763_);
v___x_4772_ = lean_apply_5(v_x_4761_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, lean_box(0));
return v___x_4772_;
}
else
{
uint8_t v_isExporting_4773_; 
v_isExporting_4773_ = lean_ctor_get_uint8(v_env_4769_, sizeof(void*)*13);
lean_dec_ref(v_env_4769_);
if (v_isExporting_4762_ == 0)
{
if (v_isExporting_4773_ == 0)
{
lean_object* v___x_4840_; 
lean_inc(v___y_4766_);
lean_inc_ref(v___y_4765_);
lean_inc(v___y_4764_);
lean_inc_ref(v___y_4763_);
v___x_4840_ = lean_apply_5(v_x_4761_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, lean_box(0));
return v___x_4840_;
}
else
{
goto v___jp_4774_;
}
}
else
{
if (v_isExporting_4773_ == 0)
{
goto v___jp_4774_;
}
else
{
lean_object* v___x_4841_; 
lean_inc(v___y_4766_);
lean_inc_ref(v___y_4765_);
lean_inc(v___y_4764_);
lean_inc_ref(v___y_4763_);
v___x_4841_ = lean_apply_5(v_x_4761_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, lean_box(0));
return v___x_4841_;
}
}
v___jp_4774_:
{
lean_object* v___x_4775_; lean_object* v_env_4776_; lean_object* v_nextMacroScope_4777_; lean_object* v_ngen_4778_; lean_object* v_auxDeclNGen_4779_; lean_object* v_traceState_4780_; lean_object* v_recordedDeps_4781_; lean_object* v_messages_4782_; lean_object* v_infoState_4783_; lean_object* v_snapshotTasks_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4838_; 
v___x_4775_ = lean_st_ref_take(v___y_4766_);
v_env_4776_ = lean_ctor_get(v___x_4775_, 0);
v_nextMacroScope_4777_ = lean_ctor_get(v___x_4775_, 1);
v_ngen_4778_ = lean_ctor_get(v___x_4775_, 2);
v_auxDeclNGen_4779_ = lean_ctor_get(v___x_4775_, 3);
v_traceState_4780_ = lean_ctor_get(v___x_4775_, 4);
v_recordedDeps_4781_ = lean_ctor_get(v___x_4775_, 6);
v_messages_4782_ = lean_ctor_get(v___x_4775_, 7);
v_infoState_4783_ = lean_ctor_get(v___x_4775_, 8);
v_snapshotTasks_4784_ = lean_ctor_get(v___x_4775_, 9);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4838_ == 0)
{
lean_object* v_unused_4839_; 
v_unused_4839_ = lean_ctor_get(v___x_4775_, 5);
lean_dec(v_unused_4839_);
v___x_4786_ = v___x_4775_;
v_isShared_4787_ = v_isSharedCheck_4838_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_snapshotTasks_4784_);
lean_inc(v_infoState_4783_);
lean_inc(v_messages_4782_);
lean_inc(v_recordedDeps_4781_);
lean_inc(v_traceState_4780_);
lean_inc(v_auxDeclNGen_4779_);
lean_inc(v_ngen_4778_);
lean_inc(v_nextMacroScope_4777_);
lean_inc(v_env_4776_);
lean_dec(v___x_4775_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4838_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4791_; 
v___x_4788_ = l_Lean_Environment_setExporting(v_env_4776_, v_isExporting_4762_);
v___x_4789_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1);
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 5, v___x_4789_);
lean_ctor_set(v___x_4786_, 0, v___x_4788_);
v___x_4791_ = v___x_4786_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v___x_4788_);
lean_ctor_set(v_reuseFailAlloc_4837_, 1, v_nextMacroScope_4777_);
lean_ctor_set(v_reuseFailAlloc_4837_, 2, v_ngen_4778_);
lean_ctor_set(v_reuseFailAlloc_4837_, 3, v_auxDeclNGen_4779_);
lean_ctor_set(v_reuseFailAlloc_4837_, 4, v_traceState_4780_);
lean_ctor_set(v_reuseFailAlloc_4837_, 5, v___x_4789_);
lean_ctor_set(v_reuseFailAlloc_4837_, 6, v_recordedDeps_4781_);
lean_ctor_set(v_reuseFailAlloc_4837_, 7, v_messages_4782_);
lean_ctor_set(v_reuseFailAlloc_4837_, 8, v_infoState_4783_);
lean_ctor_set(v_reuseFailAlloc_4837_, 9, v_snapshotTasks_4784_);
v___x_4791_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v_mctx_4794_; lean_object* v_zetaDeltaFVarIds_4795_; lean_object* v_postponed_4796_; lean_object* v_diag_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4835_; 
v___x_4792_ = lean_st_ref_put(v___y_4766_, v___x_4791_);
v___x_4793_ = lean_st_ref_take(v___y_4764_);
v_mctx_4794_ = lean_ctor_get(v___x_4793_, 0);
v_zetaDeltaFVarIds_4795_ = lean_ctor_get(v___x_4793_, 2);
v_postponed_4796_ = lean_ctor_get(v___x_4793_, 3);
v_diag_4797_ = lean_ctor_get(v___x_4793_, 4);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4835_ == 0)
{
lean_object* v_unused_4836_; 
v_unused_4836_ = lean_ctor_get(v___x_4793_, 1);
lean_dec(v_unused_4836_);
v___x_4799_ = v___x_4793_;
v_isShared_4800_ = v_isSharedCheck_4835_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_diag_4797_);
lean_inc(v_postponed_4796_);
lean_inc(v_zetaDeltaFVarIds_4795_);
lean_inc(v_mctx_4794_);
lean_dec(v___x_4793_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4835_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4801_; lean_object* v___x_4803_; 
v___x_4801_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__2);
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 1, v___x_4801_);
v___x_4803_ = v___x_4799_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_mctx_4794_);
lean_ctor_set(v_reuseFailAlloc_4834_, 1, v___x_4801_);
lean_ctor_set(v_reuseFailAlloc_4834_, 2, v_zetaDeltaFVarIds_4795_);
lean_ctor_set(v_reuseFailAlloc_4834_, 3, v_postponed_4796_);
lean_ctor_set(v_reuseFailAlloc_4834_, 4, v_diag_4797_);
v___x_4803_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
lean_object* v___x_4804_; lean_object* v_r_4805_; 
v___x_4804_ = lean_st_ref_put(v___y_4764_, v___x_4803_);
lean_inc(v___y_4766_);
lean_inc_ref(v___y_4765_);
lean_inc(v___y_4764_);
lean_inc_ref(v___y_4763_);
v_r_4805_ = lean_apply_5(v_x_4761_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, lean_box(0));
if (lean_obj_tag(v_r_4805_) == 0)
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4822_; 
v_a_4806_ = lean_ctor_get(v_r_4805_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v_r_4805_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4808_ = v_r_4805_;
v_isShared_4809_ = v_isSharedCheck_4822_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v_r_4805_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4822_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
lean_inc(v_a_4806_);
if (v_isShared_4809_ == 0)
{
lean_ctor_set_tag(v___x_4808_, 1);
v___x_4811_ = v___x_4808_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_a_4806_);
v___x_4811_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
lean_object* v___x_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4819_; 
v___x_4812_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(v___y_4766_, v_isExporting_4773_, v___x_4789_, v___y_4764_, v___x_4801_, v___x_4811_);
lean_dec_ref(v___x_4811_);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4819_ == 0)
{
lean_object* v_unused_4820_; 
v_unused_4820_ = lean_ctor_get(v___x_4812_, 0);
lean_dec(v_unused_4820_);
v___x_4814_ = v___x_4812_;
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
else
{
lean_dec(v___x_4812_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4817_; 
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 0, v_a_4806_);
v___x_4817_ = v___x_4814_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4806_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
}
else
{
lean_object* v_a_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4832_; 
v_a_4823_ = lean_ctor_get(v_r_4805_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v_r_4805_, 1);
v___x_4824_ = lean_box(0);
v___x_4825_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___lam__0(v___y_4766_, v_isExporting_4773_, v___x_4789_, v___y_4764_, v___x_4801_, v___x_4824_);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4825_);
if (v_isSharedCheck_4832_ == 0)
{
lean_object* v_unused_4833_; 
v_unused_4833_ = lean_ctor_get(v___x_4825_, 0);
lean_dec(v_unused_4833_);
v___x_4827_ = v___x_4825_;
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
else
{
lean_dec(v___x_4825_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4830_; 
if (v_isShared_4828_ == 0)
{
lean_ctor_set_tag(v___x_4827_, 1);
lean_ctor_set(v___x_4827_, 0, v_a_4823_);
v___x_4830_ = v___x_4827_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4823_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4761_ = stack[0].m_obj;
uint8_t v_isExporting_4762_ = stack[1].m_num;
lean_object* v___y_4763_ = stack[2].m_obj;
lean_object* v___y_4764_ = stack[3].m_obj;
lean_object* v___y_4765_ = stack[4].m_obj;
lean_object* v___y_4766_ = stack[5].m_obj;
lean_object* v_res_4842_;
v_res_4842_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(v_x_4761_, v_isExporting_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_);
stack->m_obj
 = v_res_4842_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___boxed(lean_object* v_x_4843_, lean_object* v_isExporting_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
uint8_t v_isExporting_boxed_4850_; lean_object* v_res_4851_; 
v_isExporting_boxed_4850_ = lean_unbox(v_isExporting_4844_);
v_res_4851_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(v_x_4843_, v_isExporting_boxed_4850_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
return v_res_4851_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(lean_object* v_x_4852_, uint8_t v_when_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
if (v_when_4853_ == 0)
{
lean_object* v___x_4859_; 
lean_inc(v___y_4857_);
lean_inc_ref(v___y_4856_);
lean_inc(v___y_4855_);
lean_inc_ref(v___y_4854_);
v___x_4859_ = lean_apply_5(v_x_4852_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, lean_box(0));
return v___x_4859_;
}
else
{
uint8_t v___x_4860_; lean_object* v___x_4861_; 
v___x_4860_ = 0;
v___x_4861_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(v_x_4852_, v___x_4860_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
return v___x_4861_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4852_ = stack[0].m_obj;
uint8_t v_when_4853_ = stack[1].m_num;
lean_object* v___y_4854_ = stack[2].m_obj;
lean_object* v___y_4855_ = stack[3].m_obj;
lean_object* v___y_4856_ = stack[4].m_obj;
lean_object* v___y_4857_ = stack[5].m_obj;
lean_object* v_res_4862_;
v_res_4862_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(v_x_4852_, v_when_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
stack->m_obj
 = v_res_4862_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg___boxed(lean_object* v_x_4863_, lean_object* v_when_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_){
_start:
{
uint8_t v_when_boxed_4870_; lean_object* v_res_4871_; 
v_when_boxed_4870_ = lean_unbox(v_when_4864_);
v_res_4871_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(v_x_4863_, v_when_boxed_4870_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_);
lean_dec(v___y_4868_);
lean_dec_ref(v___y_4867_);
lean_dec(v___y_4866_);
lean_dec_ref(v___y_4865_);
return v_res_4871_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5(lean_object* v_o_4872_, lean_object* v_k_4873_, uint8_t v_v_4874_){
_start:
{
lean_object* v_map_4875_; uint8_t v_hasTrace_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4890_; 
v_map_4875_ = lean_ctor_get(v_o_4872_, 0);
v_hasTrace_4876_ = lean_ctor_get_uint8(v_o_4872_, sizeof(void*)*1);
v_isSharedCheck_4890_ = !lean_is_exclusive(v_o_4872_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4878_ = v_o_4872_;
v_isShared_4879_ = v_isSharedCheck_4890_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_map_4875_);
lean_dec(v_o_4872_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4890_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4880_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4880_, 0, v_v_4874_);
lean_inc(v_k_4873_);
v___x_4881_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4873_, v___x_4880_, v_map_4875_);
if (v_hasTrace_4876_ == 0)
{
lean_object* v___x_4882_; uint8_t v___x_4883_; lean_object* v___x_4885_; 
v___x_4882_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__4));
v___x_4883_ = l_Lean_Name_isPrefixOf(v___x_4882_, v_k_4873_);
lean_dec(v_k_4873_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v___x_4881_);
v___x_4885_ = v___x_4878_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4881_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
lean_ctor_set_uint8(v___x_4885_, sizeof(void*)*1, v___x_4883_);
return v___x_4885_;
}
}
else
{
lean_object* v___x_4888_; 
lean_dec(v_k_4873_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v___x_4881_);
v___x_4888_ = v___x_4878_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4881_);
lean_ctor_set_uint8(v_reuseFailAlloc_4889_, sizeof(void*)*1, v_hasTrace_4876_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_4872_ = stack[0].m_obj;
lean_object* v_k_4873_ = stack[1].m_obj;
uint8_t v_v_4874_ = stack[2].m_num;
lean_object* v_res_4891_;
v_res_4891_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5(v_o_4872_, v_k_4873_, v_v_4874_);
stack->m_obj
 = v_res_4891_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5___boxed(lean_object* v_o_4892_, lean_object* v_k_4893_, lean_object* v_v_4894_){
_start:
{
uint8_t v_v_boxed_4895_; lean_object* v_res_4896_; 
v_v_boxed_4895_ = lean_unbox(v_v_4894_);
v_res_4896_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5(v_o_4892_, v_k_4893_, v_v_boxed_4895_);
return v_res_4896_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(lean_object* v_opts_4897_, lean_object* v_opt_4898_, uint8_t v_val_4899_){
_start:
{
lean_object* v_name_4900_; lean_object* v___x_4901_; 
v_name_4900_ = lean_ctor_get(v_opt_4898_, 0);
lean_inc(v_name_4900_);
lean_dec_ref(v_opt_4898_);
v___x_4901_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_spec__5(v_opts_4897_, v_name_4900_, v_val_4899_);
return v___x_4901_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_4897_ = stack[0].m_obj;
lean_object* v_opt_4898_ = stack[1].m_obj;
uint8_t v_val_4899_ = stack[2].m_num;
lean_object* v_res_4902_;
v_res_4902_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_opts_4897_, v_opt_4898_, v_val_4899_);
stack->m_obj
 = v_res_4902_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4___boxed(lean_object* v_opts_4903_, lean_object* v_opt_4904_, lean_object* v_val_4905_){
_start:
{
uint8_t v_val_boxed_4906_; lean_object* v_res_4907_; 
v_val_boxed_4906_ = lean_unbox(v_val_4905_);
v_res_4907_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_opts_4903_, v_opt_4904_, v_val_boxed_4906_);
return v_res_4907_;
}
}
lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(lean_object* v___x_4908_, uint8_t v___x_4909_, uint8_t v___x_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v___y_4917_; uint16_t v___y_4918_; lean_object* v_fileName_4919_; lean_object* v_fileMap_4920_; lean_object* v_currNamespace_4921_; lean_object* v_openDecls_4922_; lean_object* v_initHeartbeats_4923_; lean_object* v_maxHeartbeats_4924_; lean_object* v_quotContext_4925_; lean_object* v_currMacroScope_4926_; lean_object* v_cancelTk_x3f_4927_; lean_object* v_inheritedTraceOptions_4928_; lean_object* v_currRecDepth_4929_; lean_object* v_ref_4930_; uint8_t v_suppressElabErrors_4931_; uint8_t v_isRecordingDeps_4932_; lean_object* v___y_4933_; lean_object* v_toCold_4939_; lean_object* v_currRecDepth_4940_; lean_object* v_ref_4941_; uint8_t v_suppressElabErrors_4942_; uint8_t v_isRecordingDeps_4943_; lean_object* v_fileName_4944_; lean_object* v_fileMap_4945_; lean_object* v_options_4946_; lean_object* v_currNamespace_4947_; lean_object* v_openDecls_4948_; lean_object* v_initHeartbeats_4949_; lean_object* v_maxHeartbeats_4950_; lean_object* v_quotContext_4951_; lean_object* v_currMacroScope_4952_; lean_object* v_cancelTk_x3f_4953_; lean_object* v_inheritedTraceOptions_4954_; uint8_t v___y_4956_; lean_object* v___y_4957_; uint16_t v___y_4958_; lean_object* v___y_4981_; 
v_toCold_4939_ = lean_ctor_get(v___y_4913_, 0);
v_currRecDepth_4940_ = lean_ctor_get(v___y_4913_, 1);
v_ref_4941_ = lean_ctor_get(v___y_4913_, 2);
v_suppressElabErrors_4942_ = lean_ctor_get_uint8(v___y_4913_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4943_ = lean_ctor_get_uint8(v___y_4913_, sizeof(void*)*3 + 3);
v_fileName_4944_ = lean_ctor_get(v_toCold_4939_, 0);
v_fileMap_4945_ = lean_ctor_get(v_toCold_4939_, 1);
v_options_4946_ = lean_ctor_get(v_toCold_4939_, 2);
v_currNamespace_4947_ = lean_ctor_get(v_toCold_4939_, 4);
v_openDecls_4948_ = lean_ctor_get(v_toCold_4939_, 5);
v_initHeartbeats_4949_ = lean_ctor_get(v_toCold_4939_, 6);
v_maxHeartbeats_4950_ = lean_ctor_get(v_toCold_4939_, 7);
v_quotContext_4951_ = lean_ctor_get(v_toCold_4939_, 8);
v_currMacroScope_4952_ = lean_ctor_get(v_toCold_4939_, 9);
v_cancelTk_x3f_4953_ = lean_ctor_get(v_toCold_4939_, 10);
v_inheritedTraceOptions_4954_ = lean_ctor_get(v_toCold_4939_, 11);
if (v_isRecordingDeps_4943_ == 0)
{
lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4990_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_4946_);
v___x_4991_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_options_4946_, v___x_4990_, v_isRecordingDeps_4943_);
v___y_4981_ = v___x_4991_;
goto v___jp_4980_;
}
else
{
lean_object* v___x_4992_; 
lean_inc_ref(v_options_4946_);
v___x_4992_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_4946_);
v___y_4981_ = v___x_4992_;
goto v___jp_4980_;
}
v___jp_4916_:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4934_ = l_Lean_maxRecDepth;
v___x_4935_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v___y_4917_, v___x_4934_);
v___x_4936_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4936_, 0, v_fileName_4919_);
lean_ctor_set(v___x_4936_, 1, v_fileMap_4920_);
lean_ctor_set(v___x_4936_, 2, v___y_4917_);
lean_ctor_set(v___x_4936_, 3, v___x_4935_);
lean_ctor_set(v___x_4936_, 4, v_currNamespace_4921_);
lean_ctor_set(v___x_4936_, 5, v_openDecls_4922_);
lean_ctor_set(v___x_4936_, 6, v_initHeartbeats_4923_);
lean_ctor_set(v___x_4936_, 7, v_maxHeartbeats_4924_);
lean_ctor_set(v___x_4936_, 8, v_quotContext_4925_);
lean_ctor_set(v___x_4936_, 9, v_currMacroScope_4926_);
lean_ctor_set(v___x_4936_, 10, v_cancelTk_x3f_4927_);
lean_ctor_set(v___x_4936_, 11, v_inheritedTraceOptions_4928_);
lean_inc(v_ref_4930_);
lean_inc(v_currRecDepth_4929_);
v___x_4937_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4937_, 0, v___x_4936_);
lean_ctor_set(v___x_4937_, 1, v_currRecDepth_4929_);
lean_ctor_set(v___x_4937_, 2, v_ref_4930_);
lean_ctor_set_uint16(v___x_4937_, sizeof(void*)*3, v___y_4918_);
lean_ctor_set_uint8(v___x_4937_, sizeof(void*)*3 + 2, v_suppressElabErrors_4931_);
lean_ctor_set_uint8(v___x_4937_, sizeof(void*)*3 + 3, v_isRecordingDeps_4932_);
v___x_4938_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(v___x_4908_, v___x_4909_, v___y_4911_, v___y_4912_, v___x_4937_, v___y_4933_);
lean_dec_ref_known(v___x_4937_, 3);
return v___x_4938_;
}
v___jp_4955_:
{
lean_object* v___x_4959_; lean_object* v_env_4960_; lean_object* v_nextMacroScope_4961_; lean_object* v_ngen_4962_; lean_object* v_auxDeclNGen_4963_; lean_object* v_traceState_4964_; lean_object* v_recordedDeps_4965_; lean_object* v_messages_4966_; lean_object* v_infoState_4967_; lean_object* v_snapshotTasks_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4978_; 
v___x_4959_ = lean_st_ref_take(v___y_4914_);
v_env_4960_ = lean_ctor_get(v___x_4959_, 0);
v_nextMacroScope_4961_ = lean_ctor_get(v___x_4959_, 1);
v_ngen_4962_ = lean_ctor_get(v___x_4959_, 2);
v_auxDeclNGen_4963_ = lean_ctor_get(v___x_4959_, 3);
v_traceState_4964_ = lean_ctor_get(v___x_4959_, 4);
v_recordedDeps_4965_ = lean_ctor_get(v___x_4959_, 6);
v_messages_4966_ = lean_ctor_get(v___x_4959_, 7);
v_infoState_4967_ = lean_ctor_get(v___x_4959_, 8);
v_snapshotTasks_4968_ = lean_ctor_get(v___x_4959_, 9);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_4978_ == 0)
{
lean_object* v_unused_4979_; 
v_unused_4979_ = lean_ctor_get(v___x_4959_, 5);
lean_dec(v_unused_4979_);
v___x_4970_ = v___x_4959_;
v_isShared_4971_ = v_isSharedCheck_4978_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_snapshotTasks_4968_);
lean_inc(v_infoState_4967_);
lean_inc(v_messages_4966_);
lean_inc(v_recordedDeps_4965_);
lean_inc(v_traceState_4964_);
lean_inc(v_auxDeclNGen_4963_);
lean_inc(v_ngen_4962_);
lean_inc(v_nextMacroScope_4961_);
lean_inc(v_env_4960_);
lean_dec(v___x_4959_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4978_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4975_; 
v___x_4972_ = l_Lean_Kernel_enableDiag(v_env_4960_, v___y_4956_);
v___x_4973_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1);
if (v_isShared_4971_ == 0)
{
lean_ctor_set(v___x_4970_, 5, v___x_4973_);
lean_ctor_set(v___x_4970_, 0, v___x_4972_);
v___x_4975_ = v___x_4970_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4972_);
lean_ctor_set(v_reuseFailAlloc_4977_, 1, v_nextMacroScope_4961_);
lean_ctor_set(v_reuseFailAlloc_4977_, 2, v_ngen_4962_);
lean_ctor_set(v_reuseFailAlloc_4977_, 3, v_auxDeclNGen_4963_);
lean_ctor_set(v_reuseFailAlloc_4977_, 4, v_traceState_4964_);
lean_ctor_set(v_reuseFailAlloc_4977_, 5, v___x_4973_);
lean_ctor_set(v_reuseFailAlloc_4977_, 6, v_recordedDeps_4965_);
lean_ctor_set(v_reuseFailAlloc_4977_, 7, v_messages_4966_);
lean_ctor_set(v_reuseFailAlloc_4977_, 8, v_infoState_4967_);
lean_ctor_set(v_reuseFailAlloc_4977_, 9, v_snapshotTasks_4968_);
v___x_4975_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
lean_object* v___x_4976_; 
v___x_4976_ = lean_st_ref_put(v___y_4914_, v___x_4975_);
lean_inc_ref(v_inheritedTraceOptions_4954_);
lean_inc(v_cancelTk_x3f_4953_);
lean_inc(v_currMacroScope_4952_);
lean_inc(v_quotContext_4951_);
lean_inc(v_maxHeartbeats_4950_);
lean_inc(v_initHeartbeats_4949_);
lean_inc(v_openDecls_4948_);
lean_inc(v_currNamespace_4947_);
lean_inc_ref(v_fileMap_4945_);
lean_inc_ref(v_fileName_4944_);
v___y_4917_ = v___y_4957_;
v___y_4918_ = v___y_4958_;
v_fileName_4919_ = v_fileName_4944_;
v_fileMap_4920_ = v_fileMap_4945_;
v_currNamespace_4921_ = v_currNamespace_4947_;
v_openDecls_4922_ = v_openDecls_4948_;
v_initHeartbeats_4923_ = v_initHeartbeats_4949_;
v_maxHeartbeats_4924_ = v_maxHeartbeats_4950_;
v_quotContext_4925_ = v_quotContext_4951_;
v_currMacroScope_4926_ = v_currMacroScope_4952_;
v_cancelTk_x3f_4927_ = v_cancelTk_x3f_4953_;
v_inheritedTraceOptions_4928_ = v_inheritedTraceOptions_4954_;
v_currRecDepth_4929_ = v_currRecDepth_4940_;
v_ref_4930_ = v_ref_4941_;
v_suppressElabErrors_4931_ = v_suppressElabErrors_4942_;
v_isRecordingDeps_4932_ = v_isRecordingDeps_4943_;
v___y_4933_ = v___y_4914_;
goto v___jp_4916_;
}
}
}
v___jp_4980_:
{
uint16_t v___x_4982_; lean_object* v___x_4983_; lean_object* v_env_4984_; uint8_t v___x_4985_; uint16_t v___x_4986_; uint16_t v___x_4987_; uint16_t v___x_4988_; uint8_t v___x_4989_; 
v___x_4982_ = l_Lean_OptionFlags_ofOptions(v___y_4981_);
v___x_4983_ = lean_st_ref_get(v___y_4914_);
v_env_4984_ = lean_ctor_get(v___x_4983_, 0);
lean_inc_ref(v_env_4984_);
lean_dec(v___x_4983_);
v___x_4985_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4984_);
lean_dec_ref(v_env_4984_);
v___x_4986_ = 512;
v___x_4987_ = lean_uint16_land(v___x_4982_, v___x_4986_);
v___x_4988_ = 0;
v___x_4989_ = lean_uint16_dec_eq(v___x_4987_, v___x_4988_);
if (v___x_4989_ == 0)
{
if (v___x_4985_ == 0)
{
v___y_4956_ = v___x_4909_;
v___y_4957_ = v___y_4981_;
v___y_4958_ = v___x_4982_;
goto v___jp_4955_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_4954_);
lean_inc(v_cancelTk_x3f_4953_);
lean_inc(v_currMacroScope_4952_);
lean_inc(v_quotContext_4951_);
lean_inc(v_maxHeartbeats_4950_);
lean_inc(v_initHeartbeats_4949_);
lean_inc(v_openDecls_4948_);
lean_inc(v_currNamespace_4947_);
lean_inc_ref(v_fileMap_4945_);
lean_inc_ref(v_fileName_4944_);
v___y_4917_ = v___y_4981_;
v___y_4918_ = v___x_4982_;
v_fileName_4919_ = v_fileName_4944_;
v_fileMap_4920_ = v_fileMap_4945_;
v_currNamespace_4921_ = v_currNamespace_4947_;
v_openDecls_4922_ = v_openDecls_4948_;
v_initHeartbeats_4923_ = v_initHeartbeats_4949_;
v_maxHeartbeats_4924_ = v_maxHeartbeats_4950_;
v_quotContext_4925_ = v_quotContext_4951_;
v_currMacroScope_4926_ = v_currMacroScope_4952_;
v_cancelTk_x3f_4927_ = v_cancelTk_x3f_4953_;
v_inheritedTraceOptions_4928_ = v_inheritedTraceOptions_4954_;
v_currRecDepth_4929_ = v_currRecDepth_4940_;
v_ref_4930_ = v_ref_4941_;
v_suppressElabErrors_4931_ = v_suppressElabErrors_4942_;
v_isRecordingDeps_4932_ = v_isRecordingDeps_4943_;
v___y_4933_ = v___y_4914_;
goto v___jp_4916_;
}
}
else
{
if (v___x_4985_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_4954_);
lean_inc(v_cancelTk_x3f_4953_);
lean_inc(v_currMacroScope_4952_);
lean_inc(v_quotContext_4951_);
lean_inc(v_maxHeartbeats_4950_);
lean_inc(v_initHeartbeats_4949_);
lean_inc(v_openDecls_4948_);
lean_inc(v_currNamespace_4947_);
lean_inc_ref(v_fileMap_4945_);
lean_inc_ref(v_fileName_4944_);
v___y_4917_ = v___y_4981_;
v___y_4918_ = v___x_4982_;
v_fileName_4919_ = v_fileName_4944_;
v_fileMap_4920_ = v_fileMap_4945_;
v_currNamespace_4921_ = v_currNamespace_4947_;
v_openDecls_4922_ = v_openDecls_4948_;
v_initHeartbeats_4923_ = v_initHeartbeats_4949_;
v_maxHeartbeats_4924_ = v_maxHeartbeats_4950_;
v_quotContext_4925_ = v_quotContext_4951_;
v_currMacroScope_4926_ = v_currMacroScope_4952_;
v_cancelTk_x3f_4927_ = v_cancelTk_x3f_4953_;
v_inheritedTraceOptions_4928_ = v_inheritedTraceOptions_4954_;
v_currRecDepth_4929_ = v_currRecDepth_4940_;
v_ref_4930_ = v_ref_4941_;
v_suppressElabErrors_4931_ = v_suppressElabErrors_4942_;
v_isRecordingDeps_4932_ = v_isRecordingDeps_4943_;
v___y_4933_ = v___y_4914_;
goto v___jp_4916_;
}
else
{
v___y_4956_ = v___x_4910_;
v___y_4957_ = v___y_4981_;
v___y_4958_ = v___x_4982_;
goto v___jp_4955_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_mkUnfoldEq___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4908_ = stack[0].m_obj;
uint8_t v___x_4909_ = stack[1].m_num;
uint8_t v___x_4910_ = stack[2].m_num;
lean_object* v___y_4911_ = stack[3].m_obj;
lean_object* v___y_4912_ = stack[4].m_obj;
lean_object* v___y_4913_ = stack[5].m_obj;
lean_object* v___y_4914_ = stack[6].m_obj;
lean_object* v_res_4993_;
v_res_4993_ = l_Lean_Elab_WF_mkUnfoldEq___lam__2(v___x_4908_, v___x_4909_, v___x_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_);
stack->m_obj
 = v_res_4993_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object* v___x_4994_, lean_object* v___x_4995_, lean_object* v___x_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_){
_start:
{
uint8_t v___x_10221__boxed_5002_; uint8_t v___x_10222__boxed_5003_; lean_object* v_res_5004_; 
v___x_10221__boxed_5002_ = lean_unbox(v___x_4995_);
v___x_10222__boxed_5003_ = lean_unbox(v___x_4996_);
v_res_5004_ = l_Lean_Elab_WF_mkUnfoldEq___lam__2(v___x_4994_, v___x_10221__boxed_5002_, v___x_10222__boxed_5003_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
lean_dec(v___y_5000_);
lean_dec_ref(v___y_4999_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
return v_res_5004_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5006_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___closed__0));
v___x_5007_ = l_Lean_stringToMessageData(v___x_5006_);
return v___x_5007_;
}
}
lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object* v_preDef_5008_, lean_object* v_unaryPreDefName_5009_, lean_object* v_wfPreprocessProof_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v___x_5016_; lean_object* v_env_5017_; lean_object* v_levelParams_5018_; lean_object* v_declName_5019_; lean_object* v_value_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___f_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___f_5027_; uint8_t v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; uint8_t v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___f_5034_; lean_object* v___x_5035_; 
v___x_5016_ = lean_st_ref_get(v_a_5014_);
v_env_5017_ = lean_ctor_get(v___x_5016_, 0);
lean_inc_ref(v_env_5017_);
lean_dec(v___x_5016_);
v_levelParams_5018_ = lean_ctor_get(v_preDef_5008_, 1);
lean_inc(v_levelParams_5018_);
v_declName_5019_ = lean_ctor_get(v_preDef_5008_, 3);
lean_inc_n(v_declName_5019_, 2);
v_value_5020_ = lean_ctor_get(v_preDef_5008_, 7);
lean_inc_ref(v_value_5020_);
lean_dec_ref(v_preDef_5008_);
v___x_5021_ = l_Lean_Meta_unfoldThmSuffix;
v___x_5022_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5017_, v_declName_5019_, v___x_5021_);
lean_inc(v___x_5022_);
v___f_5023_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5023_, 0, v_levelParams_5018_);
lean_closure_set(v___f_5023_, 1, v_declName_5019_);
lean_closure_set(v___f_5023_, 2, v_wfPreprocessProof_5010_);
lean_closure_set(v___f_5023_, 3, v___x_5022_);
lean_closure_set(v___f_5023_, 4, v_unaryPreDefName_5009_);
v___x_5024_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___closed__1, &l_Lean_Elab_WF_mkUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1);
v___x_5025_ = l_Lean_MessageData_ofName(v___x_5022_);
v___x_5026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5024_);
lean_ctor_set(v___x_5026_, 1, v___x_5025_);
v___f_5027_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_5027_, 0, v___x_5026_);
v___x_5028_ = 0;
v___x_5029_ = lean_box(v___x_5028_);
v___x_5030_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___boxed), 9, 4);
lean_closure_set(v___x_5030_, 0, lean_box(0));
lean_closure_set(v___x_5030_, 1, v_value_5020_);
lean_closure_set(v___x_5030_, 2, v___f_5023_);
lean_closure_set(v___x_5030_, 3, v___x_5029_);
v___x_5031_ = 1;
v___x_5032_ = lean_box(v___x_5031_);
v___x_5033_ = lean_box(v___x_5028_);
v___f_5034_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_5034_, 0, v___x_5030_);
lean_closure_set(v___f_5034_, 1, v___x_5032_);
lean_closure_set(v___f_5034_, 2, v___x_5033_);
v___x_5035_ = l_Lean_Meta_mapErrorImp___redArg(v___f_5034_, v___f_5027_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
if (lean_obj_tag(v___x_5035_) == 0)
{
lean_object* v_a_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5043_; 
v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5038_ = v___x_5035_;
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_a_5036_);
lean_dec(v___x_5035_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5041_; 
if (v_isShared_5039_ == 0)
{
v___x_5041_ = v___x_5038_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_a_5036_);
v___x_5041_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
return v___x_5041_;
}
}
}
else
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5051_; 
v_a_5044_ = lean_ctor_get(v___x_5035_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5046_ = v___x_5035_;
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___x_5035_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5049_; 
if (v_isShared_5047_ == 0)
{
v___x_5049_ = v___x_5046_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_mkUnfoldEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDef_5008_ = stack[0].m_obj;
lean_object* v_unaryPreDefName_5009_ = stack[1].m_obj;
lean_object* v_wfPreprocessProof_5010_ = stack[2].m_obj;
lean_object* v_a_5011_ = stack[3].m_obj;
lean_object* v_a_5012_ = stack[4].m_obj;
lean_object* v_a_5013_ = stack[5].m_obj;
lean_object* v_a_5014_ = stack[6].m_obj;
lean_object* v_res_5052_;
v_res_5052_ = l_Lean_Elab_WF_mkUnfoldEq(v_preDef_5008_, v_unaryPreDefName_5009_, v_wfPreprocessProof_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
stack->m_obj
 = v_res_5052_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___boxed(lean_object* v_preDef_5053_, lean_object* v_unaryPreDefName_5054_, lean_object* v_wfPreprocessProof_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Lean_Elab_WF_mkUnfoldEq(v_preDef_5053_, v_unaryPreDefName_5054_, v_wfPreprocessProof_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_);
lean_dec(v_a_5059_);
lean_dec_ref(v_a_5058_);
lean_dec(v_a_5057_);
lean_dec_ref(v_a_5056_);
return v_res_5061_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(lean_object* v_00_u03b1_5062_, lean_object* v_x_5063_, uint8_t v_isExporting_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_){
_start:
{
lean_object* v___x_5070_; 
v___x_5070_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg(v_x_5063_, v_isExporting_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
return v___x_5070_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5063_ = stack[1].m_obj;
uint8_t v_isExporting_5064_ = stack[2].m_num;
lean_object* v___y_5065_ = stack[3].m_obj;
lean_object* v___y_5066_ = stack[4].m_obj;
lean_object* v___y_5067_ = stack[5].m_obj;
lean_object* v___y_5068_ = stack[6].m_obj;
lean_object* v_res_5071_;
v_res_5071_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(lean_box(0), v_x_5063_, v_isExporting_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
stack->m_obj
 = v_res_5071_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___boxed(lean_object* v_00_u03b1_5072_, lean_object* v_x_5073_, lean_object* v_isExporting_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_){
_start:
{
uint8_t v_isExporting_boxed_5080_; lean_object* v_res_5081_; 
v_isExporting_boxed_5080_ = lean_unbox(v_isExporting_5074_);
v_res_5081_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3(v_00_u03b1_5072_, v_x_5073_, v_isExporting_boxed_5080_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
return v_res_5081_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_object* v_00_u03b1_5082_, lean_object* v_x_5083_, uint8_t v_when_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_){
_start:
{
lean_object* v___x_5090_; 
v___x_5090_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___redArg(v_x_5083_, v_when_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
return v___x_5090_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5083_ = stack[1].m_obj;
uint8_t v_when_5084_ = stack[2].m_num;
lean_object* v___y_5085_ = stack[3].m_obj;
lean_object* v___y_5086_ = stack[4].m_obj;
lean_object* v___y_5087_ = stack[5].m_obj;
lean_object* v___y_5088_ = stack[6].m_obj;
lean_object* v_res_5091_;
v_res_5091_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(lean_box(0), v_x_5083_, v_when_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
stack->m_obj
 = v_res_5091_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3___boxed(lean_object* v_00_u03b1_5092_, lean_object* v_x_5093_, lean_object* v_when_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_){
_start:
{
uint8_t v_when_boxed_5100_; lean_object* v_res_5101_; 
v_when_boxed_5100_ = lean_unbox(v_when_5094_);
v_res_5101_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3(v_00_u03b1_5092_, v_x_5093_, v_when_boxed_5100_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_);
lean_dec(v___y_5098_);
lean_dec_ref(v___y_5097_);
lean_dec(v___y_5096_);
lean_dec_ref(v___y_5095_);
return v_res_5101_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5103_; lean_object* v___x_5104_; 
v___x_5103_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0));
v___x_5104_ = l_Lean_stringToMessageData(v___x_5103_);
return v___x_5104_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; 
v___x_5110_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3));
v___x_5111_ = l_Lean_stringToMessageData(v___x_5110_);
return v___x_5111_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6(void){
_start:
{
lean_object* v___x_5113_; lean_object* v___x_5114_; 
v___x_5113_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5));
v___x_5114_ = l_Lean_stringToMessageData(v___x_5113_);
return v___x_5114_;
}
}
lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object* v_levelParams_5115_, lean_object* v_declName_5116_, lean_object* v___x_5117_, lean_object* v___x_5118_, lean_object* v___x_5119_, lean_object* v_xs_5120_, lean_object* v_body_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; 
v___x_5130_ = lean_box(0);
lean_inc(v_levelParams_5115_);
v___x_5131_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__3(v_levelParams_5115_, v___x_5130_);
v___x_5132_ = l_Lean_mkConst(v_declName_5116_, v___x_5131_);
v___x_5133_ = l_Lean_mkAppN(v___x_5132_, v_xs_5120_);
v___x_5134_ = l_Lean_Meta_mkEq(v___x_5133_, v_body_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc_n(v_a_5135_, 2);
lean_dec_ref_known(v___x_5134_, 1);
v___x_5136_ = lean_box(0);
v___x_5137_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_5135_, v___x_5136_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v_a_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
v_a_5138_ = lean_ctor_get(v___x_5137_, 0);
lean_inc(v_a_5138_);
lean_dec_ref_known(v___x_5137_, 1);
v___x_5139_ = l_Lean_Expr_mvarId_x21(v_a_5138_);
v___x_5140_ = l_Lean_Elab_Eqns_deltaLHS(v___x_5139_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v_a_5141_; uint8_t v___x_5142_; uint8_t v___x_5143_; lean_object* v___y_5145_; lean_object* v___y_5146_; lean_object* v___y_5147_; lean_object* v___y_5148_; lean_object* v___x_5205_; lean_object* v___x_5206_; 
v_a_5141_ = lean_ctor_get(v___x_5140_, 0);
lean_inc_n(v_a_5141_, 2);
lean_dec_ref_known(v___x_5140_, 1);
v___x_5142_ = 1;
v___x_5143_ = 0;
v___x_5205_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2));
v___x_5206_ = l_Lean_MVarId_applyConst(v_a_5141_, v___x_5118_, v___x_5205_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5206_) == 0)
{
lean_object* v_a_5207_; uint8_t v___x_5208_; 
v_a_5207_ = lean_ctor_get(v___x_5206_, 0);
lean_inc(v_a_5207_);
lean_dec_ref_known(v___x_5206_, 1);
v___x_5208_ = l_List_isEmpty___redArg(v_a_5207_);
lean_dec(v_a_5207_);
if (v___x_5208_ == 0)
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; 
lean_dec(v_a_5138_);
lean_dec(v_a_5135_);
lean_dec(v___x_5117_);
lean_dec(v_levelParams_5115_);
v___x_5209_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4);
v___x_5210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5209_);
lean_ctor_set(v___x_5210_, 1, v___x_5119_);
v___x_5211_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6);
v___x_5212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5210_);
lean_ctor_set(v___x_5212_, 1, v___x_5211_);
v___x_5213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5213_, 0, v_a_5141_);
v___x_5214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5214_, 0, v___x_5212_);
lean_ctor_set(v___x_5214_, 1, v___x_5213_);
v___x_5215_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5216_, 0, v___x_5214_);
lean_ctor_set(v___x_5216_, 1, v___x_5215_);
v___x_5217_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq_spec__3___redArg(v___x_5216_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
return v___x_5217_;
}
else
{
lean_dec(v_a_5141_);
lean_dec_ref(v___x_5119_);
v___y_5145_ = v___y_5122_;
v___y_5146_ = v___y_5123_;
v___y_5147_ = v___y_5124_;
v___y_5148_ = v___y_5125_;
goto v___jp_5144_;
}
}
else
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
lean_dec(v_a_5141_);
lean_dec(v_a_5138_);
lean_dec(v_a_5135_);
lean_dec_ref(v___x_5119_);
lean_dec(v___x_5117_);
lean_dec(v_levelParams_5115_);
v_a_5218_ = lean_ctor_get(v___x_5206_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5206_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5220_ = v___x_5206_;
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5206_);
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
v___jp_5144_:
{
lean_object* v___x_5149_; lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5204_; 
v___x_5149_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher_spec__6___redArg(v_a_5138_, v___y_5146_);
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5152_ = v___x_5149_;
v_isShared_5153_ = v_isSharedCheck_5204_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_5149_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5204_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
uint8_t v___x_5154_; lean_object* v___x_5155_; 
v___x_5154_ = 1;
v___x_5155_ = l_Lean_Meta_mkForallFVars(v_xs_5120_, v_a_5135_, v___x_5143_, v___x_5142_, v___x_5142_, v___x_5154_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
if (lean_obj_tag(v___x_5155_) == 0)
{
lean_object* v_a_5156_; lean_object* v___x_5157_; 
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
lean_inc(v_a_5156_);
lean_dec_ref_known(v___x_5155_, 1);
v___x_5157_ = l_Lean_Meta_letToHave(v_a_5156_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
if (lean_obj_tag(v___x_5157_) == 0)
{
lean_object* v_a_5158_; lean_object* v___x_5159_; 
v_a_5158_ = lean_ctor_get(v___x_5157_, 0);
lean_inc(v_a_5158_);
lean_dec_ref_known(v___x_5157_, 1);
v___x_5159_ = l_Lean_Meta_mkLambdaFVars(v_xs_5120_, v_a_5150_, v___x_5143_, v___x_5142_, v___x_5143_, v___x_5142_, v___x_5154_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v_a_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5165_; 
v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc(v_a_5160_);
lean_dec_ref_known(v___x_5159_, 1);
lean_inc_n(v___x_5117_, 2);
v___x_5161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5117_);
lean_ctor_set(v___x_5161_, 1, v_levelParams_5115_);
lean_ctor_set(v___x_5161_, 2, v_a_5158_);
v___x_5162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5117_);
lean_ctor_set(v___x_5162_, 1, v___x_5130_);
v___x_5163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5163_, 0, v___x_5161_);
lean_ctor_set(v___x_5163_, 1, v_a_5160_);
lean_ctor_set(v___x_5163_, 2, v___x_5162_);
if (v_isShared_5153_ == 0)
{
lean_ctor_set_tag(v___x_5152_, 2);
lean_ctor_set(v___x_5152_, 0, v___x_5163_);
v___x_5165_ = v___x_5152_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v___x_5163_);
v___x_5165_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
lean_object* v___x_5166_; 
v___x_5166_ = l_Lean_addDecl(v___x_5165_, v___x_5143_, v___y_5147_, v___y_5148_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v___x_5167_; 
lean_dec_ref_known(v___x_5166_, 1);
lean_inc(v___x_5117_);
v___x_5167_ = l_Lean_inferDefEqAttr(v___x_5117_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_toCold_5168_; lean_object* v_options_5169_; uint8_t v_hasTrace_5170_; 
lean_dec_ref_known(v___x_5167_, 1);
v_toCold_5168_ = lean_ctor_get(v___y_5147_, 0);
v_options_5169_ = lean_ctor_get(v_toCold_5168_, 2);
v_hasTrace_5170_ = lean_ctor_get_uint8(v_options_5169_, sizeof(void*)*1);
if (v_hasTrace_5170_ == 0)
{
lean_dec(v___x_5117_);
goto v___jp_5127_;
}
else
{
lean_object* v_inheritedTraceOptions_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; uint8_t v___x_5174_; 
v_inheritedTraceOptions_5171_ = lean_ctor_get(v_toCold_5168_, 11);
v___x_5172_ = ((lean_object*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2));
v___x_5173_ = lean_obj_once(&l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5, &l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5_once, _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__5);
v___x_5174_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5171_, v_options_5169_, v___x_5173_);
if (v___x_5174_ == 0)
{
lean_dec(v___x_5117_);
goto v___jp_5127_;
}
else
{
lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; 
v___x_5175_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1);
v___x_5176_ = l_Lean_MessageData_ofConstName(v___x_5117_, v___x_5143_);
v___x_5177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5177_, 0, v___x_5175_);
lean_ctor_set(v___x_5177_, 1, v___x_5176_);
v___x_5178_ = l_Lean_addTrace___at___00Lean_Elab_WF_mkUnfoldEq_spec__0(v___x_5172_, v___x_5177_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
return v___x_5178_;
}
}
}
else
{
lean_dec(v___x_5117_);
return v___x_5167_;
}
}
else
{
lean_dec(v___x_5117_);
return v___x_5166_;
}
}
}
else
{
lean_object* v_a_5180_; lean_object* v___x_5182_; uint8_t v_isShared_5183_; uint8_t v_isSharedCheck_5187_; 
lean_dec(v_a_5158_);
lean_del_object(v___x_5152_);
lean_dec(v___x_5117_);
lean_dec(v_levelParams_5115_);
v_a_5180_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5187_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5187_ == 0)
{
v___x_5182_ = v___x_5159_;
v_isShared_5183_ = v_isSharedCheck_5187_;
goto v_resetjp_5181_;
}
else
{
lean_inc(v_a_5180_);
lean_dec(v___x_5159_);
v___x_5182_ = lean_box(0);
v_isShared_5183_ = v_isSharedCheck_5187_;
goto v_resetjp_5181_;
}
v_resetjp_5181_:
{
lean_object* v___x_5185_; 
if (v_isShared_5183_ == 0)
{
v___x_5185_ = v___x_5182_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5186_; 
v_reuseFailAlloc_5186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5186_, 0, v_a_5180_);
v___x_5185_ = v_reuseFailAlloc_5186_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
return v___x_5185_;
}
}
}
}
else
{
lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5195_; 
lean_del_object(v___x_5152_);
lean_dec(v_a_5150_);
lean_dec(v___x_5117_);
lean_dec(v_levelParams_5115_);
v_a_5188_ = lean_ctor_get(v___x_5157_, 0);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5157_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5190_ = v___x_5157_;
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_a_5188_);
lean_dec(v___x_5157_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5193_; 
if (v_isShared_5191_ == 0)
{
v___x_5193_ = v___x_5190_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_a_5188_);
v___x_5193_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
return v___x_5193_;
}
}
}
}
else
{
lean_object* v_a_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5203_; 
lean_del_object(v___x_5152_);
lean_dec(v_a_5150_);
lean_dec(v___x_5117_);
lean_dec(v_levelParams_5115_);
v_a_5196_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5198_ = v___x_5155_;
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_a_5196_);
lean_dec(v___x_5155_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5201_; 
if (v_isShared_5199_ == 0)
{
v___x_5201_ = v___x_5198_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_a_5196_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
}
}
else
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5233_; 
lean_dec(v_a_5138_);
lean_dec(v_a_5135_);
lean_dec_ref(v___x_5119_);
lean_dec(v___x_5118_);
lean_dec(v___x_5117_);
lean_dec(v_levelParams_5115_);
v_a_5226_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5228_ = v___x_5140_;
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5140_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5231_; 
if (v_isShared_5229_ == 0)
{
v___x_5231_ = v___x_5228_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
v___x_5231_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
return v___x_5231_;
}
}
}
}
else
{
lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5241_; 
lean_dec(v_a_5135_);
lean_dec_ref(v___x_5119_);
lean_dec(v___x_5118_);
lean_dec(v___x_5117_);
lean_dec(v_levelParams_5115_);
v_a_5234_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5241_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5236_ = v___x_5137_;
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_dec(v___x_5137_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5239_; 
if (v_isShared_5237_ == 0)
{
v___x_5239_ = v___x_5236_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5240_; 
v_reuseFailAlloc_5240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5240_, 0, v_a_5234_);
v___x_5239_ = v_reuseFailAlloc_5240_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
return v___x_5239_;
}
}
}
}
else
{
lean_object* v_a_5242_; lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5249_; 
lean_dec_ref(v___x_5119_);
lean_dec(v___x_5118_);
lean_dec(v___x_5117_);
lean_dec(v_levelParams_5115_);
v_a_5242_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5244_ = v___x_5134_;
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
else
{
lean_inc(v_a_5242_);
lean_dec(v___x_5134_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5247_; 
if (v_isShared_5245_ == 0)
{
v___x_5247_ = v___x_5244_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5242_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
v___jp_5127_:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5128_ = lean_box(0);
v___x_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
return v___x_5129_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_levelParams_5115_ = stack[0].m_obj;
lean_object* v_declName_5116_ = stack[1].m_obj;
lean_object* v___x_5117_ = stack[2].m_obj;
lean_object* v___x_5118_ = stack[3].m_obj;
lean_object* v___x_5119_ = stack[4].m_obj;
lean_object* v_xs_5120_ = stack[5].m_obj;
lean_object* v_body_5121_ = stack[6].m_obj;
lean_object* v___y_5122_ = stack[7].m_obj;
lean_object* v___y_5123_ = stack[8].m_obj;
lean_object* v___y_5124_ = stack[9].m_obj;
lean_object* v___y_5125_ = stack[10].m_obj;
lean_object* v_res_5250_;
v_res_5250_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(v_levelParams_5115_, v_declName_5116_, v___x_5117_, v___x_5118_, v___x_5119_, v_xs_5120_, v_body_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
stack->m_obj
 = v_res_5250_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed(lean_object* v_levelParams_5251_, lean_object* v_declName_5252_, lean_object* v___x_5253_, lean_object* v___x_5254_, lean_object* v___x_5255_, lean_object* v_xs_5256_, lean_object* v_body_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_){
_start:
{
lean_object* v_res_5263_; 
v_res_5263_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(v_levelParams_5251_, v_declName_5252_, v___x_5253_, v___x_5254_, v___x_5255_, v_xs_5256_, v_body_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_dec_ref(v_xs_5256_);
return v_res_5263_;
}
}
lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(lean_object* v_value_5264_, lean_object* v___f_5265_, uint8_t v___x_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_){
_start:
{
uint16_t v___y_5273_; lean_object* v___y_5274_; lean_object* v_fileName_5275_; lean_object* v_fileMap_5276_; lean_object* v_currNamespace_5277_; lean_object* v_openDecls_5278_; lean_object* v_initHeartbeats_5279_; lean_object* v_maxHeartbeats_5280_; lean_object* v_quotContext_5281_; lean_object* v_currMacroScope_5282_; lean_object* v_cancelTk_x3f_5283_; lean_object* v_inheritedTraceOptions_5284_; lean_object* v_currRecDepth_5285_; lean_object* v_ref_5286_; uint8_t v_suppressElabErrors_5287_; uint8_t v_isRecordingDeps_5288_; lean_object* v___y_5289_; lean_object* v_toCold_5295_; lean_object* v_currRecDepth_5296_; lean_object* v_ref_5297_; uint8_t v_suppressElabErrors_5298_; uint8_t v_isRecordingDeps_5299_; lean_object* v_fileName_5300_; lean_object* v_fileMap_5301_; lean_object* v_options_5302_; lean_object* v_currNamespace_5303_; lean_object* v_openDecls_5304_; lean_object* v_initHeartbeats_5305_; lean_object* v_maxHeartbeats_5306_; lean_object* v_quotContext_5307_; lean_object* v_currMacroScope_5308_; lean_object* v_cancelTk_x3f_5309_; lean_object* v_inheritedTraceOptions_5310_; uint8_t v___y_5312_; uint16_t v___y_5313_; lean_object* v___y_5314_; lean_object* v___y_5337_; 
v_toCold_5295_ = lean_ctor_get(v___y_5269_, 0);
v_currRecDepth_5296_ = lean_ctor_get(v___y_5269_, 1);
v_ref_5297_ = lean_ctor_get(v___y_5269_, 2);
v_suppressElabErrors_5298_ = lean_ctor_get_uint8(v___y_5269_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5299_ = lean_ctor_get_uint8(v___y_5269_, sizeof(void*)*3 + 3);
v_fileName_5300_ = lean_ctor_get(v_toCold_5295_, 0);
v_fileMap_5301_ = lean_ctor_get(v_toCold_5295_, 1);
v_options_5302_ = lean_ctor_get(v_toCold_5295_, 2);
v_currNamespace_5303_ = lean_ctor_get(v_toCold_5295_, 4);
v_openDecls_5304_ = lean_ctor_get(v_toCold_5295_, 5);
v_initHeartbeats_5305_ = lean_ctor_get(v_toCold_5295_, 6);
v_maxHeartbeats_5306_ = lean_ctor_get(v_toCold_5295_, 7);
v_quotContext_5307_ = lean_ctor_get(v_toCold_5295_, 8);
v_currMacroScope_5308_ = lean_ctor_get(v_toCold_5295_, 9);
v_cancelTk_x3f_5309_ = lean_ctor_get(v_toCold_5295_, 10);
v_inheritedTraceOptions_5310_ = lean_ctor_get(v_toCold_5295_, 11);
if (v_isRecordingDeps_5299_ == 0)
{
lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5347_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_5302_);
v___x_5348_ = l_Lean_Option_set___at___00Lean_Elab_WF_mkUnfoldEq_spec__4(v_options_5302_, v___x_5347_, v_isRecordingDeps_5299_);
v___y_5337_ = v___x_5348_;
goto v___jp_5336_;
}
else
{
lean_object* v___x_5349_; 
lean_inc_ref(v_options_5302_);
v___x_5349_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_5302_);
v___y_5337_ = v___x_5349_;
goto v___jp_5336_;
}
v___jp_5272_:
{
lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5290_ = l_Lean_maxRecDepth;
v___x_5291_ = l_Lean_Option_get___at___00Lean_Elab_WF_mkUnfoldEq_spec__2(v___y_5274_, v___x_5290_);
v___x_5292_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_5292_, 0, v_fileName_5275_);
lean_ctor_set(v___x_5292_, 1, v_fileMap_5276_);
lean_ctor_set(v___x_5292_, 2, v___y_5274_);
lean_ctor_set(v___x_5292_, 3, v___x_5291_);
lean_ctor_set(v___x_5292_, 4, v_currNamespace_5277_);
lean_ctor_set(v___x_5292_, 5, v_openDecls_5278_);
lean_ctor_set(v___x_5292_, 6, v_initHeartbeats_5279_);
lean_ctor_set(v___x_5292_, 7, v_maxHeartbeats_5280_);
lean_ctor_set(v___x_5292_, 8, v_quotContext_5281_);
lean_ctor_set(v___x_5292_, 9, v_currMacroScope_5282_);
lean_ctor_set(v___x_5292_, 10, v_cancelTk_x3f_5283_);
lean_ctor_set(v___x_5292_, 11, v_inheritedTraceOptions_5284_);
lean_inc(v_ref_5286_);
lean_inc(v_currRecDepth_5285_);
v___x_5293_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
lean_ctor_set(v___x_5293_, 1, v_currRecDepth_5285_);
lean_ctor_set(v___x_5293_, 2, v_ref_5286_);
lean_ctor_set_uint16(v___x_5293_, sizeof(void*)*3, v___y_5273_);
lean_ctor_set_uint8(v___x_5293_, sizeof(void*)*3 + 2, v_suppressElabErrors_5287_);
lean_ctor_set_uint8(v___x_5293_, sizeof(void*)*3 + 3, v_isRecordingDeps_5288_);
v___x_5294_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_mkUnfoldEq_spec__1___redArg(v_value_5264_, v___f_5265_, v___x_5266_, v___y_5267_, v___y_5268_, v___x_5293_, v___y_5289_);
lean_dec_ref_known(v___x_5293_, 3);
return v___x_5294_;
}
v___jp_5311_:
{
lean_object* v___x_5315_; lean_object* v_env_5316_; lean_object* v_nextMacroScope_5317_; lean_object* v_ngen_5318_; lean_object* v_auxDeclNGen_5319_; lean_object* v_traceState_5320_; lean_object* v_recordedDeps_5321_; lean_object* v_messages_5322_; lean_object* v_infoState_5323_; lean_object* v_snapshotTasks_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5334_; 
v___x_5315_ = lean_st_ref_take(v___y_5270_);
v_env_5316_ = lean_ctor_get(v___x_5315_, 0);
v_nextMacroScope_5317_ = lean_ctor_get(v___x_5315_, 1);
v_ngen_5318_ = lean_ctor_get(v___x_5315_, 2);
v_auxDeclNGen_5319_ = lean_ctor_get(v___x_5315_, 3);
v_traceState_5320_ = lean_ctor_get(v___x_5315_, 4);
v_recordedDeps_5321_ = lean_ctor_get(v___x_5315_, 6);
v_messages_5322_ = lean_ctor_get(v___x_5315_, 7);
v_infoState_5323_ = lean_ctor_get(v___x_5315_, 8);
v_snapshotTasks_5324_ = lean_ctor_get(v___x_5315_, 9);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5334_ == 0)
{
lean_object* v_unused_5335_; 
v_unused_5335_ = lean_ctor_get(v___x_5315_, 5);
lean_dec(v_unused_5335_);
v___x_5326_ = v___x_5315_;
v_isShared_5327_ = v_isSharedCheck_5334_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_snapshotTasks_5324_);
lean_inc(v_infoState_5323_);
lean_inc(v_messages_5322_);
lean_inc(v_recordedDeps_5321_);
lean_inc(v_traceState_5320_);
lean_inc(v_auxDeclNGen_5319_);
lean_inc(v_ngen_5318_);
lean_inc(v_nextMacroScope_5317_);
lean_inc(v_env_5316_);
lean_dec(v___x_5315_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5334_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5331_; 
v___x_5328_ = l_Lean_Kernel_enableDiag(v_env_5316_, v___y_5312_);
v___x_5329_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_mkUnfoldEq_spec__3_spec__3___redArg___closed__1);
if (v_isShared_5327_ == 0)
{
lean_ctor_set(v___x_5326_, 5, v___x_5329_);
lean_ctor_set(v___x_5326_, 0, v___x_5328_);
v___x_5331_ = v___x_5326_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5328_);
lean_ctor_set(v_reuseFailAlloc_5333_, 1, v_nextMacroScope_5317_);
lean_ctor_set(v_reuseFailAlloc_5333_, 2, v_ngen_5318_);
lean_ctor_set(v_reuseFailAlloc_5333_, 3, v_auxDeclNGen_5319_);
lean_ctor_set(v_reuseFailAlloc_5333_, 4, v_traceState_5320_);
lean_ctor_set(v_reuseFailAlloc_5333_, 5, v___x_5329_);
lean_ctor_set(v_reuseFailAlloc_5333_, 6, v_recordedDeps_5321_);
lean_ctor_set(v_reuseFailAlloc_5333_, 7, v_messages_5322_);
lean_ctor_set(v_reuseFailAlloc_5333_, 8, v_infoState_5323_);
lean_ctor_set(v_reuseFailAlloc_5333_, 9, v_snapshotTasks_5324_);
v___x_5331_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
lean_object* v___x_5332_; 
v___x_5332_ = lean_st_ref_put(v___y_5270_, v___x_5331_);
lean_inc_ref(v_inheritedTraceOptions_5310_);
lean_inc(v_cancelTk_x3f_5309_);
lean_inc(v_currMacroScope_5308_);
lean_inc(v_quotContext_5307_);
lean_inc(v_maxHeartbeats_5306_);
lean_inc(v_initHeartbeats_5305_);
lean_inc(v_openDecls_5304_);
lean_inc(v_currNamespace_5303_);
lean_inc_ref(v_fileMap_5301_);
lean_inc_ref(v_fileName_5300_);
v___y_5273_ = v___y_5313_;
v___y_5274_ = v___y_5314_;
v_fileName_5275_ = v_fileName_5300_;
v_fileMap_5276_ = v_fileMap_5301_;
v_currNamespace_5277_ = v_currNamespace_5303_;
v_openDecls_5278_ = v_openDecls_5304_;
v_initHeartbeats_5279_ = v_initHeartbeats_5305_;
v_maxHeartbeats_5280_ = v_maxHeartbeats_5306_;
v_quotContext_5281_ = v_quotContext_5307_;
v_currMacroScope_5282_ = v_currMacroScope_5308_;
v_cancelTk_x3f_5283_ = v_cancelTk_x3f_5309_;
v_inheritedTraceOptions_5284_ = v_inheritedTraceOptions_5310_;
v_currRecDepth_5285_ = v_currRecDepth_5296_;
v_ref_5286_ = v_ref_5297_;
v_suppressElabErrors_5287_ = v_suppressElabErrors_5298_;
v_isRecordingDeps_5288_ = v_isRecordingDeps_5299_;
v___y_5289_ = v___y_5270_;
goto v___jp_5272_;
}
}
}
v___jp_5336_:
{
uint16_t v___x_5338_; lean_object* v___x_5339_; lean_object* v_env_5340_; uint8_t v___x_5341_; uint16_t v___x_5342_; uint16_t v___x_5343_; uint16_t v___x_5344_; uint8_t v___x_5345_; 
v___x_5338_ = l_Lean_OptionFlags_ofOptions(v___y_5337_);
v___x_5339_ = lean_st_ref_get(v___y_5270_);
v_env_5340_ = lean_ctor_get(v___x_5339_, 0);
lean_inc_ref(v_env_5340_);
lean_dec(v___x_5339_);
v___x_5341_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5340_);
lean_dec_ref(v_env_5340_);
v___x_5342_ = 512;
v___x_5343_ = lean_uint16_land(v___x_5338_, v___x_5342_);
v___x_5344_ = 0;
v___x_5345_ = lean_uint16_dec_eq(v___x_5343_, v___x_5344_);
if (v___x_5345_ == 0)
{
if (v___x_5341_ == 0)
{
uint8_t v___x_5346_; 
v___x_5346_ = 1;
v___y_5312_ = v___x_5346_;
v___y_5313_ = v___x_5338_;
v___y_5314_ = v___y_5337_;
goto v___jp_5311_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_5310_);
lean_inc(v_cancelTk_x3f_5309_);
lean_inc(v_currMacroScope_5308_);
lean_inc(v_quotContext_5307_);
lean_inc(v_maxHeartbeats_5306_);
lean_inc(v_initHeartbeats_5305_);
lean_inc(v_openDecls_5304_);
lean_inc(v_currNamespace_5303_);
lean_inc_ref(v_fileMap_5301_);
lean_inc_ref(v_fileName_5300_);
v___y_5273_ = v___x_5338_;
v___y_5274_ = v___y_5337_;
v_fileName_5275_ = v_fileName_5300_;
v_fileMap_5276_ = v_fileMap_5301_;
v_currNamespace_5277_ = v_currNamespace_5303_;
v_openDecls_5278_ = v_openDecls_5304_;
v_initHeartbeats_5279_ = v_initHeartbeats_5305_;
v_maxHeartbeats_5280_ = v_maxHeartbeats_5306_;
v_quotContext_5281_ = v_quotContext_5307_;
v_currMacroScope_5282_ = v_currMacroScope_5308_;
v_cancelTk_x3f_5283_ = v_cancelTk_x3f_5309_;
v_inheritedTraceOptions_5284_ = v_inheritedTraceOptions_5310_;
v_currRecDepth_5285_ = v_currRecDepth_5296_;
v_ref_5286_ = v_ref_5297_;
v_suppressElabErrors_5287_ = v_suppressElabErrors_5298_;
v_isRecordingDeps_5288_ = v_isRecordingDeps_5299_;
v___y_5289_ = v___y_5270_;
goto v___jp_5272_;
}
}
else
{
if (v___x_5341_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_5310_);
lean_inc(v_cancelTk_x3f_5309_);
lean_inc(v_currMacroScope_5308_);
lean_inc(v_quotContext_5307_);
lean_inc(v_maxHeartbeats_5306_);
lean_inc(v_initHeartbeats_5305_);
lean_inc(v_openDecls_5304_);
lean_inc(v_currNamespace_5303_);
lean_inc_ref(v_fileMap_5301_);
lean_inc_ref(v_fileName_5300_);
v___y_5273_ = v___x_5338_;
v___y_5274_ = v___y_5337_;
v_fileName_5275_ = v_fileName_5300_;
v_fileMap_5276_ = v_fileMap_5301_;
v_currNamespace_5277_ = v_currNamespace_5303_;
v_openDecls_5278_ = v_openDecls_5304_;
v_initHeartbeats_5279_ = v_initHeartbeats_5305_;
v_maxHeartbeats_5280_ = v_maxHeartbeats_5306_;
v_quotContext_5281_ = v_quotContext_5307_;
v_currMacroScope_5282_ = v_currMacroScope_5308_;
v_cancelTk_x3f_5283_ = v_cancelTk_x3f_5309_;
v_inheritedTraceOptions_5284_ = v_inheritedTraceOptions_5310_;
v_currRecDepth_5285_ = v_currRecDepth_5296_;
v_ref_5286_ = v_ref_5297_;
v_suppressElabErrors_5287_ = v_suppressElabErrors_5298_;
v_isRecordingDeps_5288_ = v_isRecordingDeps_5299_;
v___y_5289_ = v___y_5270_;
goto v___jp_5272_;
}
else
{
v___y_5312_ = v___x_5266_;
v___y_5313_ = v___x_5338_;
v___y_5314_ = v___y_5337_;
goto v___jp_5311_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_5264_ = stack[0].m_obj;
lean_object* v___f_5265_ = stack[1].m_obj;
uint8_t v___x_5266_ = stack[2].m_num;
lean_object* v___y_5267_ = stack[3].m_obj;
lean_object* v___y_5268_ = stack[4].m_obj;
lean_object* v___y_5269_ = stack[5].m_obj;
lean_object* v___y_5270_ = stack[6].m_obj;
lean_object* v_res_5350_;
v_res_5350_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(v_value_5264_, v___f_5265_, v___x_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
stack->m_obj
 = v_res_5350_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed(lean_object* v_value_5351_, lean_object* v___f_5352_, lean_object* v___x_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_){
_start:
{
uint8_t v___x_5451__boxed_5359_; lean_object* v_res_5360_; 
v___x_5451__boxed_5359_ = lean_unbox(v___x_5353_);
v_res_5360_ = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2(v_value_5351_, v___f_5352_, v___x_5451__boxed_5359_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_);
lean_dec(v___y_5357_);
lean_dec_ref(v___y_5356_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
return v_res_5360_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1(void){
_start:
{
lean_object* v___x_5362_; lean_object* v___x_5363_; 
v___x_5362_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0));
v___x_5363_ = l_Lean_stringToMessageData(v___x_5362_);
return v___x_5363_;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3(void){
_start:
{
lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___x_5365_ = ((lean_object*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__2));
v___x_5366_ = l_Lean_stringToMessageData(v___x_5365_);
return v___x_5366_;
}
}
lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object* v_preDef_5367_, lean_object* v_unaryPreDefName_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_){
_start:
{
lean_object* v___x_5374_; lean_object* v_env_5375_; lean_object* v_levelParams_5376_; lean_object* v_declName_5377_; lean_object* v_value_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v_env_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___f_5390_; lean_object* v___x_5391_; lean_object* v___f_5392_; uint8_t v___x_5393_; lean_object* v___x_5394_; lean_object* v___f_5395_; lean_object* v___x_5396_; 
v___x_5374_ = lean_st_ref_get(v_a_5372_);
v_env_5375_ = lean_ctor_get(v___x_5374_, 0);
lean_inc_ref(v_env_5375_);
lean_dec(v___x_5374_);
v_levelParams_5376_ = lean_ctor_get(v_preDef_5367_, 1);
lean_inc(v_levelParams_5376_);
v_declName_5377_ = lean_ctor_get(v_preDef_5367_, 3);
lean_inc_n(v_declName_5377_, 2);
v_value_5378_ = lean_ctor_get(v_preDef_5367_, 7);
lean_inc_ref(v_value_5378_);
lean_dec_ref(v_preDef_5367_);
v___x_5379_ = l_Lean_Meta_unfoldThmSuffix;
v___x_5380_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5375_, v_declName_5377_, v___x_5379_);
v___x_5381_ = lean_st_ref_get(v_a_5372_);
v_env_5382_ = lean_ctor_get(v___x_5381_, 0);
lean_inc_ref(v_env_5382_);
lean_dec(v___x_5381_);
v___x_5383_ = l_Lean_Meta_mkEqLikeNameFor(v_env_5382_, v_unaryPreDefName_5368_, v___x_5379_);
v___x_5384_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1);
lean_inc(v___x_5380_);
v___x_5385_ = l_Lean_MessageData_ofName(v___x_5380_);
v___x_5386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5386_, 0, v___x_5384_);
lean_ctor_set(v___x_5386_, 1, v___x_5385_);
v___x_5387_ = lean_obj_once(&l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3, &l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3_once, _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__3);
v___x_5388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5388_, 0, v___x_5386_);
lean_ctor_set(v___x_5388_, 1, v___x_5387_);
lean_inc(v___x_5383_);
v___x_5389_ = l_Lean_MessageData_ofName(v___x_5383_);
lean_inc_ref(v___x_5389_);
v___f_5390_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5390_, 0, v_levelParams_5376_);
lean_closure_set(v___f_5390_, 1, v_declName_5377_);
lean_closure_set(v___f_5390_, 2, v___x_5380_);
lean_closure_set(v___f_5390_, 3, v___x_5383_);
lean_closure_set(v___f_5390_, 4, v___x_5389_);
v___x_5391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5391_, 0, v___x_5388_);
lean_ctor_set(v___x_5391_, 1, v___x_5389_);
v___f_5392_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkMatchArgPusher___lam__11), 2, 1);
lean_closure_set(v___f_5392_, 0, v___x_5391_);
v___x_5393_ = 0;
v___x_5394_ = lean_box(v___x_5393_);
v___f_5395_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(v___f_5395_, 0, v_value_5378_);
lean_closure_set(v___f_5395_, 1, v___f_5390_);
lean_closure_set(v___f_5395_, 2, v___x_5394_);
v___x_5396_ = l_Lean_Meta_mapErrorImp___redArg(v___f_5395_, v___f_5392_, v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_);
if (lean_obj_tag(v___x_5396_) == 0)
{
lean_object* v_a_5397_; lean_object* v___x_5399_; uint8_t v_isShared_5400_; uint8_t v_isSharedCheck_5404_; 
v_a_5397_ = lean_ctor_get(v___x_5396_, 0);
v_isSharedCheck_5404_ = !lean_is_exclusive(v___x_5396_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5399_ = v___x_5396_;
v_isShared_5400_ = v_isSharedCheck_5404_;
goto v_resetjp_5398_;
}
else
{
lean_inc(v_a_5397_);
lean_dec(v___x_5396_);
v___x_5399_ = lean_box(0);
v_isShared_5400_ = v_isSharedCheck_5404_;
goto v_resetjp_5398_;
}
v_resetjp_5398_:
{
lean_object* v___x_5402_; 
if (v_isShared_5400_ == 0)
{
v___x_5402_ = v___x_5399_;
goto v_reusejp_5401_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_a_5397_);
v___x_5402_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5401_;
}
v_reusejp_5401_:
{
return v___x_5402_;
}
}
}
else
{
lean_object* v_a_5405_; lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5412_; 
v_a_5405_ = lean_ctor_get(v___x_5396_, 0);
v_isSharedCheck_5412_ = !lean_is_exclusive(v___x_5396_);
if (v_isSharedCheck_5412_ == 0)
{
v___x_5407_ = v___x_5396_;
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
else
{
lean_inc(v_a_5405_);
lean_dec(v___x_5396_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
lean_object* v___x_5410_; 
if (v_isShared_5408_ == 0)
{
v___x_5410_ = v___x_5407_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5411_; 
v_reuseFailAlloc_5411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_a_5405_);
v___x_5410_ = v_reuseFailAlloc_5411_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
return v___x_5410_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_mkBinaryUnfoldEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDef_5367_ = stack[0].m_obj;
lean_object* v_unaryPreDefName_5368_ = stack[1].m_obj;
lean_object* v_a_5369_ = stack[2].m_obj;
lean_object* v_a_5370_ = stack[3].m_obj;
lean_object* v_a_5371_ = stack[4].m_obj;
lean_object* v_a_5372_ = stack[5].m_obj;
lean_object* v_res_5413_;
v_res_5413_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_preDef_5367_, v_unaryPreDefName_5368_, v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_);
stack->m_obj
 = v_res_5413_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___boxed(lean_object* v_preDef_5414_, lean_object* v_unaryPreDefName_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_preDef_5414_, v_unaryPreDefName_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_);
lean_dec(v_a_5419_);
lean_dec_ref(v_a_5418_);
lean_dec(v_a_5417_);
lean_dec_ref(v_a_5416_);
return v_res_5421_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5466_; uint8_t v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5466_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5467_ = 0;
v___x_5468_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_));
v___x_5469_ = l_Lean_registerTraceClass(v___x_5466_, v___x_5467_, v___x_5468_);
return v___x_5469_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5470_;
v_res_5470_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5470_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2____boxed(lean_object* v_a_5471_){
_start:
{
lean_object* v_res_5472_; 
v_res_5472_ = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Unfold_417821031____hygCtx___hyg_2_();
return v_res_5472_;
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
