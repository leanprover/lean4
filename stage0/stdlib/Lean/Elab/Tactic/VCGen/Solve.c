// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.Solve
// Imports: public import Lean.Elab.Tactic.VCGen.Context public import Lean.Elab.Tactic.VCGen.RuleCache public import Lean.Elab.Tactic.VCGen.Entails public import Lean.Meta.Sym.InstantiateS public import Lean.Meta.Sym.Simp.App import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_match_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_introPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_prog(lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_FrameSplit_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_stripArgsN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorem_global_x3f(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc;
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_post(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_M(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Pred(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_findSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_outOfFuel_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_outOfFuel_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_untilPatternMatched_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_untilPatternMatched_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noEntailment_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noEntailment_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noProgress_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noProgress_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noSpecFound_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noSpecFound_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_goals_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_goals_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_stop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_stop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Failed to intro forall target "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 102, .m_capacity = 102, .m_length = 101, .m_data = "vcgen: shared-continuation handling for `__do_jp` is not yet implemented. Detection point reached at "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 205, .m_capacity = 205, .m_length = 204, .m_data = "; the upstream `Lean.Elab.Tactic.Do.onJoinPoint` (`src/Lean/Elab/Tactic/Do/VCGen.lean:215`) needs to be ported to the worklist style. Drop `(jp := true)` to fall back to the default zeta-unfold behaviour."};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(180, 190, 140, 210, 253, 78, 130, 238)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 104, 229, 54, 179, 197, 12, 87)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(49, 235, 69, 93, 100, 93, 190, 221)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let-intro: "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "let-zeta-dup: "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(190, 57, 218, 157, 42, 52, 8, 129)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 33, 148, 124, 218, 91, 248, 169)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__6;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "of_top_le_prop"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(112, 50, 129, 57, 86, 19, 237, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Solved by rfl "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Solved by lifted hypothesis "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "le_of_right"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 236, 244, 28, 139, 157, 99)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 127, 121, 224, 88, 246, 48, 72)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(114, 80, 184, 106, 225, 60, 114, 167)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 43, .m_data = "Failed to cancel the `⊓ ⊤` precondition of "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 160, 150, 32, 134, 96, 114, 42)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iSup"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 241, 153, 184, 251, 59, 2, 100)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Failed to eliminate the `iSup` precondition of "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Failed to apply "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "true_le_of_top_le"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 158, 62, 101, 253, 23, 66, 126)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " to"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Failed to intro hoisted let"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let-hoist: "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "split rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to apply split rule for "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fvar-zeta: "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "SpecProof.global "};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1;
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.local "};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3;
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.stx _ "};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5;
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "No spec applicable to program "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " in monad "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ". Candidates were "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "No spec found for program "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "`until` pattern matched program "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "; stopping"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_match__1_splitter(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`frames` matched "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "; frame:"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PreservesSup"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "upperAdjoint"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 52, 128, 160, 100, 147, 237, 166)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "frame rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "frame: split VC is not an entailment"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "frame: failed to apply rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "spec rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " for "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ". Excess args: "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Applying spec "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "`@[frameproc]` matched "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nerror: "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\ntarget:"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\nPred:"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\nexcessArgs: "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Failed to construct rule "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Failed to apply spec "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Failed to decompose weakest precondition for "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = ". This should not happen."};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 11, .m_data = "📜 Program: "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 10, .m_data = "🎯 Target: "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
default: 
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorIdx___boxed(lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorIdx(v_x_7_);
lean_dec(v_x_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(lean_object* v_t_9_, lean_object* v_k_10_){
_start:
{
switch(lean_obj_tag(v_t_9_))
{
case 0:
{
return v_k_10_;
}
case 3:
{
lean_object* v_pre_11_; lean_object* v_rhs_12_; lean_object* v___x_13_; 
v_pre_11_ = lean_ctor_get(v_t_9_, 0);
lean_inc_ref(v_pre_11_);
v_rhs_12_ = lean_ctor_get(v_t_9_, 1);
lean_inc_ref(v_rhs_12_);
lean_dec_ref_known(v_t_9_, 2);
v___x_13_ = lean_apply_2(v_k_10_, v_pre_11_, v_rhs_12_);
return v___x_13_;
}
case 4:
{
lean_object* v_e_14_; lean_object* v_monad_15_; lean_object* v_thms_16_; lean_object* v___x_17_; 
v_e_14_ = lean_ctor_get(v_t_9_, 0);
lean_inc_ref(v_e_14_);
v_monad_15_ = lean_ctor_get(v_t_9_, 1);
lean_inc_ref(v_monad_15_);
v_thms_16_ = lean_ctor_get(v_t_9_, 2);
lean_inc_ref(v_thms_16_);
lean_dec_ref_known(v_t_9_, 3);
v___x_17_ = lean_apply_3(v_k_10_, v_e_14_, v_monad_15_, v_thms_16_);
return v___x_17_;
}
default: 
{
lean_object* v_m_18_; lean_object* v___x_19_; 
v_m_18_ = lean_ctor_get(v_t_9_, 0);
lean_inc_ref(v_m_18_);
lean_dec(v_t_9_);
v___x_19_ = lean_apply_1(v_k_10_, v_m_18_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_22_, v_k_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___boxed(lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim(v_motive_26_, v_ctorIdx_27_, v_t_28_, v_h_29_, v_k_30_);
lean_dec(v_ctorIdx_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_outOfFuel_elim___redArg(lean_object* v_t_32_, lean_object* v_outOfFuel_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_32_, v_outOfFuel_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_outOfFuel_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_outOfFuel_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_36_, v_outOfFuel_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_untilPatternMatched_elim___redArg(lean_object* v_t_40_, lean_object* v_untilPatternMatched_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_40_, v_untilPatternMatched_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_untilPatternMatched_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_untilPatternMatched_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_44_, v_untilPatternMatched_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noEntailment_elim___redArg(lean_object* v_t_48_, lean_object* v_noEntailment_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_48_, v_noEntailment_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noEntailment_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_noEntailment_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_52_, v_noEntailment_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noProgress_elim___redArg(lean_object* v_t_56_, lean_object* v_noProgress_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_56_, v_noProgress_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noProgress_elim(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_noProgress_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_60_, v_noProgress_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noSpecFound_elim___redArg(lean_object* v_t_64_, lean_object* v_noSpecFound_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_64_, v_noSpecFound_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noSpecFound_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_noSpecFound_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_68_, v_noSpecFound_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorIdx(lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_object* v___x_73_; 
v___x_73_ = lean_unsigned_to_nat(0u);
return v___x_73_;
}
else
{
lean_object* v___x_74_; 
v___x_74_ = lean_unsigned_to_nat(1u);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorIdx___boxed(lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorIdx(v_x_75_);
lean_dec_ref(v_x_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(lean_object* v_t_77_, lean_object* v_k_78_){
_start:
{
if (lean_obj_tag(v_t_77_) == 0)
{
lean_object* v_scope_79_; lean_object* v_subgoals_80_; lean_object* v___x_81_; 
v_scope_79_ = lean_ctor_get(v_t_77_, 0);
lean_inc_ref(v_scope_79_);
v_subgoals_80_ = lean_ctor_get(v_t_77_, 1);
lean_inc(v_subgoals_80_);
lean_dec_ref_known(v_t_77_, 2);
v___x_81_ = lean_apply_2(v_k_78_, v_scope_79_, v_subgoals_80_);
return v___x_81_;
}
else
{
lean_object* v_reason_82_; lean_object* v___x_83_; 
v_reason_82_ = lean_ctor_get(v_t_77_, 0);
lean_inc(v_reason_82_);
lean_dec_ref_known(v_t_77_, 1);
v___x_83_ = lean_apply_1(v_k_78_, v_reason_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim(lean_object* v_motive_84_, lean_object* v_ctorIdx_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_k_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(v_t_86_, v_k_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___boxed(lean_object* v_motive_90_, lean_object* v_ctorIdx_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_k_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim(v_motive_90_, v_ctorIdx_91_, v_t_92_, v_h_93_, v_k_94_);
lean_dec(v_ctorIdx_91_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_goals_elim___redArg(lean_object* v_t_96_, lean_object* v_goals_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(v_t_96_, v_goals_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_goals_elim(lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_goals_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(v_t_100_, v_goals_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_stop_elim___redArg(lean_object* v_t_104_, lean_object* v_stop_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(v_t_104_, v_stop_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_stop_elim(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_stop_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(v_t_108_, v_stop_110_);
return v___x_111_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable(lean_object* v_e_117_){
_start:
{
switch(lean_obj_tag(v_e_117_))
{
case 5:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__2));
v___x_119_ = l_Lean_Expr_isAppOf(v_e_117_, v___x_118_);
return v___x_119_;
}
case 6:
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
case 7:
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
case 8:
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
case 10:
{
lean_object* v_expr_123_; 
v_expr_123_ = lean_ctor_get(v_e_117_, 1);
v_e_117_ = v_expr_123_;
goto _start;
}
case 11:
{
lean_object* v_struct_125_; 
v_struct_125_ = lean_ctor_get(v_e_117_, 2);
v_e_117_ = v_struct_125_;
goto _start;
}
default: 
{
uint8_t v___x_127_; 
v___x_127_ = 1;
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___boxed(lean_object* v_e_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable(v_e_128_);
lean_dec_ref(v_e_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg(lean_object* v_goal_131_, lean_object* v_target_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = l_Lean_Expr_isMData(v_target_132_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec(v_goal_131_);
v___x_139_ = lean_box(0);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = l_Lean_Expr_consumeMData(v_target_132_);
v___x_142_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_131_, v___x_141_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_151_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_151_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v_a_143_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_147_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_142_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_142_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg___boxed(lean_object* v_goal_160_, lean_object* v_target_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg(v_goal_160_, v_target_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec_ref(v_target_161_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f(lean_object* v_goal_168_, lean_object* v_target_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg(v_goal_168_, v_target_169_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___boxed(lean_object* v_goal_183_, lean_object* v_target_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f(v_goal_183_, v_target_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec_ref(v_target_184_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0_spec__0(lean_object* v_msgData_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; lean_object* v_env_205_; lean_object* v___x_206_; lean_object* v_mctx_207_; lean_object* v_lctx_208_; lean_object* v_options_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_204_ = lean_st_ref_get(v___y_202_);
v_env_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc_ref(v_env_205_);
lean_dec(v___x_204_);
v___x_206_ = lean_st_ref_get(v___y_200_);
v_mctx_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc_ref(v_mctx_207_);
lean_dec(v___x_206_);
v_lctx_208_ = lean_ctor_get(v___y_199_, 2);
v_options_209_ = lean_ctor_get(v___y_201_, 2);
lean_inc_ref(v_options_209_);
lean_inc_ref(v_lctx_208_);
v___x_210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_210_, 0, v_env_205_);
lean_ctor_set(v___x_210_, 1, v_mctx_207_);
lean_ctor_set(v___x_210_, 2, v_lctx_208_);
lean_ctor_set(v___x_210_, 3, v_options_209_);
v___x_211_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v_msgData_198_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0_spec__0(v_msgData_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(lean_object* v_msg_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_ref_226_; lean_object* v___x_227_; lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_236_; 
v_ref_226_ = lean_ctor_get(v___y_223_, 5);
v___x_227_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0_spec__0(v_msg_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_236_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
lean_inc(v_ref_226_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_ref_226_);
lean_ctor_set(v___x_232_, 1, v_a_228_);
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 1);
lean_ctor_set(v___x_230_, 0, v___x_232_);
v___x_234_ = v___x_230_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg___boxed(lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v_msg_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_243_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__1));
v___x_248_ = l_Lean_stringToMessageData(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f(lean_object* v_goal_251_, lean_object* v_target_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___y_266_; uint8_t v___x_271_; 
v___x_271_ = l_Lean_Expr_isForall(v_target_252_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v_goal_251_);
v___x_272_ = lean_box(0);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; 
lean_inc(v_goal_251_);
v___x_274_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_goal_251_, v_a_253_, v_a_254_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_325_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_325_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_325_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_325_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v_fst_280_; uint8_t v_snd_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; 
switch(lean_obj_tag(v_a_275_))
{
case 0:
{
uint8_t v___x_319_; 
lean_del_object(v___x_277_);
v___x_319_ = 0;
v_fst_280_ = v_goal_251_;
v_snd_281_ = v___x_319_;
v___y_282_ = v_a_253_;
v___y_283_ = v_a_254_;
v___y_284_ = v_a_255_;
v___y_285_ = v_a_256_;
v___y_286_ = v_a_257_;
v___y_287_ = v_a_258_;
v___y_288_ = v_a_259_;
v___y_289_ = v_a_260_;
v___y_290_ = v_a_261_;
v___y_291_ = v_a_262_;
v___y_292_ = v_a_263_;
goto v___jp_279_;
}
case 1:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
lean_dec(v_goal_251_);
v___x_320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_320_);
v___x_322_ = v___x_277_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
default: 
{
lean_object* v_mvarId_324_; 
lean_del_object(v___x_277_);
lean_dec(v_goal_251_);
v_mvarId_324_ = lean_ctor_get(v_a_275_, 0);
lean_inc(v_mvarId_324_);
lean_dec_ref_known(v_a_275_, 1);
v_fst_280_ = v_mvarId_324_;
v_snd_281_ = v___x_271_;
v___y_282_ = v_a_253_;
v___y_283_ = v_a_254_;
v___y_284_ = v_a_255_;
v___y_285_ = v_a_256_;
v___y_286_ = v_a_257_;
v___y_287_ = v_a_258_;
v___y_288_ = v_a_259_;
v___y_289_ = v_a_260_;
v___y_290_ = v_a_261_;
v___y_291_ = v_a_262_;
v___y_292_ = v_a_263_;
goto v___jp_279_;
}
}
v___jp_279_:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0));
lean_inc(v_fst_280_);
v___x_294_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_fst_280_, v___x_293_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_294_) == 0)
{
if (v_snd_281_ == 0)
{
if (v___x_271_ == 0)
{
lean_object* v_a_295_; 
lean_dec(v_fst_280_);
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v___y_266_ = v_a_295_;
goto v___jp_265_;
}
else
{
lean_object* v_a_296_; uint8_t v___x_297_; 
v_a_296_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_294_, 1);
v___x_297_ = l_Lean_instBEqMVarId_beq(v_a_296_, v_fst_280_);
if (v___x_297_ == 0)
{
lean_dec(v_fst_280_);
v___y_266_ = v_a_296_;
goto v___jp_265_;
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec(v_a_296_);
v___x_298_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v_fst_280_);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_300_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
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
lean_object* v_a_310_; 
lean_dec(v_fst_280_);
v_a_310_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_294_, 1);
v___y_266_ = v_a_310_;
goto v___jp_265_;
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec(v_fst_280_);
v_a_311_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_294_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_294_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec(v_goal_251_);
v_a_326_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_274_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_274_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
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
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
v___jp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_267_ = lean_box(0);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v___y_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___boxed(lean_object* v_goal_334_, lean_object* v_target_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f(v_goal_334_, v_target_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_target_335_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0(lean_object* v_00_u03b1_349_, lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v_msg_350_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___boxed(lean_object* v_00_u03b1_364_, lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0(v_00_u03b1_364_, v_msg_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_378_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__1(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__0));
v___x_381_ = l_Lean_stringToMessageData(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__3(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__2));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg(lean_object* v_name_385_, lean_object* v_val_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
uint8_t v_useJP_396_; 
v_useJP_396_ = lean_ctor_get_uint8(v_a_387_, sizeof(void*)*5 + 1);
if (v_useJP_396_ == 0)
{
lean_dec(v_name_385_);
goto v___jp_393_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = l_Lean_Elab_Tactic_Do_isJP(v_name_385_);
if (v___x_397_ == 0)
{
lean_dec(v_name_385_);
goto v___jp_393_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = l_Lean_Expr_isLambda(v_val_386_);
if (v___x_398_ == 0)
{
lean_dec(v_name_385_);
goto v___jp_393_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_399_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__1);
v___x_400_ = l_Lean_MessageData_ofName(v_name_385_);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___closed__3);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_403_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
return v___x_404_;
}
}
}
v___jp_393_:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_box(0);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg___boxed(lean_object* v_name_405_, lean_object* v_val_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg(v_name_405_, v_val_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec_ref(v_val_406_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP(lean_object* v_name_414_, lean_object* v_val_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg(v_name_414_, v_val_415_, v_a_416_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___boxed(lean_object* v_name_429_, lean_object* v_val_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP(v_name_429_, v_val_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v_val_430_);
return v_res_443_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_444_; double v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_float_of_nat(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(lean_object* v_cls_449_, lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_ref_456_; lean_object* v___x_457_; lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_502_; 
v_ref_456_ = lean_ctor_get(v___y_453_, 5);
v___x_457_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0_spec__0(v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_502_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_502_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_502_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v_traceState_463_; lean_object* v_env_464_; lean_object* v_nextMacroScope_465_; lean_object* v_ngen_466_; lean_object* v_auxDeclNGen_467_; lean_object* v_cache_468_; lean_object* v_messages_469_; lean_object* v_infoState_470_; lean_object* v_snapshotTasks_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_501_; 
v___x_462_ = lean_st_ref_take(v___y_454_);
v_traceState_463_ = lean_ctor_get(v___x_462_, 4);
v_env_464_ = lean_ctor_get(v___x_462_, 0);
v_nextMacroScope_465_ = lean_ctor_get(v___x_462_, 1);
v_ngen_466_ = lean_ctor_get(v___x_462_, 2);
v_auxDeclNGen_467_ = lean_ctor_get(v___x_462_, 3);
v_cache_468_ = lean_ctor_get(v___x_462_, 5);
v_messages_469_ = lean_ctor_get(v___x_462_, 6);
v_infoState_470_ = lean_ctor_get(v___x_462_, 7);
v_snapshotTasks_471_ = lean_ctor_get(v___x_462_, 8);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_501_ == 0)
{
v___x_473_ = v___x_462_;
v_isShared_474_ = v_isSharedCheck_501_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snapshotTasks_471_);
lean_inc(v_infoState_470_);
lean_inc(v_messages_469_);
lean_inc(v_cache_468_);
lean_inc(v_traceState_463_);
lean_inc(v_auxDeclNGen_467_);
lean_inc(v_ngen_466_);
lean_inc(v_nextMacroScope_465_);
lean_inc(v_env_464_);
lean_dec(v___x_462_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_501_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
uint64_t v_tid_475_; lean_object* v_traces_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_500_; 
v_tid_475_ = lean_ctor_get_uint64(v_traceState_463_, sizeof(void*)*1);
v_traces_476_ = lean_ctor_get(v_traceState_463_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v_traceState_463_);
if (v_isSharedCheck_500_ == 0)
{
v___x_478_ = v_traceState_463_;
v_isShared_479_ = v_isSharedCheck_500_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_traces_476_);
lean_dec(v_traceState_463_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_500_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; double v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_480_ = lean_box(0);
v___x_481_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0);
v___x_482_ = 0;
v___x_483_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__1));
v___x_484_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_484_, 0, v_cls_449_);
lean_ctor_set(v___x_484_, 1, v___x_480_);
lean_ctor_set(v___x_484_, 2, v___x_483_);
lean_ctor_set_float(v___x_484_, sizeof(void*)*3, v___x_481_);
lean_ctor_set_float(v___x_484_, sizeof(void*)*3 + 8, v___x_481_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*3 + 16, v___x_482_);
v___x_485_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__2));
v___x_486_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v_a_458_);
lean_ctor_set(v___x_486_, 2, v___x_485_);
lean_inc(v_ref_456_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_ref_456_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_PersistentArray_push___redArg(v_traces_476_, v___x_487_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_488_);
v___x_490_ = v___x_478_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_488_);
lean_ctor_set_uint64(v_reuseFailAlloc_499_, sizeof(void*)*1, v_tid_475_);
v___x_490_ = v_reuseFailAlloc_499_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v___x_490_);
v___x_492_ = v___x_473_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_env_464_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_nextMacroScope_465_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_ngen_466_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_auxDeclNGen_467_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_498_, 5, v_cache_468_);
lean_ctor_set(v_reuseFailAlloc_498_, 6, v_messages_469_);
lean_ctor_set(v_reuseFailAlloc_498_, 7, v_infoState_470_);
lean_ctor_set(v_reuseFailAlloc_498_, 8, v_snapshotTasks_471_);
v___x_492_ = v_reuseFailAlloc_498_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_493_ = lean_st_ref_put(v___y_454_, v___x_492_);
v___x_494_ = lean_box(0);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_494_);
v___x_496_ = v___x_460_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___boxed(lean_object* v_cls_503_, lean_object* v_msg_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_503_, v_msg_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
return v_res_510_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__6));
v___x_525_ = l_Lean_Name_append(v___x_524_, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__9(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__8));
v___x_528_ = l_Lean_stringToMessageData(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__10));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f(lean_object* v_goal_532_, lean_object* v_target_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; 
if (lean_obj_tag(v_target_533_) == 8)
{
lean_object* v_declName_577_; lean_object* v_value_578_; lean_object* v_body_579_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___x_618_; 
v_declName_577_ = lean_ctor_get(v_target_533_, 0);
lean_inc_n(v_declName_577_, 2);
v_value_578_ = lean_ctor_get(v_target_533_, 2);
lean_inc_ref(v_value_578_);
v_body_579_ = lean_ctor_get(v_target_533_, 3);
lean_inc_ref(v_body_579_);
lean_dec_ref_known(v_target_533_, 4);
v___x_618_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg(v_declName_577_, v_value_578_, v_a_534_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_618_) == 0)
{
uint8_t v___x_619_; 
lean_dec_ref_known(v___x_618_, 1);
v___x_619_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable(v_value_578_);
if (v___x_619_ == 0)
{
lean_object* v_options_620_; uint8_t v_hasTrace_621_; 
lean_dec_ref(v_body_579_);
lean_dec_ref(v_value_578_);
v_options_620_ = lean_ctor_get(v_a_543_, 2);
v_hasTrace_621_ = lean_ctor_get_uint8(v_options_620_, sizeof(void*)*1);
if (v_hasTrace_621_ == 0)
{
lean_dec(v_declName_577_);
v___y_547_ = v_a_534_;
v___y_548_ = v_a_535_;
v___y_549_ = v_a_536_;
v___y_550_ = v_a_537_;
v___y_551_ = v_a_538_;
v___y_552_ = v_a_539_;
v___y_553_ = v_a_540_;
v___y_554_ = v_a_541_;
v___y_555_ = v_a_542_;
v___y_556_ = v_a_543_;
v___y_557_ = v_a_544_;
goto v___jp_546_;
}
else
{
lean_object* v_inheritedTraceOptions_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_inheritedTraceOptions_622_ = lean_ctor_get(v_a_543_, 13);
v___x_623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_624_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_625_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_622_, v_options_620_, v___x_624_);
if (v___x_625_ == 0)
{
lean_dec(v_declName_577_);
v___y_547_ = v_a_534_;
v___y_548_ = v_a_535_;
v___y_549_ = v_a_536_;
v___y_550_ = v_a_537_;
v___y_551_ = v_a_538_;
v___y_552_ = v_a_539_;
v___y_553_ = v_a_540_;
v___y_554_ = v_a_541_;
v___y_555_ = v_a_542_;
v___y_556_ = v_a_543_;
v___y_557_ = v_a_544_;
goto v___jp_546_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_626_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__9, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__9);
v___x_627_ = l_Lean_MessageData_ofName(v_declName_577_);
v___x_628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_623_, v___x_628_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_dec_ref_known(v___x_629_, 1);
v___y_547_ = v_a_534_;
v___y_548_ = v_a_535_;
v___y_549_ = v_a_536_;
v___y_550_ = v_a_537_;
v___y_551_ = v_a_538_;
v___y_552_ = v_a_539_;
v___y_553_ = v_a_540_;
v___y_554_ = v_a_541_;
v___y_555_ = v_a_542_;
v___y_556_ = v_a_543_;
v___y_557_ = v_a_544_;
goto v___jp_546_;
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v_goal_532_);
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
}
else
{
lean_object* v_options_638_; uint8_t v_hasTrace_639_; 
v_options_638_ = lean_ctor_get(v_a_543_, 2);
v_hasTrace_639_ = lean_ctor_get_uint8(v_options_638_, sizeof(void*)*1);
if (v_hasTrace_639_ == 0)
{
lean_dec(v_declName_577_);
v___y_581_ = v_a_539_;
v___y_582_ = v_a_540_;
v___y_583_ = v_a_541_;
v___y_584_ = v_a_542_;
v___y_585_ = v_a_543_;
v___y_586_ = v_a_544_;
goto v___jp_580_;
}
else
{
lean_object* v_inheritedTraceOptions_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_inheritedTraceOptions_640_ = lean_ctor_get(v_a_543_, 13);
v___x_641_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_642_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_643_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_640_, v_options_638_, v___x_642_);
if (v___x_643_ == 0)
{
lean_dec(v_declName_577_);
v___y_581_ = v_a_539_;
v___y_582_ = v_a_540_;
v___y_583_ = v_a_541_;
v___y_584_ = v_a_542_;
v___y_585_ = v_a_543_;
v___y_586_ = v_a_544_;
goto v___jp_580_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_644_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11);
v___x_645_ = l_Lean_MessageData_ofName(v_declName_577_);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_641_, v___x_646_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec_ref_known(v___x_647_, 1);
v___y_581_ = v_a_539_;
v___y_582_ = v_a_540_;
v___y_583_ = v_a_541_;
v___y_584_ = v_a_542_;
v___y_585_ = v_a_543_;
v___y_586_ = v_a_544_;
goto v___jp_580_;
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v_body_579_);
lean_dec_ref(v_value_578_);
lean_dec(v_goal_532_);
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
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
lean_dec_ref(v_body_579_);
lean_dec_ref(v_value_578_);
lean_dec(v_declName_577_);
lean_dec(v_goal_532_);
v_a_656_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_618_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_618_);
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
v___jp_580_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
v___x_589_ = lean_array_push(v___x_588_, v_value_578_);
v___x_590_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_579_, v___x_589_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_532_, v_a_591_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_601_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_601_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_a_593_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_597_);
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_a_602_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_592_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_592_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_goal_532_);
v_a_610_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_590_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_590_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec_ref(v_target_533_);
lean_dec(v_goal_532_);
v___x_664_ = lean_box(0);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
v___jp_546_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0));
v___x_559_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_goal_532_, v___x_558_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_568_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_568_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v_a_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_566_ = v___x_562_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
v_a_569_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_559_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_559_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___boxed(lean_object* v_goal_666_, lean_object* v_target_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f(v_goal_666_, v_target_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0(lean_object* v_cls_681_, lean_object* v_msg_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_681_, v_msg_682_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___boxed(lean_object* v_cls_696_, lean_object* v_msg_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0(v_cls_696_, v_msg_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f(lean_object* v_goal_719_, lean_object* v_target_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3));
v___x_734_ = l_Lean_Expr_isAppOf(v_target_720_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec(v_goal_719_);
v___x_735_ = lean_box(0);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Elab_Tactic_VCGen_unfoldTriple(v_goal_719_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_746_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_746_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_a_738_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_a_747_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_737_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_737_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___boxed(lean_object* v_goal_755_, lean_object* v_target_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f(v_goal_755_, v_target_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec_ref(v_target_756_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
lean_object* v_ks_774_; lean_object* v_vs_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_799_; 
v_ks_774_ = lean_ctor_get(v_x_770_, 0);
v_vs_775_ = lean_ctor_get(v_x_770_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v_x_770_);
if (v_isSharedCheck_799_ == 0)
{
v___x_777_ = v_x_770_;
v_isShared_778_ = v_isSharedCheck_799_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_vs_775_);
lean_inc(v_ks_774_);
lean_dec(v_x_770_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_799_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = lean_array_get_size(v_ks_774_);
v___x_780_ = lean_nat_dec_lt(v_x_771_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
lean_dec(v_x_771_);
v___x_781_ = lean_array_push(v_ks_774_, v_x_772_);
v___x_782_ = lean_array_push(v_vs_775_, v_x_773_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_782_);
lean_ctor_set(v___x_777_, 0, v___x_781_);
v___x_784_ = v___x_777_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
else
{
lean_object* v_k_x27_786_; uint8_t v___x_787_; 
v_k_x27_786_ = lean_array_fget_borrowed(v_ks_774_, v_x_771_);
v___x_787_ = l_Lean_instBEqMVarId_beq(v_x_772_, v_k_x27_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_789_; 
if (v_isShared_778_ == 0)
{
v___x_789_ = v___x_777_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_ks_774_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_vs_775_);
v___x_789_ = v_reuseFailAlloc_793_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_add(v_x_771_, v___x_790_);
lean_dec(v_x_771_);
v_x_770_ = v___x_789_;
v_x_771_ = v___x_791_;
goto _start;
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_794_ = lean_array_fset(v_ks_774_, v_x_771_, v_x_772_);
v___x_795_ = lean_array_fset(v_vs_775_, v_x_771_, v_x_773_);
lean_dec(v_x_771_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_795_);
lean_ctor_set(v___x_777_, 0, v___x_794_);
v___x_797_ = v___x_777_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_800_, lean_object* v_k_801_, lean_object* v_v_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_800_, v___x_803_, v_k_801_, v_v_802_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_x_806_, size_t v_x_807_, size_t v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
if (lean_obj_tag(v_x_806_) == 0)
{
lean_object* v_es_811_; size_t v___x_812_; size_t v___x_813_; lean_object* v_j_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_es_811_ = lean_ctor_get(v_x_806_, 0);
v___x_812_ = ((size_t)31ULL);
v___x_813_ = lean_usize_land(v_x_807_, v___x_812_);
v_j_814_ = lean_usize_to_nat(v___x_813_);
v___x_815_ = lean_array_get_size(v_es_811_);
v___x_816_ = lean_nat_dec_lt(v_j_814_, v___x_815_);
if (v___x_816_ == 0)
{
lean_dec(v_j_814_);
lean_dec(v_x_810_);
lean_dec(v_x_809_);
return v_x_806_;
}
else
{
lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_855_; 
lean_inc_ref(v_es_811_);
v_isSharedCheck_855_ = !lean_is_exclusive(v_x_806_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; 
v_unused_856_ = lean_ctor_get(v_x_806_, 0);
lean_dec(v_unused_856_);
v___x_818_ = v_x_806_;
v_isShared_819_ = v_isSharedCheck_855_;
goto v_resetjp_817_;
}
else
{
lean_dec(v_x_806_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_855_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_v_820_; lean_object* v___x_821_; lean_object* v_xs_x27_822_; lean_object* v___y_824_; 
v_v_820_ = lean_array_fget(v_es_811_, v_j_814_);
v___x_821_ = lean_box(0);
v_xs_x27_822_ = lean_array_fset(v_es_811_, v_j_814_, v___x_821_);
switch(lean_obj_tag(v_v_820_))
{
case 0:
{
lean_object* v_key_829_; lean_object* v_val_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_840_; 
v_key_829_ = lean_ctor_get(v_v_820_, 0);
v_val_830_ = lean_ctor_get(v_v_820_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_v_820_);
if (v_isSharedCheck_840_ == 0)
{
v___x_832_ = v_v_820_;
v_isShared_833_ = v_isSharedCheck_840_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_val_830_);
lean_inc(v_key_829_);
lean_dec(v_v_820_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_840_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
uint8_t v___x_834_; 
v___x_834_ = l_Lean_instBEqMVarId_beq(v_x_809_, v_key_829_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_del_object(v___x_832_);
v___x_835_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_829_, v_val_830_, v_x_809_, v_x_810_);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
v___y_824_ = v___x_836_;
goto v___jp_823_;
}
else
{
lean_object* v___x_838_; 
lean_dec(v_val_830_);
lean_dec(v_key_829_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_x_810_);
lean_ctor_set(v___x_832_, 0, v_x_809_);
v___x_838_ = v___x_832_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_x_809_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_x_810_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
v___y_824_ = v___x_838_;
goto v___jp_823_;
}
}
}
}
case 1:
{
lean_object* v_node_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_853_; 
v_node_841_ = lean_ctor_get(v_v_820_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v_v_820_);
if (v_isSharedCheck_853_ == 0)
{
v___x_843_ = v_v_820_;
v_isShared_844_ = v_isSharedCheck_853_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_node_841_);
lean_dec(v_v_820_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_853_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
size_t v___x_845_; size_t v___x_846_; size_t v___x_847_; size_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_845_ = ((size_t)5ULL);
v___x_846_ = lean_usize_shift_right(v_x_807_, v___x_845_);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_add(v_x_808_, v___x_847_);
v___x_849_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_node_841_, v___x_846_, v___x_848_, v_x_809_, v_x_810_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_849_);
v___x_851_ = v___x_843_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
v___y_824_ = v___x_851_;
goto v___jp_823_;
}
}
}
default: 
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v_x_809_);
lean_ctor_set(v___x_854_, 1, v_x_810_);
v___y_824_ = v___x_854_;
goto v___jp_823_;
}
}
v___jp_823_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_array_fset(v_xs_x27_822_, v_j_814_, v___y_824_);
lean_dec(v_j_814_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_825_);
v___x_827_ = v___x_818_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
else
{
lean_object* v_ks_857_; lean_object* v_vs_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_878_; 
v_ks_857_ = lean_ctor_get(v_x_806_, 0);
v_vs_858_ = lean_ctor_get(v_x_806_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_x_806_);
if (v_isSharedCheck_878_ == 0)
{
v___x_860_ = v_x_806_;
v_isShared_861_ = v_isSharedCheck_878_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_vs_858_);
lean_inc(v_ks_857_);
lean_dec(v_x_806_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_878_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_ks_857_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_vs_858_);
v___x_863_ = v_reuseFailAlloc_877_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v_newNode_864_; uint8_t v___y_866_; size_t v___x_872_; uint8_t v___x_873_; 
v_newNode_864_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v___x_863_, v_x_809_, v_x_810_);
v___x_872_ = ((size_t)7ULL);
v___x_873_ = lean_usize_dec_le(v___x_872_, v_x_808_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_874_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_864_);
v___x_875_ = lean_unsigned_to_nat(4u);
v___x_876_ = lean_nat_dec_lt(v___x_874_, v___x_875_);
lean_dec(v___x_874_);
v___y_866_ = v___x_876_;
goto v___jp_865_;
}
else
{
v___y_866_ = v___x_873_;
goto v___jp_865_;
}
v___jp_865_:
{
if (v___y_866_ == 0)
{
lean_object* v_ks_867_; lean_object* v_vs_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_ks_867_ = lean_ctor_get(v_newNode_864_, 0);
lean_inc_ref(v_ks_867_);
v_vs_868_ = lean_ctor_get(v_newNode_864_, 1);
lean_inc_ref(v_vs_868_);
lean_dec_ref(v_newNode_864_);
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_871_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_x_808_, v_ks_867_, v_vs_868_, v___x_869_, v___x_870_);
lean_dec_ref(v_vs_868_);
lean_dec_ref(v_ks_867_);
return v___x_871_;
}
else
{
return v_newNode_864_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_879_, lean_object* v_keys_880_, lean_object* v_vals_881_, lean_object* v_i_882_, lean_object* v_entries_883_){
_start:
{
lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_884_ = lean_array_get_size(v_keys_880_);
v___x_885_ = lean_nat_dec_lt(v_i_882_, v___x_884_);
if (v___x_885_ == 0)
{
lean_dec(v_i_882_);
return v_entries_883_;
}
else
{
lean_object* v_k_886_; lean_object* v_v_887_; uint64_t v___x_888_; size_t v_h_889_; size_t v___x_890_; lean_object* v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; size_t v_h_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_k_886_ = lean_array_fget_borrowed(v_keys_880_, v_i_882_);
v_v_887_ = lean_array_fget_borrowed(v_vals_881_, v_i_882_);
v___x_888_ = l_Lean_instHashableMVarId_hash(v_k_886_);
v_h_889_ = lean_uint64_to_usize(v___x_888_);
v___x_890_ = ((size_t)5ULL);
v___x_891_ = lean_unsigned_to_nat(1u);
v___x_892_ = ((size_t)1ULL);
v___x_893_ = lean_usize_sub(v_depth_879_, v___x_892_);
v___x_894_ = lean_usize_mul(v___x_890_, v___x_893_);
v_h_895_ = lean_usize_shift_right(v_h_889_, v___x_894_);
v___x_896_ = lean_nat_add(v_i_882_, v___x_891_);
lean_dec(v_i_882_);
lean_inc(v_v_887_);
lean_inc(v_k_886_);
v___x_897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_entries_883_, v_h_895_, v_depth_879_, v_k_886_, v_v_887_);
v_i_882_ = v___x_896_;
v_entries_883_ = v___x_897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_899_, lean_object* v_keys_900_, lean_object* v_vals_901_, lean_object* v_i_902_, lean_object* v_entries_903_){
_start:
{
size_t v_depth_boxed_904_; lean_object* v_res_905_; 
v_depth_boxed_904_ = lean_unbox_usize(v_depth_899_);
lean_dec(v_depth_899_);
v_res_905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_904_, v_keys_900_, v_vals_901_, v_i_902_, v_entries_903_);
lean_dec_ref(v_vals_901_);
lean_dec_ref(v_keys_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
size_t v_x_8514__boxed_911_; size_t v_x_8515__boxed_912_; lean_object* v_res_913_; 
v_x_8514__boxed_911_ = lean_unbox_usize(v_x_907_);
lean_dec(v_x_907_);
v_x_8515__boxed_912_ = lean_unbox_usize(v_x_908_);
lean_dec(v_x_908_);
v_res_913_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_906_, v_x_8514__boxed_911_, v_x_8515__boxed_912_, v_x_909_, v_x_910_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
uint64_t v___x_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; 
v___x_917_ = l_Lean_instHashableMVarId_hash(v_x_915_);
v___x_918_ = lean_uint64_to_usize(v___x_917_);
v___x_919_ = ((size_t)1ULL);
v___x_920_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_914_, v___x_918_, v___x_919_, v_x_915_, v_x_916_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(lean_object* v_mvarId_921_, lean_object* v_val_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; lean_object* v_mctx_926_; lean_object* v_cache_927_; lean_object* v_zetaDeltaFVarIds_928_; lean_object* v_postponed_929_; lean_object* v_diag_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_958_; 
v___x_925_ = lean_st_ref_take(v___y_923_);
v_mctx_926_ = lean_ctor_get(v___x_925_, 0);
v_cache_927_ = lean_ctor_get(v___x_925_, 1);
v_zetaDeltaFVarIds_928_ = lean_ctor_get(v___x_925_, 2);
v_postponed_929_ = lean_ctor_get(v___x_925_, 3);
v_diag_930_ = lean_ctor_get(v___x_925_, 4);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_958_ == 0)
{
v___x_932_ = v___x_925_;
v_isShared_933_ = v_isSharedCheck_958_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_diag_930_);
lean_inc(v_postponed_929_);
lean_inc(v_zetaDeltaFVarIds_928_);
lean_inc(v_cache_927_);
lean_inc(v_mctx_926_);
lean_dec(v___x_925_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_958_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_depth_934_; lean_object* v_levelAssignDepth_935_; lean_object* v_lmvarCounter_936_; lean_object* v_mvarCounter_937_; lean_object* v_lDecls_938_; lean_object* v_decls_939_; lean_object* v_userNames_940_; lean_object* v_lAssignment_941_; lean_object* v_eAssignment_942_; lean_object* v_dAssignment_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_957_; 
v_depth_934_ = lean_ctor_get(v_mctx_926_, 0);
v_levelAssignDepth_935_ = lean_ctor_get(v_mctx_926_, 1);
v_lmvarCounter_936_ = lean_ctor_get(v_mctx_926_, 2);
v_mvarCounter_937_ = lean_ctor_get(v_mctx_926_, 3);
v_lDecls_938_ = lean_ctor_get(v_mctx_926_, 4);
v_decls_939_ = lean_ctor_get(v_mctx_926_, 5);
v_userNames_940_ = lean_ctor_get(v_mctx_926_, 6);
v_lAssignment_941_ = lean_ctor_get(v_mctx_926_, 7);
v_eAssignment_942_ = lean_ctor_get(v_mctx_926_, 8);
v_dAssignment_943_ = lean_ctor_get(v_mctx_926_, 9);
v_isSharedCheck_957_ = !lean_is_exclusive(v_mctx_926_);
if (v_isSharedCheck_957_ == 0)
{
v___x_945_ = v_mctx_926_;
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_dAssignment_943_);
lean_inc(v_eAssignment_942_);
lean_inc(v_lAssignment_941_);
lean_inc(v_userNames_940_);
lean_inc(v_decls_939_);
lean_inc(v_lDecls_938_);
lean_inc(v_mvarCounter_937_);
lean_inc(v_lmvarCounter_936_);
lean_inc(v_levelAssignDepth_935_);
lean_inc(v_depth_934_);
lean_dec(v_mctx_926_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_eAssignment_942_, v_mvarId_921_, v_val_922_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 8, v___x_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_depth_934_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_levelAssignDepth_935_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_lmvarCounter_936_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_mvarCounter_937_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v_lDecls_938_);
lean_ctor_set(v_reuseFailAlloc_956_, 5, v_decls_939_);
lean_ctor_set(v_reuseFailAlloc_956_, 6, v_userNames_940_);
lean_ctor_set(v_reuseFailAlloc_956_, 7, v_lAssignment_941_);
lean_ctor_set(v_reuseFailAlloc_956_, 8, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_956_, 9, v_dAssignment_943_);
v___x_949_ = v_reuseFailAlloc_956_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_949_);
v___x_951_ = v___x_932_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_cache_927_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_zetaDeltaFVarIds_928_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_postponed_929_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v_diag_930_);
v___x_951_ = v_reuseFailAlloc_955_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_st_ref_put(v___y_923_, v___x_951_);
v___x_953_ = lean_box(0);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_959_, lean_object* v_val_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_959_, v_val_960_, v___y_961_);
lean_dec(v___y_961_);
return v_res_963_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__4(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_unsigned_to_nat(0u);
v___x_972_ = l_Lean_Level_ofNat(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__4, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__4);
v___x_974_ = l_Lean_mkSort(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__6(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__5);
v___x_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__7(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_977_ = lean_box(0);
v___x_978_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__6, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__6_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__6);
v___x_979_ = lean_unsigned_to_nat(2u);
v___x_980_ = lean_mk_empty_array_with_capacity(v___x_979_);
v___x_981_ = lean_array_push(v___x_980_, v___x_978_);
v___x_982_ = lean_array_push(v___x_981_, v___x_977_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__13(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
v___x_996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__12));
v___x_997_ = l_Lean_mkConst(v___x_996_, v___x_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f(lean_object* v_goal_998_, lean_object* v_target_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; 
lean_inc_ref(v_target_999_);
v___x_1012_ = l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(v_target_999_);
if (lean_obj_tag(v___x_1012_) == 1)
{
lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1079_; 
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v___x_1012_, 0);
lean_dec(v_unused_1080_);
v___x_1014_ = v___x_1012_;
v_isShared_1015_ = v_isSharedCheck_1079_;
goto v_resetjp_1013_;
}
else
{
lean_dec(v___x_1012_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1079_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1016_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3));
v___x_1017_ = lean_unsigned_to_nat(2u);
v___x_1018_ = lean_mk_empty_array_with_capacity(v___x_1017_);
v___x_1019_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__7);
v___x_1020_ = l_Lean_Meta_mkAppOptM(v___x_1016_, v___x_1019_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10));
v___x_1023_ = lean_array_push(v___x_1018_, v_a_1021_);
lean_inc_ref(v_target_999_);
v___x_1024_ = lean_array_push(v___x_1023_, v_target_999_);
v___x_1025_ = l_Lean_Meta_mkAppM(v___x_1022_, v___x_1024_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = l_Lean_Meta_Sym_shareCommon(v_a_1026_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = lean_box(0);
v___x_1030_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1028_, v___x_1029_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1045_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc_n(v_a_1031_, 2);
lean_dec_ref_known(v___x_1030_, 1);
v___x_1032_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__13, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__13_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__13);
v___x_1033_ = l_Lean_mkAppB(v___x_1032_, v_target_999_, v_a_1031_);
v___x_1034_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_998_, v___x_1033_, v_a_1008_);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; 
v_unused_1046_ = lean_ctor_get(v___x_1034_, 0);
lean_dec(v_unused_1046_);
v___x_1036_ = v___x_1034_;
v_isShared_1037_ = v_isSharedCheck_1045_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v___x_1034_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1045_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1038_ = l_Lean_Expr_mvarId_x21(v_a_1031_);
lean_dec(v_a_1031_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1038_);
v___x_1040_ = v___x_1014_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1040_);
v___x_1042_ = v___x_1036_;
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
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_del_object(v___x_1014_);
lean_dec_ref(v_target_999_);
lean_dec(v_goal_998_);
v_a_1047_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1030_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1030_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_del_object(v___x_1014_);
lean_dec_ref(v_target_999_);
lean_dec(v_goal_998_);
v_a_1055_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1027_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1027_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_del_object(v___x_1014_);
lean_dec_ref(v_target_999_);
lean_dec(v_goal_998_);
v_a_1063_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1025_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1025_);
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
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec_ref(v___x_1018_);
lean_del_object(v___x_1014_);
lean_dec_ref(v_target_999_);
lean_dec(v_goal_998_);
v_a_1071_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1020_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1020_);
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
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec(v___x_1012_);
lean_dec_ref(v_target_999_);
lean_dec(v_goal_998_);
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___boxed(lean_object* v_goal_1083_, lean_object* v_target_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f(v_goal_1083_, v_target_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0(lean_object* v_mvarId_1098_, lean_object* v_val_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_1098_, v_val_1099_, v___y_1108_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___boxed(lean_object* v_mvarId_1113_, lean_object* v_val_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0(v_mvarId_1113_, v_val_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_x_1129_, v_x_1130_, v_x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, size_t v_x_1135_, size_t v_x_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_1134_, v_x_1135_, v_x_1136_, v_x_1137_, v_x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
size_t v_x_9024__boxed_1146_; size_t v_x_9025__boxed_1147_; lean_object* v_res_1148_; 
v_x_9024__boxed_1146_ = lean_unbox_usize(v_x_1142_);
lean_dec(v_x_1142_);
v_x_9025__boxed_1147_ = lean_unbox_usize(v_x_1143_);
lean_dec(v_x_1143_);
v_res_1148_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1140_, v_x_1141_, v_x_9024__boxed_1146_, v_x_9025__boxed_1147_, v_x_1144_, v_x_1145_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1149_, lean_object* v_n_1150_, lean_object* v_k_1151_, lean_object* v_v_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1150_, v_k_1151_, v_v_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1154_, size_t v_depth_1155_, lean_object* v_keys_1156_, lean_object* v_vals_1157_, lean_object* v_heq_1158_, lean_object* v_i_1159_, lean_object* v_entries_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1155_, v_keys_1156_, v_vals_1157_, v_i_1159_, v_entries_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1162_, lean_object* v_depth_1163_, lean_object* v_keys_1164_, lean_object* v_vals_1165_, lean_object* v_heq_1166_, lean_object* v_i_1167_, lean_object* v_entries_1168_){
_start:
{
size_t v_depth_boxed_1169_; lean_object* v_res_1170_; 
v_depth_boxed_1169_ = lean_unbox_usize(v_depth_1163_);
lean_dec(v_depth_1163_);
v_res_1170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1162_, v_depth_boxed_1169_, v_keys_1164_, v_vals_1165_, v_heq_1166_, v_i_1167_, v_entries_1168_);
lean_dec_ref(v_vals_1165_);
lean_dec_ref(v_keys_1164_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1172_, v_x_1173_, v_x_1174_, v_x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__0));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(lean_object* v_goal_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_backwardRules_1189_; lean_object* v_refl_1190_; lean_object* v___x_1191_; 
v_backwardRules_1189_ = lean_ctor_get(v_a_1181_, 0);
v_refl_1190_ = lean_ctor_get(v_backwardRules_1189_, 9);
lean_inc_ref(v_refl_1190_);
lean_inc(v_goal_1180_);
v___x_1191_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1180_, v_refl_1190_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1230_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1230_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1230_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
if (lean_obj_tag(v_a_1192_) == 1)
{
lean_object* v_mvarIds_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1225_; 
v_mvarIds_1196_ = lean_ctor_get(v_a_1192_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_a_1192_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1198_ = v_a_1192_;
v_isShared_1199_ = v_isSharedCheck_1225_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_mvarIds_1196_);
lean_dec(v_a_1192_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1225_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v_options_1207_; uint8_t v_hasTrace_1208_; 
v_options_1207_ = lean_ctor_get(v_a_1186_, 2);
v_hasTrace_1208_ = lean_ctor_get_uint8(v_options_1207_, sizeof(void*)*1);
if (v_hasTrace_1208_ == 0)
{
lean_dec(v_goal_1180_);
goto v___jp_1200_;
}
else
{
lean_object* v_inheritedTraceOptions_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_inheritedTraceOptions_1209_ = lean_ctor_get(v_a_1186_, 13);
v___x_1210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_1211_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_1212_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1209_, v_options_1207_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_dec(v_goal_1180_);
goto v___jp_1200_;
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1213_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1);
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_goal_1180_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1210_, v___x_1215_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_dec_ref_known(v___x_1216_, 1);
goto v___jp_1200_;
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_del_object(v___x_1198_);
lean_dec(v_mvarIds_1196_);
lean_del_object(v___x_1194_);
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
v___jp_1200_:
{
lean_object* v___x_1202_; 
if (v_isShared_1199_ == 0)
{
v___x_1202_ = v___x_1198_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_mvarIds_1196_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1202_);
v___x_1204_ = v___x_1194_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
lean_dec(v_a_1192_);
lean_dec(v_goal_1180_);
v___x_1226_ = lean_box(0);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1226_);
v___x_1228_ = v___x_1194_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_goal_1180_);
v_a_1231_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1191_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1191_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___boxed(lean_object* v_goal_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(v_goal_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec_ref(v_a_1240_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f(lean_object* v_goal_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(v_goal_1249_, v_a_1250_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___boxed(lean_object* v_goal_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f(v_goal_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
return v_res_1276_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__0));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(lean_object* v_scope_1280_, lean_object* v_e_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_lastLiftedPre_x3f_1287_; 
v_lastLiftedPre_x3f_1287_ = lean_ctor_get(v_scope_1280_, 2);
lean_inc(v_lastLiftedPre_x3f_1287_);
lean_dec_ref(v_scope_1280_);
if (lean_obj_tag(v_lastLiftedPre_x3f_1287_) == 1)
{
lean_object* v_val_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1345_; 
v_val_1288_ = lean_ctor_get(v_lastLiftedPre_x3f_1287_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_lastLiftedPre_x3f_1287_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1290_ = v_lastLiftedPre_x3f_1287_;
v_isShared_1291_ = v_isSharedCheck_1345_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_val_1288_);
lean_dec(v_lastLiftedPre_x3f_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1345_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_lctx_1292_; lean_object* v___x_1293_; 
v_lctx_1292_ = lean_ctor_get(v_a_1282_, 2);
lean_inc_ref(v_lctx_1292_);
v___x_1293_ = lean_local_ctx_find(v_lctx_1292_, v_val_1288_);
if (lean_obj_tag(v___x_1293_) == 1)
{
lean_object* v_val_1294_; lean_object* v___x_1295_; size_t v___x_1296_; size_t v___x_1297_; uint8_t v___x_1298_; 
v_val_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_val_1294_);
v___x_1295_ = l_Lean_LocalDecl_type(v_val_1294_);
v___x_1296_ = lean_ptr_addr(v_e_1281_);
v___x_1297_ = lean_ptr_addr(v___x_1295_);
lean_dec_ref(v___x_1295_);
v___x_1298_ = lean_usize_dec_eq(v___x_1296_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1306_; 
lean_dec(v_val_1294_);
lean_del_object(v___x_1290_);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v___x_1293_, 0);
lean_dec(v_unused_1307_);
v___x_1300_ = v___x_1293_;
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
else
{
lean_dec(v___x_1293_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = lean_box(0);
if (v_isShared_1301_ == 0)
{
lean_ctor_set_tag(v___x_1300_, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1302_);
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
else
{
lean_object* v_options_1308_; uint8_t v_hasTrace_1309_; 
v_options_1308_ = lean_ctor_get(v_a_1284_, 2);
v_hasTrace_1309_ = lean_ctor_get_uint8(v_options_1308_, sizeof(void*)*1);
if (v_hasTrace_1309_ == 0)
{
lean_object* v___x_1311_; 
lean_dec(v_val_1294_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1293_);
v___x_1311_ = v___x_1290_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1293_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
else
{
lean_object* v_inheritedTraceOptions_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_inheritedTraceOptions_1313_ = lean_ctor_get(v_a_1284_, 13);
v___x_1314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_1315_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_1316_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1313_, v_options_1308_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1318_; 
lean_dec(v_val_1294_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1293_);
v___x_1318_ = v___x_1290_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1293_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_del_object(v___x_1290_);
v___x_1320_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1);
v___x_1321_ = l_Lean_LocalDecl_userName(v_val_1294_);
lean_dec(v_val_1294_);
v___x_1322_ = l_Lean_MessageData_ofName(v___x_1321_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1320_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1314_, v___x_1323_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v___x_1324_, 0);
lean_dec(v_unused_1332_);
v___x_1326_ = v___x_1324_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v___x_1324_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1293_);
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1293_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref_known(v___x_1293_, 1);
v_a_1333_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1324_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1324_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
lean_dec(v___x_1293_);
v___x_1341_ = lean_box(0);
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1341_);
v___x_1343_ = v___x_1290_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec(v_lastLiftedPre_x3f_1287_);
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___boxed(lean_object* v_scope_1348_, lean_object* v_e_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_1348_, v_e_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec_ref(v_e_1349_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f(lean_object* v_scope_1356_, lean_object* v_e_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_1356_, v_e_1357_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___boxed(lean_object* v_scope_1371_, lean_object* v_e_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f(v_scope_1371_, v_e_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec_ref(v_e_1372_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(lean_object* v_x_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
lean_inc(v___y_1389_);
lean_inc(v___y_1388_);
lean_inc_ref(v___y_1387_);
v___x_1399_ = lean_apply_12(v_x_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, lean_box(0));
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(v_x_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(lean_object* v_mvarId_1414_, lean_object* v_x_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___f_1428_; lean_object* v___x_1429_; 
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
lean_inc(v___y_1420_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
v___f_1428_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1428_, 0, v_x_1415_);
lean_closure_set(v___f_1428_, 1, v___y_1416_);
lean_closure_set(v___f_1428_, 2, v___y_1417_);
lean_closure_set(v___f_1428_, 3, v___y_1418_);
lean_closure_set(v___f_1428_, 4, v___y_1419_);
lean_closure_set(v___f_1428_, 5, v___y_1420_);
lean_closure_set(v___f_1428_, 6, v___y_1421_);
lean_closure_set(v___f_1428_, 7, v___y_1422_);
v___x_1429_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1414_, v___f_1428_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1429_) == 0)
{
return v___x_1429_;
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_1438_, lean_object* v_x_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1438_, v_x_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0(lean_object* v_00_u03b1_1453_, lean_object* v_mvarId_1454_, lean_object* v_x_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1454_, v_x_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___boxed(lean_object* v_00_u03b1_1469_, lean_object* v_mvarId_1470_, lean_object* v_x_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0(v_00_u03b1_1469_, v_mvarId_1470_, v_x_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0(uint8_t v___x_1490_, lean_object* v_scope_1491_, lean_object* v_rhs_1492_, lean_object* v_pre_1493_, lean_object* v_goal_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
if (v___x_1490_ == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_dec(v_goal_1494_);
lean_dec_ref(v_pre_1493_);
lean_dec_ref(v_rhs_1492_);
lean_dec_ref(v_scope_1491_);
v___x_1507_ = lean_box(0);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
else
{
lean_object* v___x_1509_; 
v___x_1509_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_1491_, v_rhs_1492_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1546_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1546_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1546_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
if (lean_obj_tag(v_a_1510_) == 1)
{
lean_object* v_val_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_del_object(v___x_1512_);
v_val_1514_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_val_1514_);
lean_dec_ref_known(v_a_1510_, 1);
v___x_1515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1));
v___x_1516_ = l_Lean_LocalDecl_toExpr(v_val_1514_);
v___x_1517_ = lean_unsigned_to_nat(3u);
v___x_1518_ = lean_mk_empty_array_with_capacity(v___x_1517_);
v___x_1519_ = lean_array_push(v___x_1518_, v_pre_1493_);
v___x_1520_ = lean_array_push(v___x_1519_, v_rhs_1492_);
v___x_1521_ = lean_array_push(v___x_1520_, v___x_1516_);
v___x_1522_ = l_Lean_Meta_mkAppM(v___x_1515_, v___x_1521_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1532_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1494_, v_a_1523_, v___y_1503_);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v___x_1524_, 0);
lean_dec(v_unused_1533_);
v___x_1526_ = v___x_1524_;
v_isShared_1527_ = v_isSharedCheck_1532_;
goto v_resetjp_1525_;
}
else
{
lean_dec(v___x_1524_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1532_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1528_);
v___x_1530_ = v___x_1526_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v_goal_1494_);
v_a_1534_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1522_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1522_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
lean_dec(v_a_1510_);
lean_dec(v_goal_1494_);
lean_dec_ref(v_pre_1493_);
lean_dec_ref(v_rhs_1492_);
v___x_1542_ = lean_box(0);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1542_);
v___x_1544_ = v___x_1512_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
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
lean_dec(v_goal_1494_);
lean_dec_ref(v_pre_1493_);
lean_dec_ref(v_rhs_1492_);
v_a_1547_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1509_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1509_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___boxed(lean_object** _args){
lean_object* v___x_1555_ = _args[0];
lean_object* v_scope_1556_ = _args[1];
lean_object* v_rhs_1557_ = _args[2];
lean_object* v_pre_1558_ = _args[3];
lean_object* v_goal_1559_ = _args[4];
lean_object* v___y_1560_ = _args[5];
lean_object* v___y_1561_ = _args[6];
lean_object* v___y_1562_ = _args[7];
lean_object* v___y_1563_ = _args[8];
lean_object* v___y_1564_ = _args[9];
lean_object* v___y_1565_ = _args[10];
lean_object* v___y_1566_ = _args[11];
lean_object* v___y_1567_ = _args[12];
lean_object* v___y_1568_ = _args[13];
lean_object* v___y_1569_ = _args[14];
lean_object* v___y_1570_ = _args[15];
lean_object* v___y_1571_ = _args[16];
_start:
{
uint8_t v___x_7757__boxed_1572_; lean_object* v_res_1573_; 
v___x_7757__boxed_1572_ = lean_unbox(v___x_1555_);
v_res_1573_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0(v___x_7757__boxed_1572_, v_scope_1556_, v_rhs_1557_, v_pre_1558_, v_goal_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f(lean_object* v_scope_1574_, lean_object* v_goal_1575_, lean_object* v_00_u03b1_1576_, lean_object* v_pre_1577_, lean_object* v_rhs_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___y_1593_; lean_object* v___x_1594_; 
v___x_1591_ = l_Lean_Expr_isProp(v_00_u03b1_1576_);
v___x_1592_ = lean_box(v___x_1591_);
lean_inc(v_goal_1575_);
v___y_1593_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___boxed), 17, 5);
lean_closure_set(v___y_1593_, 0, v___x_1592_);
lean_closure_set(v___y_1593_, 1, v_scope_1574_);
lean_closure_set(v___y_1593_, 2, v_rhs_1578_);
lean_closure_set(v___y_1593_, 3, v_pre_1577_);
lean_closure_set(v___y_1593_, 4, v_goal_1575_);
v___x_1594_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1575_, v___y_1593_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___boxed(lean_object** _args){
lean_object* v_scope_1595_ = _args[0];
lean_object* v_goal_1596_ = _args[1];
lean_object* v_00_u03b1_1597_ = _args[2];
lean_object* v_pre_1598_ = _args[3];
lean_object* v_rhs_1599_ = _args[4];
lean_object* v_a_1600_ = _args[5];
lean_object* v_a_1601_ = _args[6];
lean_object* v_a_1602_ = _args[7];
lean_object* v_a_1603_ = _args[8];
lean_object* v_a_1604_ = _args[9];
lean_object* v_a_1605_ = _args[10];
lean_object* v_a_1606_ = _args[11];
lean_object* v_a_1607_ = _args[12];
lean_object* v_a_1608_ = _args[13];
lean_object* v_a_1609_ = _args[14];
lean_object* v_a_1610_ = _args[15];
lean_object* v_a_1611_ = _args[16];
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f(v_scope_1595_, v_goal_1596_, v_00_u03b1_1597_, v_pre_1598_, v_rhs_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec_ref(v_00_u03b1_1597_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0(lean_object* v_scope_1613_, lean_object* v_target_1614_, lean_object* v_goal_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_1613_, v_target_1614_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1649_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1649_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1649_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
if (lean_obj_tag(v_a_1629_) == 1)
{
lean_object* v_val_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1643_; 
lean_del_object(v___x_1631_);
v_val_1633_ = lean_ctor_get(v_a_1629_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v_a_1629_, 1);
v___x_1634_ = l_Lean_LocalDecl_toExpr(v_val_1633_);
v___x_1635_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1615_, v___x_1634_, v___y_1624_);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; 
v_unused_1644_ = lean_ctor_get(v___x_1635_, 0);
lean_dec(v_unused_1644_);
v___x_1637_ = v___x_1635_;
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
else
{
lean_dec(v___x_1635_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1639_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
lean_dec(v_a_1629_);
lean_dec(v_goal_1615_);
v___x_1645_ = lean_box(0);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1645_);
v___x_1647_ = v___x_1631_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_goal_1615_);
v_a_1650_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1628_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1628_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0___boxed(lean_object* v_scope_1658_, lean_object* v_target_1659_, lean_object* v_goal_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0(v_scope_1658_, v_target_1659_, v_goal_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec_ref(v_target_1659_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f(lean_object* v_scope_1674_, lean_object* v_goal_1675_, lean_object* v_target_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___f_1689_; lean_object* v___x_1690_; 
lean_inc(v_goal_1675_);
v___f_1689_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0___boxed), 15, 3);
lean_closure_set(v___f_1689_, 0, v_scope_1674_);
lean_closure_set(v___f_1689_, 1, v_target_1676_);
lean_closure_set(v___f_1689_, 2, v_goal_1675_);
v___x_1690_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1675_, v___f_1689_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___boxed(lean_object* v_scope_1691_, lean_object* v_goal_1692_, lean_object* v_target_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f(v_scope_1691_, v_goal_1692_, v_target_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(lean_object* v_e_1707_, lean_object* v_i_1708_, lean_object* v_n_1709_, lean_object* v_v_1710_){
_start:
{
if (lean_obj_tag(v_e_1707_) == 5)
{
lean_object* v_fn_1711_; lean_object* v_arg_1712_; uint8_t v___y_1714_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v_fn_1711_ = lean_ctor_get(v_e_1707_, 0);
v_arg_1712_ = lean_ctor_get(v_e_1707_, 1);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_add(v_i_1708_, v___x_1716_);
v___x_1718_ = lean_nat_dec_eq(v_n_1709_, v___x_1717_);
lean_dec(v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___y_1722_; size_t v___x_1724_; size_t v___x_1725_; uint8_t v___x_1726_; 
v___x_1719_ = lean_nat_sub(v_n_1709_, v___x_1716_);
lean_inc_ref(v_fn_1711_);
v___x_1720_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(v_fn_1711_, v_i_1708_, v___x_1719_, v_v_1710_);
lean_dec(v___x_1719_);
v___x_1724_ = lean_ptr_addr(v_fn_1711_);
v___x_1725_ = lean_ptr_addr(v___x_1720_);
v___x_1726_ = lean_usize_dec_eq(v___x_1724_, v___x_1725_);
if (v___x_1726_ == 0)
{
v___y_1722_ = v___x_1726_;
goto v___jp_1721_;
}
else
{
size_t v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = lean_ptr_addr(v_arg_1712_);
v___x_1728_ = lean_usize_dec_eq(v___x_1727_, v___x_1727_);
v___y_1722_ = v___x_1728_;
goto v___jp_1721_;
}
v___jp_1721_:
{
if (v___y_1722_ == 0)
{
lean_object* v___x_1723_; 
lean_inc_ref(v_arg_1712_);
lean_dec_ref_known(v_e_1707_, 2);
v___x_1723_ = l_Lean_Expr_app___override(v___x_1720_, v_arg_1712_);
return v___x_1723_;
}
else
{
lean_dec_ref(v___x_1720_);
return v_e_1707_;
}
}
}
else
{
size_t v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = lean_ptr_addr(v_fn_1711_);
v___x_1730_ = lean_usize_dec_eq(v___x_1729_, v___x_1729_);
if (v___x_1730_ == 0)
{
v___y_1714_ = v___x_1730_;
goto v___jp_1713_;
}
else
{
size_t v___x_1731_; size_t v___x_1732_; uint8_t v___x_1733_; 
v___x_1731_ = lean_ptr_addr(v_arg_1712_);
v___x_1732_ = lean_ptr_addr(v_v_1710_);
v___x_1733_ = lean_usize_dec_eq(v___x_1731_, v___x_1732_);
v___y_1714_ = v___x_1733_;
goto v___jp_1713_;
}
}
v___jp_1713_:
{
if (v___y_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_inc_ref(v_fn_1711_);
lean_dec_ref_known(v_e_1707_, 2);
v___x_1715_ = l_Lean_Expr_app___override(v_fn_1711_, v_v_1710_);
return v___x_1715_;
}
else
{
lean_dec_ref(v_v_1710_);
return v_e_1707_;
}
}
}
else
{
lean_dec_ref(v_v_1710_);
return v_e_1707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg___boxed(lean_object* v_e_1734_, lean_object* v_i_1735_, lean_object* v_n_1736_, lean_object* v_v_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(v_e_1734_, v_i_1735_, v_n_1736_, v_v_1737_);
lean_dec(v_n_1736_);
lean_dec(v_i_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(lean_object* v_rhs_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
uint8_t v___x_1755_; 
v___x_1755_ = l_Lean_Expr_hasMVar(v_rhs_1747_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec_ref(v_rhs_1747_);
v___x_1756_ = lean_box(0);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
else
{
lean_object* v_n_1758_; lean_object* v___x_1759_; uint8_t v___y_1761_; uint8_t v___x_1808_; 
v_n_1758_ = l_Lean_Expr_getAppNumArgs(v_rhs_1747_);
v___x_1759_ = lean_unsigned_to_nat(7u);
v___x_1808_ = lean_nat_dec_lt(v___x_1759_, v_n_1758_);
if (v___x_1808_ == 0)
{
v___y_1761_ = v___x_1808_;
goto v___jp_1760_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1809_ = l_Lean_Expr_getAppFn(v_rhs_1747_);
v___x_1810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__2));
v___x_1811_ = l_Lean_Expr_isConstOf(v___x_1809_, v___x_1810_);
lean_dec_ref(v___x_1809_);
v___y_1761_ = v___x_1811_;
goto v___jp_1760_;
}
v___jp_1760_:
{
if (v___y_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v_n_1758_);
lean_dec_ref(v_rhs_1747_);
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v_prog_1767_; lean_object* v___x_1768_; 
v___x_1764_ = lean_nat_sub(v_n_1758_, v___x_1759_);
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = lean_nat_sub(v___x_1764_, v___x_1765_);
lean_dec(v___x_1764_);
v_prog_1767_ = l_Lean_Expr_getRevArg_x21(v_rhs_1747_, v___x_1766_);
lean_inc_ref(v_prog_1767_);
v___x_1768_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_prog_1767_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1799_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1799_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1799_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
size_t v___x_1773_; size_t v___x_1774_; uint8_t v___x_1775_; 
v___x_1773_ = lean_ptr_addr(v_prog_1767_);
lean_dec_ref(v_prog_1767_);
v___x_1774_ = lean_ptr_addr(v_a_1769_);
v___x_1775_ = lean_usize_dec_eq(v___x_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_del_object(v___x_1771_);
v___x_1776_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(v_rhs_1747_, v___x_1759_, v_n_1758_, v_a_1769_);
lean_dec(v_n_1758_);
v___x_1777_ = l_Lean_Meta_Sym_shareCommon(v___x_1776_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1786_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_a_1778_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
v_a_1787_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1777_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1777_);
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
else
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_dec(v_a_1769_);
lean_dec(v_n_1758_);
lean_dec_ref(v_rhs_1747_);
v___x_1795_ = lean_box(0);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1795_);
v___x_1797_ = v___x_1771_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
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
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec_ref(v_prog_1767_);
lean_dec(v_n_1758_);
lean_dec_ref(v_rhs_1747_);
v_a_1800_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1768_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1768_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___boxed(lean_object* v_rhs_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_rhs_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f(lean_object* v_rhs_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_rhs_1821_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___boxed(lean_object* v_rhs_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f(v_rhs_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1849_, lean_object* v_a_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___y_1859_; lean_object* v___x_1862_; uint8_t v_debug_1863_; 
v___x_1862_ = lean_st_ref_get(v___y_1852_);
v_debug_1863_ = lean_ctor_get_uint8(v___x_1862_, sizeof(void*)*11);
lean_dec(v___x_1862_);
if (v_debug_1863_ == 0)
{
v___y_1859_ = v___y_1852_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1849_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v___x_1865_; 
lean_dec_ref_known(v___x_1864_, 1);
v___x_1865_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_dec_ref_known(v___x_1865_, 1);
v___y_1859_ = v___y_1852_;
goto v___jp_1858_;
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v_a_1850_);
lean_dec_ref(v_f_1849_);
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v_a_1850_);
lean_dec_ref(v_f_1849_);
v_a_1874_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1864_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1864_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
v___jp_1858_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = l_Lean_Expr_app___override(v_f_1849_, v_a_1850_);
v___x_1861_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1860_, v___y_1859_);
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1882_, lean_object* v_a_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_f_1882_, v_a_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0(lean_object* v_args_1892_, lean_object* v_endIdx_1893_, lean_object* v_b_1894_, lean_object* v_i_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_nat_dec_le(v_endIdx_1893_, v_i_1895_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = l_Lean_instInhabitedExpr;
v___x_1910_ = lean_array_get_borrowed(v___x_1909_, v_args_1892_, v_i_1895_);
lean_inc(v___x_1910_);
v___x_1911_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_b_1894_, v___x_1910_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = lean_unsigned_to_nat(1u);
v___x_1914_ = lean_nat_add(v_i_1895_, v___x_1913_);
lean_dec(v_i_1895_);
v_b_1894_ = v_a_1912_;
v_i_1895_ = v___x_1914_;
goto _start;
}
else
{
lean_dec(v_i_1895_);
return v___x_1911_;
}
}
else
{
lean_object* v___x_1916_; 
lean_dec(v_i_1895_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_b_1894_);
return v___x_1916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0___boxed(lean_object* v_args_1917_, lean_object* v_endIdx_1918_, lean_object* v_b_1919_, lean_object* v_i_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0(v_args_1917_, v_endIdx_1918_, v_b_1919_, v_i_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v_endIdx_1918_);
lean_dec_ref(v_args_1917_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(lean_object* v_f_1934_, lean_object* v_args_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = lean_array_get_size(v_args_1935_);
v___x_1950_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0(v_args_1935_, v___x_1949_, v_f_1934_, v___x_1948_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0___boxed(lean_object* v_f_1951_, lean_object* v_args_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_f_1951_, v_args_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec_ref(v_args_1952_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(lean_object* v_goal_1966_, lean_object* v_target_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = l_Lean_Expr_cleanupAnnotations(v_target_1967_);
v___x_1984_ = l_Lean_Expr_isApp(v___x_1983_);
if (v___x_1984_ == 0)
{
lean_dec_ref(v___x_1983_);
lean_dec(v_goal_1966_);
goto v___jp_1980_;
}
else
{
lean_object* v_arg_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_arg_1985_ = lean_ctor_get(v___x_1983_, 1);
lean_inc_ref(v_arg_1985_);
v___x_1986_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1983_);
v___x_1987_ = l_Lean_Expr_isApp(v___x_1986_);
if (v___x_1987_ == 0)
{
lean_dec_ref(v___x_1986_);
lean_dec_ref(v_arg_1985_);
lean_dec(v_goal_1966_);
goto v___jp_1980_;
}
else
{
lean_object* v_arg_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v_arg_1988_ = lean_ctor_get(v___x_1986_, 1);
lean_inc_ref(v_arg_1988_);
v___x_1989_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1986_);
v___x_1990_ = l_Lean_Expr_isApp(v___x_1989_);
if (v___x_1990_ == 0)
{
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec(v_goal_1966_);
goto v___jp_1980_;
}
else
{
lean_object* v_arg_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v_arg_1991_ = lean_ctor_get(v___x_1989_, 1);
lean_inc_ref(v_arg_1991_);
v___x_1992_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1989_);
v___x_1993_ = l_Lean_Expr_isApp(v___x_1992_);
if (v___x_1993_ == 0)
{
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec(v_goal_1966_);
goto v___jp_1980_;
}
else
{
lean_object* v_arg_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v_arg_1994_ = lean_ctor_get(v___x_1992_, 1);
lean_inc_ref(v_arg_1994_);
v___x_1995_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1992_);
v___x_1996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10));
v___x_1997_ = l_Lean_Expr_isConstOf(v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_dec_ref(v___x_1995_);
lean_dec_ref(v_arg_1994_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec(v_goal_1966_);
goto v___jp_1980_;
}
else
{
lean_object* v___x_1998_; 
lean_inc_ref(v_arg_1994_);
v___x_1998_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1994_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
lean_inc_ref(v_arg_1988_);
v___x_2000_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1988_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2002_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
lean_inc_ref(v_arg_1985_);
v___x_2002_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1985_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2004_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc_n(v_a_2003_, 2);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_a_2003_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2064_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2064_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2064_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___y_2010_; lean_object* v___y_2046_; uint8_t v___y_2047_; lean_object* v___y_2056_; 
if (lean_obj_tag(v_a_2005_) == 0)
{
v___y_2056_ = v_a_2003_;
goto v___jp_2055_;
}
else
{
lean_object* v_val_2063_; 
lean_dec(v_a_2003_);
v_val_2063_ = lean_ctor_get(v_a_2005_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v_a_2005_, 1);
v___y_2056_ = v_val_2063_;
goto v___jp_2055_;
}
v___jp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2011_ = lean_unsigned_to_nat(4u);
v___x_2012_ = lean_mk_empty_array_with_capacity(v___x_2011_);
v___x_2013_ = lean_array_push(v___x_2012_, v_a_1999_);
v___x_2014_ = lean_array_push(v___x_2013_, v_arg_1991_);
v___x_2015_ = lean_array_push(v___x_2014_, v_a_2001_);
v___x_2016_ = lean_array_push(v___x_2015_, v___y_2010_);
v___x_2017_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v___x_1995_, v___x_2016_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
lean_dec_ref(v___x_2016_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_1966_, v_a_2018_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2028_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_a_2020_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_a_2029_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2019_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2019_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_goal_1966_);
v_a_2037_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2017_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2017_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
v___jp_2045_:
{
if (v___y_2047_ == 0)
{
lean_del_object(v___x_2007_);
lean_dec_ref(v_arg_1985_);
v___y_2010_ = v___y_2046_;
goto v___jp_2009_;
}
else
{
size_t v___x_2048_; size_t v___x_2049_; uint8_t v___x_2050_; 
v___x_2048_ = lean_ptr_addr(v_arg_1985_);
lean_dec_ref(v_arg_1985_);
v___x_2049_ = lean_ptr_addr(v___y_2046_);
v___x_2050_ = lean_usize_dec_eq(v___x_2048_, v___x_2049_);
if (v___x_2050_ == 0)
{
lean_del_object(v___x_2007_);
v___y_2010_ = v___y_2046_;
goto v___jp_2009_;
}
else
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
lean_dec_ref(v___y_2046_);
lean_dec(v_a_2001_);
lean_dec(v_a_1999_);
lean_dec_ref(v___x_1995_);
lean_dec_ref(v_arg_1991_);
lean_dec(v_goal_1966_);
v___x_2051_ = lean_box(0);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2051_);
v___x_2053_ = v___x_2007_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
v___jp_2055_:
{
size_t v___x_2057_; size_t v___x_2058_; uint8_t v___x_2059_; 
v___x_2057_ = lean_ptr_addr(v_arg_1994_);
lean_dec_ref(v_arg_1994_);
v___x_2058_ = lean_ptr_addr(v_a_1999_);
v___x_2059_ = lean_usize_dec_eq(v___x_2057_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_dec_ref(v_arg_1988_);
v___y_2046_ = v___y_2056_;
v___y_2047_ = v___x_2059_;
goto v___jp_2045_;
}
else
{
size_t v___x_2060_; size_t v___x_2061_; uint8_t v___x_2062_; 
v___x_2060_ = lean_ptr_addr(v_arg_1988_);
lean_dec_ref(v_arg_1988_);
v___x_2061_ = lean_ptr_addr(v_a_2001_);
v___x_2062_ = lean_usize_dec_eq(v___x_2060_, v___x_2061_);
v___y_2046_ = v___y_2056_;
v___y_2047_ = v___x_2062_;
goto v___jp_2045_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec(v_a_2003_);
lean_dec(v_a_2001_);
lean_dec(v_a_1999_);
lean_dec_ref(v___x_1995_);
lean_dec_ref(v_arg_1994_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec(v_goal_1966_);
v_a_2065_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2004_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2004_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_a_2001_);
lean_dec(v_a_1999_);
lean_dec_ref(v___x_1995_);
lean_dec_ref(v_arg_1994_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec(v_goal_1966_);
v_a_2073_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2002_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2002_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_a_1999_);
lean_dec_ref(v___x_1995_);
lean_dec_ref(v_arg_1994_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec(v_goal_1966_);
v_a_2081_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2000_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2000_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v___x_1995_);
lean_dec_ref(v_arg_1994_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec(v_goal_1966_);
v_a_2089_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_1998_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_1998_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
}
}
}
v___jp_1980_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_box(0);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
return v___x_1982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f___boxed(lean_object* v_goal_2097_, lean_object* v_target_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(v_goal_2097_, v_target_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1(lean_object* v_f_2112_, lean_object* v_a_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_f_2112_, v_a_2113_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2127_, lean_object* v_a_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1(v_f_2127_, v_a_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
return v_res_2141_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__2));
v___x_2149_ = l_Lean_stringToMessageData(v___x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(lean_object* v_goal_2150_, lean_object* v_pre_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = l_Lean_Expr_cleanupAnnotations(v_pre_2151_);
v___x_2168_ = l_Lean_Expr_isApp(v___x_2167_);
if (v___x_2168_ == 0)
{
lean_dec_ref(v___x_2167_);
lean_dec(v_goal_2150_);
goto v___jp_2164_;
}
else
{
lean_object* v_arg_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_arg_2169_ = lean_ctor_get(v___x_2167_, 1);
lean_inc_ref(v_arg_2169_);
v___x_2170_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2167_);
v___x_2171_ = l_Lean_Expr_isApp(v___x_2170_);
if (v___x_2171_ == 0)
{
lean_dec_ref(v___x_2170_);
lean_dec_ref(v_arg_2169_);
lean_dec(v_goal_2150_);
goto v___jp_2164_;
}
else
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2170_);
v___x_2173_ = l_Lean_Expr_isApp(v___x_2172_);
if (v___x_2173_ == 0)
{
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_arg_2169_);
lean_dec(v_goal_2150_);
goto v___jp_2164_;
}
else
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2172_);
v___x_2175_ = l_Lean_Expr_isApp(v___x_2174_);
if (v___x_2175_ == 0)
{
lean_dec_ref(v___x_2174_);
lean_dec_ref(v_arg_2169_);
lean_dec(v_goal_2150_);
goto v___jp_2164_;
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2176_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2174_);
v___x_2177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_2178_ = l_Lean_Expr_isConstOf(v___x_2176_, v___x_2177_);
lean_dec_ref(v___x_2176_);
if (v___x_2178_ == 0)
{
lean_dec_ref(v_arg_2169_);
lean_dec(v_goal_2150_);
goto v___jp_2164_;
}
else
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3));
v___x_2180_ = l_Lean_Expr_isAppOf(v_arg_2169_, v___x_2179_);
lean_dec_ref(v_arg_2169_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec(v_goal_2150_);
v___x_2181_ = lean_box(0);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
return v___x_2182_;
}
else
{
lean_object* v_backwardRules_2183_; lean_object* v_meetTop_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_backwardRules_2183_ = lean_ctor_get(v_a_2152_, 0);
v_meetTop_2184_ = lean_ctor_get(v_backwardRules_2183_, 10);
v___x_2185_ = lean_box(0);
lean_inc(v_goal_2150_);
lean_inc_ref(v_meetTop_2184_);
v___x_2186_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_meetTop_2184_, v_goal_2150_, v___x_2185_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2213_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2213_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2213_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; 
if (lean_obj_tag(v_a_2187_) == 1)
{
lean_object* v_mvarIds_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2212_; 
v_mvarIds_2200_ = lean_ctor_get(v_a_2187_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_a_2187_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2202_ = v_a_2187_;
v_isShared_2203_ = v_isSharedCheck_2212_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_mvarIds_2200_);
lean_dec(v_a_2187_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2212_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
if (lean_obj_tag(v_mvarIds_2200_) == 1)
{
lean_object* v_tail_2204_; 
v_tail_2204_ = lean_ctor_get(v_mvarIds_2200_, 1);
if (lean_obj_tag(v_tail_2204_) == 0)
{
lean_object* v_head_2205_; lean_object* v___x_2207_; 
lean_dec(v_goal_2150_);
v_head_2205_ = lean_ctor_get(v_mvarIds_2200_, 0);
lean_inc(v_head_2205_);
lean_dec_ref_known(v_mvarIds_2200_, 2);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v_head_2205_);
v___x_2207_ = v___x_2202_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_head_2205_);
v___x_2207_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2209_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2207_);
v___x_2209_ = v___x_2189_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2200_, 2);
lean_del_object(v___x_2202_);
lean_del_object(v___x_2189_);
v___y_2192_ = v_a_2159_;
v___y_2193_ = v_a_2160_;
v___y_2194_ = v_a_2161_;
v___y_2195_ = v_a_2162_;
goto v___jp_2191_;
}
}
else
{
lean_del_object(v___x_2202_);
lean_dec(v_mvarIds_2200_);
lean_del_object(v___x_2189_);
v___y_2192_ = v_a_2159_;
v___y_2193_ = v_a_2160_;
v___y_2194_ = v_a_2161_;
v___y_2195_ = v_a_2162_;
goto v___jp_2191_;
}
}
}
else
{
lean_del_object(v___x_2189_);
lean_dec(v_a_2187_);
v___y_2192_ = v_a_2159_;
v___y_2193_ = v_a_2160_;
v___y_2194_ = v_a_2161_;
v___y_2195_ = v_a_2162_;
goto v___jp_2191_;
}
v___jp_2191_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2196_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3);
v___x_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2197_, 0, v_goal_2150_);
v___x_2198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2196_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2198_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_goal_2150_);
v_a_2214_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2186_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2186_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
}
}
}
}
v___jp_2164_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___boxed(lean_object* v_goal_2222_, lean_object* v_pre_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(v_goal_2222_, v_pre_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(lean_object* v_goal_2244_, lean_object* v_pre_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = l_Lean_Expr_cleanupAnnotations(v_pre_2245_);
v___x_2262_ = l_Lean_Expr_isApp(v___x_2261_);
if (v___x_2262_ == 0)
{
lean_dec_ref(v___x_2261_);
lean_dec(v_goal_2244_);
goto v___jp_2258_;
}
else
{
lean_object* v_arg_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v_arg_2263_ = lean_ctor_get(v___x_2261_, 1);
lean_inc_ref(v_arg_2263_);
v___x_2264_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2261_);
v___x_2265_ = l_Lean_Expr_isApp(v___x_2264_);
if (v___x_2265_ == 0)
{
lean_dec_ref(v___x_2264_);
lean_dec_ref(v_arg_2263_);
lean_dec(v_goal_2244_);
goto v___jp_2258_;
}
else
{
lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2264_);
v___x_2267_ = l_Lean_Expr_isApp(v___x_2266_);
if (v___x_2267_ == 0)
{
lean_dec_ref(v___x_2266_);
lean_dec_ref(v_arg_2263_);
lean_dec(v_goal_2244_);
goto v___jp_2258_;
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2268_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2266_);
v___x_2269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_2270_ = l_Lean_Expr_isConstOf(v___x_2268_, v___x_2269_);
lean_dec_ref(v___x_2268_);
if (v___x_2270_ == 0)
{
lean_dec_ref(v_arg_2263_);
lean_dec(v_goal_2244_);
goto v___jp_2258_;
}
else
{
uint8_t v___x_2271_; 
v___x_2271_ = l_Lean_Expr_isTrue(v_arg_2263_);
if (v___x_2271_ == 0)
{
lean_object* v_backwardRules_2272_; lean_object* v_ofPropPreIntro_2273_; lean_object* v___x_2274_; 
v_backwardRules_2272_ = lean_ctor_get(v_a_2246_, 0);
v_ofPropPreIntro_2273_ = lean_ctor_get(v_backwardRules_2272_, 3);
lean_inc_ref(v_ofPropPreIntro_2273_);
v___x_2274_ = l_Lean_Elab_Tactic_VCGen_introPre(v_ofPropPreIntro_2273_, v_goal_2244_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2283_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_a_2275_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2279_);
v___x_2281_ = v___x_2277_;
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
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
v_a_2284_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2274_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2274_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec(v_goal_2244_);
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
}
}
}
}
v___jp_2258_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = lean_box(0);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___boxed(lean_object* v_goal_2294_, lean_object* v_pre_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(v_goal_2294_, v_pre_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
lean_dec(v_a_2304_);
lean_dec_ref(v_a_2303_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(lean_object* v_goal_2309_, lean_object* v_pre_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2329_ = l_Lean_Expr_cleanupAnnotations(v_pre_2310_);
v___x_2330_ = l_Lean_Expr_isApp(v___x_2329_);
if (v___x_2330_ == 0)
{
lean_dec_ref(v___x_2329_);
lean_dec(v_goal_2309_);
goto v___jp_2323_;
}
else
{
lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2329_);
v___x_2332_ = l_Lean_Expr_isApp(v___x_2331_);
if (v___x_2332_ == 0)
{
lean_dec_ref(v___x_2331_);
lean_dec(v_goal_2309_);
goto v___jp_2323_;
}
else
{
lean_object* v_arg_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v_arg_2333_ = lean_ctor_get(v___x_2331_, 1);
lean_inc_ref(v_arg_2333_);
v___x_2334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2331_);
v___x_2335_ = l_Lean_Expr_isApp(v___x_2334_);
if (v___x_2335_ == 0)
{
lean_dec_ref(v___x_2334_);
lean_dec_ref(v_arg_2333_);
lean_dec(v_goal_2309_);
goto v___jp_2323_;
}
else
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2334_);
v___x_2337_ = l_Lean_Expr_isApp(v___x_2336_);
if (v___x_2337_ == 0)
{
lean_dec_ref(v___x_2336_);
lean_dec_ref(v_arg_2333_);
lean_dec(v_goal_2309_);
goto v___jp_2323_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2336_);
v___x_2339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_2340_ = l_Lean_Expr_isConstOf(v___x_2338_, v___x_2339_);
lean_dec_ref(v___x_2338_);
if (v___x_2340_ == 0)
{
lean_dec_ref(v_arg_2333_);
lean_dec(v_goal_2309_);
goto v___jp_2323_;
}
else
{
lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = l_Lean_Expr_cleanupAnnotations(v_arg_2333_);
v___x_2342_ = l_Lean_Expr_isApp(v___x_2341_);
if (v___x_2342_ == 0)
{
lean_dec_ref(v___x_2341_);
lean_dec(v_goal_2309_);
goto v___jp_2326_;
}
else
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2341_);
v___x_2344_ = l_Lean_Expr_isApp(v___x_2343_);
if (v___x_2344_ == 0)
{
lean_dec_ref(v___x_2343_);
lean_dec(v_goal_2309_);
goto v___jp_2326_;
}
else
{
lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2343_);
v___x_2346_ = l_Lean_Expr_isApp(v___x_2345_);
if (v___x_2346_ == 0)
{
lean_dec_ref(v___x_2345_);
lean_dec(v_goal_2309_);
goto v___jp_2326_;
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2345_);
v___x_2348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_2349_ = l_Lean_Expr_isConstOf(v___x_2347_, v___x_2348_);
lean_dec_ref(v___x_2347_);
if (v___x_2349_ == 0)
{
lean_dec(v_goal_2309_);
goto v___jp_2326_;
}
else
{
lean_object* v_backwardRules_2350_; lean_object* v_ofPropMeetPreIntro_2351_; lean_object* v___x_2352_; 
v_backwardRules_2350_ = lean_ctor_get(v_a_2311_, 0);
v_ofPropMeetPreIntro_2351_ = lean_ctor_get(v_backwardRules_2350_, 4);
lean_inc_ref(v_ofPropMeetPreIntro_2351_);
v___x_2352_ = l_Lean_Elab_Tactic_VCGen_introPre(v_ofPropMeetPreIntro_2351_, v_goal_2309_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2361_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_a_2353_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2357_);
v___x_2359_ = v___x_2355_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
v_a_2362_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2352_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2352_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
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
}
v___jp_2323_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_box(0);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
return v___x_2325_;
}
v___jp_2326_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_box(0);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f___boxed(lean_object* v_goal_2370_, lean_object* v_pre_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(v_goal_2370_, v_pre_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
return v_res_2384_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__2));
v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(lean_object* v_goal_2393_, lean_object* v_pre_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1));
v___x_2408_ = lean_unsigned_to_nat(4u);
v___x_2409_ = l_Lean_Expr_isAppOfArity(v_pre_2394_, v___x_2407_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_dec(v_goal_2393_);
v___x_2410_ = lean_box(0);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
return v___x_2411_;
}
else
{
lean_object* v_backwardRules_2412_; lean_object* v_iSupPreIntro_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_backwardRules_2412_ = lean_ctor_get(v_a_2395_, 0);
v_iSupPreIntro_2413_ = lean_ctor_get(v_backwardRules_2412_, 5);
v___x_2414_ = lean_box(0);
lean_inc(v_goal_2393_);
lean_inc_ref(v_iSupPreIntro_2413_);
v___x_2415_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_iSupPreIntro_2413_, v_goal_2393_, v___x_2414_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2442_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2442_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2442_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; 
if (lean_obj_tag(v_a_2416_) == 1)
{
lean_object* v_mvarIds_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2441_; 
v_mvarIds_2429_ = lean_ctor_get(v_a_2416_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_a_2416_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2431_ = v_a_2416_;
v_isShared_2432_ = v_isSharedCheck_2441_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_mvarIds_2429_);
lean_dec(v_a_2416_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2441_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
if (lean_obj_tag(v_mvarIds_2429_) == 1)
{
lean_object* v_tail_2433_; 
v_tail_2433_ = lean_ctor_get(v_mvarIds_2429_, 1);
if (lean_obj_tag(v_tail_2433_) == 0)
{
lean_object* v_head_2434_; lean_object* v___x_2436_; 
lean_dec(v_goal_2393_);
v_head_2434_ = lean_ctor_get(v_mvarIds_2429_, 0);
lean_inc(v_head_2434_);
lean_dec_ref_known(v_mvarIds_2429_, 2);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v_head_2434_);
v___x_2436_ = v___x_2431_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_head_2434_);
v___x_2436_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2438_; 
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2436_);
v___x_2438_ = v___x_2418_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2429_, 2);
lean_del_object(v___x_2431_);
lean_del_object(v___x_2418_);
v___y_2421_ = v_a_2402_;
v___y_2422_ = v_a_2403_;
v___y_2423_ = v_a_2404_;
v___y_2424_ = v_a_2405_;
goto v___jp_2420_;
}
}
else
{
lean_del_object(v___x_2431_);
lean_dec(v_mvarIds_2429_);
lean_del_object(v___x_2418_);
v___y_2421_ = v_a_2402_;
v___y_2422_ = v_a_2403_;
v___y_2423_ = v_a_2404_;
v___y_2424_ = v_a_2405_;
goto v___jp_2420_;
}
}
}
else
{
lean_del_object(v___x_2418_);
lean_dec(v_a_2416_);
v___y_2421_ = v_a_2402_;
v___y_2422_ = v_a_2403_;
v___y_2423_ = v_a_2404_;
v___y_2424_ = v_a_2405_;
goto v___jp_2420_;
}
v___jp_2420_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3);
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v_goal_2393_);
v___x_2427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2427_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
return v___x_2428_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec(v_goal_2393_);
v_a_2443_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2415_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2415_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___boxed(lean_object* v_goal_2451_, lean_object* v_pre_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(v_goal_2451_, v_pre_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec_ref(v_pre_2452_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(lean_object* v_goal_2466_, lean_object* v_00_u03b1_2467_, lean_object* v_pre_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
uint8_t v___x_2481_; 
v___x_2481_ = l_Lean_Expr_isProp(v_00_u03b1_2467_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec(v_goal_2466_);
v___x_2482_ = lean_box(0);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
else
{
lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3));
v___x_2485_ = l_Lean_Expr_isAppOf(v_pre_2468_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v_backwardRules_2486_; lean_object* v_propPreIntro_2487_; lean_object* v___x_2488_; 
v_backwardRules_2486_ = lean_ctor_get(v_a_2469_, 0);
v_propPreIntro_2487_ = lean_ctor_get(v_backwardRules_2486_, 2);
lean_inc_ref(v_propPreIntro_2487_);
v___x_2488_ = l_Lean_Elab_Tactic_VCGen_introPre(v_propPreIntro_2487_, v_goal_2466_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2497_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2493_, 0, v_a_2489_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v___x_2493_);
v___x_2495_ = v___x_2491_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
v_a_2498_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2488_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2488_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v_goal_2466_);
v___x_2506_ = lean_box(0);
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f___boxed(lean_object* v_goal_2508_, lean_object* v_00_u03b1_2509_, lean_object* v_pre_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(v_goal_2508_, v_00_u03b1_2509_, v_pre_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec_ref(v_pre_2510_);
lean_dec_ref(v_00_u03b1_2509_);
return v_res_2523_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__0));
v___x_2526_ = l_Lean_stringToMessageData(v___x_2525_);
return v___x_2526_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4(void){
_start:
{
uint8_t v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = 0;
v___x_2533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3));
v___x_2534_ = l_Lean_MessageData_ofConstName(v___x_2533_, v___x_2532_);
return v___x_2534_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4);
v___x_2536_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1);
v___x_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v___x_2535_);
return v___x_2537_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__6));
v___x_2540_ = l_Lean_stringToMessageData(v___x_2539_);
return v___x_2540_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7);
v___x_2542_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5);
v___x_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v___x_2541_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(lean_object* v_goal_2544_, lean_object* v_pre_2545_, lean_object* v_target_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; uint8_t v___x_2597_; 
lean_inc_ref(v_pre_2545_);
v___x_2597_ = l_Lean_Expr_isTrue(v_pre_2545_);
if (v___x_2597_ == 0)
{
v___y_2560_ = v_a_2552_;
v___y_2561_ = v_a_2553_;
v___y_2562_ = v_a_2554_;
v___y_2563_ = v_a_2555_;
v___y_2564_ = v_a_2556_;
v___y_2565_ = v_a_2557_;
goto v___jp_2559_;
}
else
{
lean_object* v_backwardRules_2598_; lean_object* v_truePreIntro_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v_pre_2545_);
v_backwardRules_2598_ = lean_ctor_get(v_a_2547_, 0);
v_truePreIntro_2599_ = lean_ctor_get(v_backwardRules_2598_, 6);
v___x_2600_ = lean_box(0);
lean_inc_ref(v_truePreIntro_2599_);
v___x_2601_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_truePreIntro_2599_, v_goal_2544_, v___x_2600_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2637_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2637_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2637_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; 
if (lean_obj_tag(v_a_2602_) == 1)
{
lean_object* v_mvarIds_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2636_; 
v_mvarIds_2625_ = lean_ctor_get(v_a_2602_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_a_2602_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2627_ = v_a_2602_;
v_isShared_2628_ = v_isSharedCheck_2636_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_mvarIds_2625_);
lean_dec(v_a_2602_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2636_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
if (lean_obj_tag(v_mvarIds_2625_) == 1)
{
lean_object* v_tail_2629_; 
v_tail_2629_ = lean_ctor_get(v_mvarIds_2625_, 1);
if (lean_obj_tag(v_tail_2629_) == 0)
{
lean_object* v___x_2631_; 
lean_dec_ref(v_target_2546_);
if (v_isShared_2628_ == 0)
{
v___x_2631_ = v___x_2627_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_mvarIds_2625_);
v___x_2631_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2633_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2631_);
v___x_2633_ = v___x_2604_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2625_, 2);
lean_del_object(v___x_2627_);
lean_del_object(v___x_2604_);
v___y_2607_ = v_a_2552_;
v___y_2608_ = v_a_2553_;
v___y_2609_ = v_a_2554_;
v___y_2610_ = v_a_2555_;
v___y_2611_ = v_a_2556_;
v___y_2612_ = v_a_2557_;
goto v___jp_2606_;
}
}
else
{
lean_del_object(v___x_2627_);
lean_dec(v_mvarIds_2625_);
lean_del_object(v___x_2604_);
v___y_2607_ = v_a_2552_;
v___y_2608_ = v_a_2553_;
v___y_2609_ = v_a_2554_;
v___y_2610_ = v_a_2555_;
v___y_2611_ = v_a_2556_;
v___y_2612_ = v_a_2557_;
goto v___jp_2606_;
}
}
}
else
{
lean_del_object(v___x_2604_);
lean_dec(v_a_2602_);
v___y_2607_ = v_a_2552_;
v___y_2608_ = v_a_2553_;
v___y_2609_ = v_a_2554_;
v___y_2610_ = v_a_2555_;
v___y_2611_ = v_a_2556_;
v___y_2612_ = v_a_2557_;
goto v___jp_2606_;
}
v___jp_2606_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
v___x_2613_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8);
v___x_2614_ = l_Lean_indentExpr(v_target_2546_);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2615_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2616_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec_ref(v_target_2546_);
v_a_2638_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2601_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2601_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
v___jp_2559_:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(v_goal_2544_, v_target_2546_, v_pre_2545_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2588_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2588_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2588_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
if (lean_obj_tag(v_a_2567_) == 1)
{
lean_object* v_val_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2583_; 
v_val_2571_ = lean_ctor_get(v_a_2567_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_a_2567_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2573_ = v_a_2567_;
v_isShared_2574_ = v_isSharedCheck_2583_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_val_2571_);
lean_dec(v_a_2567_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2583_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_val_2571_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2576_);
v___x_2578_ = v___x_2573_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2578_);
v___x_2580_ = v___x_2569_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
lean_dec(v_a_2567_);
v___x_2584_ = lean_box(0);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2584_);
v___x_2586_ = v___x_2569_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
v_a_2589_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2566_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2566_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___boxed(lean_object* v_goal_2646_, lean_object* v_pre_2647_, lean_object* v_target_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(v_goal_2646_, v_pre_2647_, v_target_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(lean_object* v_scope_2662_, lean_object* v_goal_2663_, lean_object* v_00_u03b1_2664_, lean_object* v_pre_2665_, lean_object* v_target_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v_g_2680_; lean_object* v_g_2687_; lean_object* v_h_2688_; lean_object* v___x_2706_; 
lean_inc_ref(v_pre_2665_);
lean_inc(v_goal_2663_);
v___x_2706_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(v_goal_2663_, v_pre_2665_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2706_, 1);
if (lean_obj_tag(v_a_2707_) == 1)
{
lean_object* v_val_2708_; 
lean_dec_ref(v_target_2666_);
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
v_val_2708_ = lean_ctor_get(v_a_2707_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v_a_2707_, 1);
v_g_2680_ = v_val_2708_;
goto v___jp_2679_;
}
else
{
lean_object* v___x_2709_; 
lean_dec(v_a_2707_);
lean_inc_ref(v_pre_2665_);
lean_inc(v_goal_2663_);
v___x_2709_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(v_goal_2663_, v_pre_2665_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
if (lean_obj_tag(v_a_2710_) == 1)
{
lean_object* v_val_2711_; lean_object* v_fst_2712_; lean_object* v_snd_2713_; 
lean_dec_ref(v_target_2666_);
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
v_val_2711_ = lean_ctor_get(v_a_2710_, 0);
lean_inc(v_val_2711_);
lean_dec_ref_known(v_a_2710_, 1);
v_fst_2712_ = lean_ctor_get(v_val_2711_, 0);
lean_inc(v_fst_2712_);
v_snd_2713_ = lean_ctor_get(v_val_2711_, 1);
lean_inc(v_snd_2713_);
lean_dec(v_val_2711_);
v_g_2687_ = v_fst_2712_;
v_h_2688_ = v_snd_2713_;
goto v___jp_2686_;
}
else
{
lean_object* v___x_2714_; 
lean_dec(v_a_2710_);
lean_inc_ref(v_pre_2665_);
lean_inc(v_goal_2663_);
v___x_2714_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(v_goal_2663_, v_pre_2665_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2714_, 1);
if (lean_obj_tag(v_a_2715_) == 1)
{
lean_object* v_val_2716_; lean_object* v_fst_2717_; lean_object* v_snd_2718_; 
lean_dec_ref(v_target_2666_);
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
v_val_2716_ = lean_ctor_get(v_a_2715_, 0);
lean_inc(v_val_2716_);
lean_dec_ref_known(v_a_2715_, 1);
v_fst_2717_ = lean_ctor_get(v_val_2716_, 0);
lean_inc(v_fst_2717_);
v_snd_2718_ = lean_ctor_get(v_val_2716_, 1);
lean_inc(v_snd_2718_);
lean_dec(v_val_2716_);
v_g_2687_ = v_fst_2717_;
v_h_2688_ = v_snd_2718_;
goto v___jp_2686_;
}
else
{
lean_object* v___x_2719_; 
lean_dec(v_a_2715_);
lean_inc(v_goal_2663_);
v___x_2719_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(v_goal_2663_, v_pre_2665_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
if (lean_obj_tag(v_a_2720_) == 1)
{
lean_object* v_val_2721_; 
lean_dec_ref(v_target_2666_);
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
v_val_2721_ = lean_ctor_get(v_a_2720_, 0);
lean_inc(v_val_2721_);
lean_dec_ref_known(v_a_2720_, 1);
v_g_2680_ = v_val_2721_;
goto v___jp_2679_;
}
else
{
lean_object* v___x_2722_; 
lean_dec(v_a_2720_);
lean_inc(v_goal_2663_);
v___x_2722_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_goal_2663_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2722_, 1);
if (lean_obj_tag(v_a_2723_) == 1)
{
lean_object* v_val_2724_; 
lean_dec_ref(v_target_2666_);
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
v_val_2724_ = lean_ctor_get(v_a_2723_, 0);
lean_inc(v_val_2724_);
lean_dec_ref_known(v_a_2723_, 1);
v_g_2680_ = v_val_2724_;
goto v___jp_2679_;
}
else
{
lean_object* v___x_2725_; 
lean_dec(v_a_2723_);
lean_inc_ref(v_pre_2665_);
lean_inc(v_goal_2663_);
v___x_2725_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(v_goal_2663_, v_pre_2665_, v_target_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2763_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2763_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2763_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
if (lean_obj_tag(v_a_2726_) == 1)
{
lean_object* v_val_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2741_; 
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
v_val_2730_ = lean_ctor_get(v_a_2726_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_a_2726_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2732_ = v_a_2726_;
v_isShared_2733_ = v_isSharedCheck_2741_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_val_2730_);
lean_dec(v_a_2726_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2741_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2734_, 0, v_scope_2662_);
lean_ctor_set(v___x_2734_, 1, v_val_2730_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2734_);
v___x_2736_ = v___x_2732_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2738_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2736_);
v___x_2738_ = v___x_2728_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_object* v___x_2742_; 
lean_del_object(v___x_2728_);
lean_dec(v_a_2726_);
v___x_2742_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(v_goal_2663_, v_00_u03b1_2664_, v_pre_2665_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
lean_dec_ref(v_pre_2665_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2754_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2754_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2754_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
if (lean_obj_tag(v_a_2743_) == 1)
{
lean_object* v_val_2747_; lean_object* v_fst_2748_; lean_object* v_snd_2749_; 
lean_del_object(v___x_2745_);
v_val_2747_ = lean_ctor_get(v_a_2743_, 0);
lean_inc(v_val_2747_);
lean_dec_ref_known(v_a_2743_, 1);
v_fst_2748_ = lean_ctor_get(v_val_2747_, 0);
lean_inc(v_fst_2748_);
v_snd_2749_ = lean_ctor_get(v_val_2747_, 1);
lean_inc(v_snd_2749_);
lean_dec(v_val_2747_);
v_g_2687_ = v_fst_2748_;
v_h_2688_ = v_snd_2749_;
goto v___jp_2686_;
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
lean_dec(v_a_2743_);
lean_dec_ref(v_scope_2662_);
v___x_2750_ = lean_box(0);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2750_);
v___x_2752_ = v___x_2745_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref(v_scope_2662_);
v_a_2755_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2742_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2742_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
lean_dec_ref(v_scope_2662_);
v_a_2764_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2725_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2725_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec_ref(v_target_2666_);
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
lean_dec_ref(v_scope_2662_);
v_a_2772_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2722_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2722_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec_ref(v_target_2666_);
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
lean_dec_ref(v_scope_2662_);
v_a_2780_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2719_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2719_);
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
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec_ref(v_target_2666_);
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
lean_dec_ref(v_scope_2662_);
v_a_2788_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2714_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2714_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v_target_2666_);
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
lean_dec_ref(v_scope_2662_);
v_a_2796_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2709_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2709_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec_ref(v_target_2666_);
lean_dec_ref(v_pre_2665_);
lean_dec(v_goal_2663_);
lean_dec_ref(v_scope_2662_);
v_a_2804_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2706_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2706_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
v___jp_2679_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2681_ = lean_box(0);
v___x_2682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2682_, 0, v_g_2680_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_scope_2662_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
v___jp_2686_:
{
lean_object* v_specs_2689_; lean_object* v_jps_2690_; lean_object* v_nextDeclIdx_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2704_; 
v_specs_2689_ = lean_ctor_get(v_scope_2662_, 0);
v_jps_2690_ = lean_ctor_get(v_scope_2662_, 1);
v_nextDeclIdx_2691_ = lean_ctor_get(v_scope_2662_, 3);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_scope_2662_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v_scope_2662_, 2);
lean_dec(v_unused_2705_);
v___x_2693_ = v_scope_2662_;
v_isShared_2694_ = v_isSharedCheck_2704_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_nextDeclIdx_2691_);
lean_inc(v_jps_2690_);
lean_inc(v_specs_2689_);
lean_dec(v_scope_2662_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2704_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2695_, 0, v_h_2688_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 2, v___x_2695_);
v___x_2697_ = v___x_2693_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_specs_2689_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_jps_2690_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v_nextDeclIdx_2691_);
v___x_2697_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2698_ = lean_box(0);
v___x_2699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2699_, 0, v_g_2687_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2697_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
v___x_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f___boxed(lean_object** _args){
lean_object* v_scope_2812_ = _args[0];
lean_object* v_goal_2813_ = _args[1];
lean_object* v_00_u03b1_2814_ = _args[2];
lean_object* v_pre_2815_ = _args[3];
lean_object* v_target_2816_ = _args[4];
lean_object* v_a_2817_ = _args[5];
lean_object* v_a_2818_ = _args[6];
lean_object* v_a_2819_ = _args[7];
lean_object* v_a_2820_ = _args[8];
lean_object* v_a_2821_ = _args[9];
lean_object* v_a_2822_ = _args[10];
lean_object* v_a_2823_ = _args[11];
lean_object* v_a_2824_ = _args[12];
lean_object* v_a_2825_ = _args[13];
lean_object* v_a_2826_ = _args[14];
lean_object* v_a_2827_ = _args[15];
lean_object* v_a_2828_ = _args[16];
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(v_scope_2812_, v_goal_2813_, v_00_u03b1_2814_, v_pre_2815_, v_target_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec_ref(v_00_u03b1_2814_);
return v_res_2829_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0(void){
_start:
{
lean_object* v___x_2830_; lean_object* v_dummy_2831_; 
v___x_2830_ = lean_box(0);
v_dummy_2831_ = l_Lean_Expr_sort___override(v___x_2830_);
return v_dummy_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(lean_object* v_goal_2832_, lean_object* v_info_2833_, lean_object* v_prog_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_head_2847_; lean_object* v_args_2848_; lean_object* v_excessArgs_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_head_2847_ = lean_ctor_get(v_info_2833_, 0);
lean_inc_ref(v_head_2847_);
v_args_2848_ = lean_ctor_get(v_info_2833_, 1);
lean_inc_ref(v_args_2848_);
v_excessArgs_2849_ = lean_ctor_get(v_info_2833_, 2);
lean_inc_ref(v_excessArgs_2849_);
lean_dec_ref(v_info_2833_);
v___x_2850_ = lean_unsigned_to_nat(7u);
v___x_2851_ = lean_array_set(v_args_2848_, v___x_2850_, v_prog_2834_);
v___x_2852_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_head_2847_, v___x_2851_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
lean_dec_ref(v___x_2851_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_a_2853_, v_excessArgs_2849_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
lean_dec_ref(v_excessArgs_2849_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
lean_inc(v_goal_2832_);
v___x_2856_ = l_Lean_MVarId_getType(v_goal_2832_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v_dummy_2858_; lean_object* v_nargs_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc_n(v_a_2857_, 2);
lean_dec_ref_known(v___x_2856_, 1);
v_dummy_2858_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0);
v_nargs_2859_ = l_Lean_Expr_getAppNumArgs(v_a_2857_);
lean_inc(v_nargs_2859_);
v___x_2860_ = lean_mk_array(v_nargs_2859_, v_dummy_2858_);
v___x_2861_ = lean_unsigned_to_nat(1u);
v___x_2862_ = lean_nat_sub(v_nargs_2859_, v___x_2861_);
lean_dec(v_nargs_2859_);
v___x_2863_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2857_, v___x_2860_, v___x_2862_);
v___x_2864_ = l_Lean_Expr_getAppFn(v_a_2857_);
lean_dec(v_a_2857_);
v___x_2865_ = lean_array_get_size(v___x_2863_);
v___x_2866_ = lean_nat_sub(v___x_2865_, v___x_2861_);
v___x_2867_ = lean_array_set(v___x_2863_, v___x_2866_, v_a_2855_);
lean_dec(v___x_2866_);
v___x_2868_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v___x_2864_, v___x_2867_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
lean_dec_ref(v___x_2867_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2870_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2870_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2832_, v_a_2869_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
return v___x_2870_;
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_goal_2832_);
v_a_2871_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2868_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2868_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_a_2855_);
lean_dec(v_goal_2832_);
v_a_2879_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2856_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2856_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_goal_2832_);
v_a_2887_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2854_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2854_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec_ref(v_excessArgs_2849_);
lean_dec(v_goal_2832_);
v_a_2895_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2852_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2852_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___boxed(lean_object* v_goal_2903_, lean_object* v_info_2904_, lean_object* v_prog_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_2903_, v_info_2904_, v_prog_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(lean_object* v_goal_2919_, lean_object* v_info_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_2920_);
if (lean_obj_tag(v___x_2933_) == 10)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = l_Lean_Expr_consumeMData(v___x_2933_);
lean_dec_ref_known(v___x_2933_, 2);
v___x_2935_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_2919_, v_info_2920_, v___x_2934_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2944_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2938_ = v___x_2935_;
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2940_, 0, v_a_2936_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2940_);
v___x_2942_ = v___x_2938_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
v_a_2945_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2935_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2935_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
else
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec_ref(v___x_2933_);
lean_dec_ref(v_info_2920_);
lean_dec(v_goal_2919_);
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f___boxed(lean_object* v_goal_2955_, lean_object* v_info_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(v_goal_2955_, v_info_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
lean_dec(v_a_2965_);
lean_dec_ref(v_a_2964_);
lean_dec(v_a_2963_);
lean_dec_ref(v_a_2962_);
lean_dec(v_a_2961_);
lean_dec_ref(v_a_2960_);
lean_dec(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object* v_revArgs_2970_, lean_object* v_start_2971_, lean_object* v_b_2972_, lean_object* v_i_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
uint8_t v___x_2981_; 
v___x_2981_ = lean_nat_dec_le(v_i_2973_, v_start_2971_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v_i_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2982_ = lean_unsigned_to_nat(1u);
v_i_2983_ = lean_nat_sub(v_i_2973_, v___x_2982_);
lean_dec(v_i_2973_);
v___x_2984_ = l_Lean_instInhabitedExpr;
v___x_2985_ = lean_array_get_borrowed(v___x_2984_, v_revArgs_2970_, v_i_2983_);
lean_inc(v___x_2985_);
v___x_2986_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_b_2972_, v___x_2985_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
v_b_2972_ = v_a_2987_;
v_i_2973_ = v_i_2983_;
goto _start;
}
else
{
lean_dec(v_i_2983_);
return v___x_2986_;
}
}
else
{
lean_object* v___x_2989_; 
lean_dec(v_i_2973_);
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v_b_2972_);
return v___x_2989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_revArgs_2990_, lean_object* v_start_2991_, lean_object* v_b_2992_, lean_object* v_i_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2990_, v_start_2991_, v_b_2992_, v_i_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v_start_2991_);
lean_dec_ref(v_revArgs_2990_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(lean_object* v_f_3002_, lean_object* v_revArgs_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_array_get_size(v_revArgs_3003_);
v___x_3018_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_3003_, v___x_3016_, v_f_3002_, v___x_3017_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0___boxed(lean_object* v_f_3019_, lean_object* v_revArgs_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_f_3019_, v_revArgs_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec_ref(v_revArgs_3020_);
return v_res_3033_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__0));
v___x_3036_ = l_Lean_stringToMessageData(v___x_3035_);
return v___x_3036_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__2));
v___x_3039_ = l_Lean_stringToMessageData(v___x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(lean_object* v_goal_3040_, lean_object* v_info_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3041_);
v___x_3055_ = l_Lean_Expr_getAppFn(v___x_3054_);
if (lean_obj_tag(v___x_3055_) == 8)
{
lean_object* v_declName_3056_; lean_object* v_type_3057_; lean_object* v_value_3058_; lean_object* v_body_3059_; uint8_t v_nondep_3060_; lean_object* v___x_3061_; 
v_declName_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc_n(v_declName_3056_, 2);
v_type_3057_ = lean_ctor_get(v___x_3055_, 1);
lean_inc_ref(v_type_3057_);
v_value_3058_ = lean_ctor_get(v___x_3055_, 2);
lean_inc_ref(v_value_3058_);
v_body_3059_ = lean_ctor_get(v___x_3055_, 3);
lean_inc_ref(v_body_3059_);
v_nondep_3060_ = lean_ctor_get_uint8(v___x_3055_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v___x_3055_, 4);
v___x_3061_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg(v_declName_3056_, v_value_3058_, v_a_3042_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v_appArgs_3064_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; uint8_t v___x_3118_; 
lean_dec_ref_known(v___x_3061_, 1);
v___x_3062_ = l_Lean_Expr_getAppNumArgs(v___x_3054_);
v___x_3063_ = lean_mk_empty_array_with_capacity(v___x_3062_);
lean_dec(v___x_3062_);
v_appArgs_3064_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3054_, v___x_3063_);
v___x_3118_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable(v_value_3058_);
if (v___x_3118_ == 0)
{
lean_object* v_options_3119_; lean_object* v_inheritedTraceOptions_3120_; uint8_t v_hasTrace_3121_; uint8_t v___x_3122_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; 
v_options_3119_ = lean_ctor_get(v_a_3051_, 2);
v_inheritedTraceOptions_3120_ = lean_ctor_get(v_a_3051_, 13);
v_hasTrace_3121_ = lean_ctor_get_uint8(v_options_3119_, sizeof(void*)*1);
v___x_3122_ = 1;
if (v_hasTrace_3121_ == 0)
{
v___y_3124_ = v_a_3042_;
v___y_3125_ = v_a_3043_;
v___y_3126_ = v_a_3044_;
v___y_3127_ = v_a_3045_;
v___y_3128_ = v_a_3046_;
v___y_3129_ = v_a_3047_;
v___y_3130_ = v_a_3048_;
v___y_3131_ = v_a_3049_;
v___y_3132_ = v_a_3050_;
v___y_3133_ = v_a_3051_;
v___y_3134_ = v_a_3052_;
goto v___jp_3123_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3233_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_3234_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_3235_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3120_, v_options_3119_, v___x_3234_);
if (v___x_3235_ == 0)
{
v___y_3124_ = v_a_3042_;
v___y_3125_ = v_a_3043_;
v___y_3126_ = v_a_3044_;
v___y_3127_ = v_a_3045_;
v___y_3128_ = v_a_3046_;
v___y_3129_ = v_a_3047_;
v___y_3130_ = v_a_3048_;
v___y_3131_ = v_a_3049_;
v___y_3132_ = v_a_3050_;
v___y_3133_ = v_a_3051_;
v___y_3134_ = v_a_3052_;
goto v___jp_3123_;
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3236_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3);
lean_inc(v_declName_3056_);
v___x_3237_ = l_Lean_MessageData_ofName(v_declName_3056_);
v___x_3238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3233_, v___x_3238_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_dec_ref_known(v___x_3239_, 1);
v___y_3124_ = v_a_3042_;
v___y_3125_ = v_a_3043_;
v___y_3126_ = v_a_3044_;
v___y_3127_ = v_a_3045_;
v___y_3128_ = v_a_3046_;
v___y_3129_ = v_a_3047_;
v___y_3130_ = v_a_3048_;
v___y_3131_ = v_a_3049_;
v___y_3132_ = v_a_3050_;
v___y_3133_ = v_a_3051_;
v___y_3134_ = v_a_3052_;
goto v___jp_3123_;
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref(v_appArgs_3064_);
lean_dec_ref(v_body_3059_);
lean_dec_ref(v_value_3058_);
lean_dec_ref(v_type_3057_);
lean_dec(v_declName_3056_);
lean_dec_ref(v_info_3041_);
lean_dec(v_goal_3040_);
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
v___jp_3123_:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_body_3059_, v_appArgs_3064_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec_ref(v_appArgs_3064_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v_head_3137_; lean_object* v_args_3138_; lean_object* v_excessArgs_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___x_3135_, 1);
v_head_3137_ = lean_ctor_get(v_info_3041_, 0);
lean_inc_ref(v_head_3137_);
v_args_3138_ = lean_ctor_get(v_info_3041_, 1);
lean_inc_ref(v_args_3138_);
v_excessArgs_3139_ = lean_ctor_get(v_info_3041_, 2);
lean_inc_ref(v_excessArgs_3139_);
lean_dec_ref(v_info_3041_);
v___x_3140_ = lean_unsigned_to_nat(7u);
v___x_3141_ = lean_array_set(v_args_3138_, v___x_3140_, v_a_3136_);
v___x_3142_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_head_3137_, v___x_3141_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec_ref(v___x_3141_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3144_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3142_, 1);
v___x_3144_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_a_3143_, v_excessArgs_3139_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec_ref(v_excessArgs_3139_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
lean_inc(v_goal_3040_);
v___x_3146_ = l_Lean_MVarId_getType(v_goal_3040_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v_dummy_3148_; lean_object* v_nargs_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc_n(v_a_3147_, 2);
lean_dec_ref_known(v___x_3146_, 1);
v_dummy_3148_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0);
v_nargs_3149_ = l_Lean_Expr_getAppNumArgs(v_a_3147_);
lean_inc(v_nargs_3149_);
v___x_3150_ = lean_mk_array(v_nargs_3149_, v_dummy_3148_);
v___x_3151_ = lean_unsigned_to_nat(1u);
v___x_3152_ = lean_nat_sub(v_nargs_3149_, v___x_3151_);
lean_dec(v_nargs_3149_);
v___x_3153_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3147_, v___x_3150_, v___x_3152_);
v___x_3154_ = l_Lean_Expr_getAppFn(v_a_3147_);
lean_dec(v_a_3147_);
v___x_3155_ = lean_array_get_size(v___x_3153_);
v___x_3156_ = lean_nat_sub(v___x_3155_, v___x_3151_);
v___x_3157_ = lean_array_set(v___x_3153_, v___x_3156_, v_a_3145_);
lean_dec(v___x_3156_);
v___x_3158_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v___x_3154_, v___x_3157_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec_ref(v___x_3157_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3160_ = l_Lean_Expr_letE___override(v_declName_3056_, v_type_3057_, v_value_3058_, v_a_3159_, v_nondep_3060_);
v___x_3161_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_3040_, v___x_3160_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
v___x_3163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0));
v___x_3164_ = l_Lean_Meta_Sym_intros(v_a_3162_, v___x_3163_, v___x_3122_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3176_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3167_ = v___x_3164_;
v_isShared_3168_ = v_isSharedCheck_3176_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3164_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3176_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
if (lean_obj_tag(v_a_3165_) == 1)
{
lean_object* v_mvarId_3169_; lean_object* v___x_3170_; lean_object* v___x_3172_; 
v_mvarId_3169_ = lean_ctor_get(v_a_3165_, 1);
lean_inc(v_mvarId_3169_);
lean_dec_ref_known(v_a_3165_, 2);
v___x_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3170_, 0, v_mvarId_3169_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 0, v___x_3170_);
v___x_3172_ = v___x_3167_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
else
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
lean_del_object(v___x_3167_);
lean_dec(v_a_3165_);
v___x_3174_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1);
v___x_3175_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3174_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
return v___x_3175_;
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
v_a_3177_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3164_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3164_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
v_a_3185_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3161_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3161_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec_ref(v_value_3058_);
lean_dec_ref(v_type_3057_);
lean_dec(v_declName_3056_);
lean_dec(v_goal_3040_);
v_a_3193_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3158_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3158_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v_a_3145_);
lean_dec_ref(v_value_3058_);
lean_dec_ref(v_type_3057_);
lean_dec(v_declName_3056_);
lean_dec(v_goal_3040_);
v_a_3201_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3146_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3146_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v_value_3058_);
lean_dec_ref(v_type_3057_);
lean_dec(v_declName_3056_);
lean_dec(v_goal_3040_);
v_a_3209_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3144_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3144_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec_ref(v_excessArgs_3139_);
lean_dec_ref(v_value_3058_);
lean_dec_ref(v_type_3057_);
lean_dec(v_declName_3056_);
lean_dec(v_goal_3040_);
v_a_3217_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3142_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3142_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec_ref(v_value_3058_);
lean_dec_ref(v_type_3057_);
lean_dec(v_declName_3056_);
lean_dec_ref(v_info_3041_);
lean_dec(v_goal_3040_);
v_a_3225_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3135_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3135_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
else
{
lean_object* v_options_3248_; uint8_t v_hasTrace_3249_; 
lean_dec_ref(v_type_3057_);
v_options_3248_ = lean_ctor_get(v_a_3051_, 2);
v_hasTrace_3249_ = lean_ctor_get_uint8(v_options_3248_, sizeof(void*)*1);
if (v_hasTrace_3249_ == 0)
{
lean_dec(v_declName_3056_);
v___y_3066_ = v_a_3042_;
v___y_3067_ = v_a_3043_;
v___y_3068_ = v_a_3044_;
v___y_3069_ = v_a_3045_;
v___y_3070_ = v_a_3046_;
v___y_3071_ = v_a_3047_;
v___y_3072_ = v_a_3048_;
v___y_3073_ = v_a_3049_;
v___y_3074_ = v_a_3050_;
v___y_3075_ = v_a_3051_;
v___y_3076_ = v_a_3052_;
goto v___jp_3065_;
}
else
{
lean_object* v_inheritedTraceOptions_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; 
v_inheritedTraceOptions_3250_ = lean_ctor_get(v_a_3051_, 13);
v___x_3251_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_3252_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_3253_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3250_, v_options_3248_, v___x_3252_);
if (v___x_3253_ == 0)
{
lean_dec(v_declName_3056_);
v___y_3066_ = v_a_3042_;
v___y_3067_ = v_a_3043_;
v___y_3068_ = v_a_3044_;
v___y_3069_ = v_a_3045_;
v___y_3070_ = v_a_3046_;
v___y_3071_ = v_a_3047_;
v___y_3072_ = v_a_3048_;
v___y_3073_ = v_a_3049_;
v___y_3074_ = v_a_3050_;
v___y_3075_ = v_a_3051_;
v___y_3076_ = v_a_3052_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3254_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11);
v___x_3255_ = l_Lean_MessageData_ofName(v_declName_3056_);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3251_, v___x_3256_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_dec_ref_known(v___x_3257_, 1);
v___y_3066_ = v_a_3042_;
v___y_3067_ = v_a_3043_;
v___y_3068_ = v_a_3044_;
v___y_3069_ = v_a_3045_;
v___y_3070_ = v_a_3046_;
v___y_3071_ = v_a_3047_;
v___y_3072_ = v_a_3048_;
v___y_3073_ = v_a_3049_;
v___y_3074_ = v_a_3050_;
v___y_3075_ = v_a_3051_;
v___y_3076_ = v_a_3052_;
goto v___jp_3065_;
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v_appArgs_3064_);
lean_dec_ref(v_body_3059_);
lean_dec_ref(v_value_3058_);
lean_dec_ref(v_info_3041_);
lean_dec(v_goal_3040_);
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
}
v___jp_3065_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3077_ = lean_unsigned_to_nat(1u);
v___x_3078_ = lean_mk_empty_array_with_capacity(v___x_3077_);
v___x_3079_ = lean_array_push(v___x_3078_, v_value_3058_);
v___x_3080_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_3059_, v___x_3079_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v___x_3082_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_a_3081_, v_appArgs_3064_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec_ref(v_appArgs_3064_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3084_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3082_, 1);
v___x_3084_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3040_, v_info_3041_, v_a_3083_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3093_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3089_, 0, v_a_3085_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3089_);
v___x_3091_ = v___x_3087_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
v_a_3094_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3084_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3084_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec_ref(v_info_3041_);
lean_dec(v_goal_3040_);
v_a_3102_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3082_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3082_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec_ref(v_appArgs_3064_);
lean_dec_ref(v_info_3041_);
lean_dec(v_goal_3040_);
v_a_3110_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3080_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3080_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec_ref(v_body_3059_);
lean_dec_ref(v_value_3058_);
lean_dec_ref(v_type_3057_);
lean_dec(v_declName_3056_);
lean_dec_ref(v___x_3054_);
lean_dec_ref(v_info_3041_);
lean_dec(v_goal_3040_);
v_a_3266_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3061_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3061_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec_ref(v___x_3055_);
lean_dec_ref(v___x_3054_);
lean_dec_ref(v_info_3041_);
lean_dec(v_goal_3040_);
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
return v___x_3275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___boxed(lean_object* v_goal_3276_, lean_object* v_info_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(v_goal_3276_, v_info_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0(lean_object* v_revArgs_3291_, lean_object* v_start_3292_, lean_object* v_b_3293_, lean_object* v_i_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_3291_, v_start_3292_, v_b_3293_, v_i_3294_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___boxed(lean_object* v_revArgs_3308_, lean_object* v_start_3309_, lean_object* v_b_3310_, lean_object* v_i_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0(v_revArgs_3308_, v_start_3309_, v_b_3310_, v_i_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v_start_3309_);
lean_dec_ref(v_revArgs_3308_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0(lean_object* v_arg_3325_, lean_object* v___x_3326_, lean_object* v___x_3327_, uint8_t v___x_3328_, lean_object* v_a_3329_, lean_object* v_fn_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v___x_3341_; 
lean_inc_ref(v_arg_3325_);
v___x_3341_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_arg_3325_, v___x_3326_, v___x_3327_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3343_, 0, v___x_3328_);
lean_ctor_set_uint8(v___x_3343_, 1, v___x_3328_);
v___x_3344_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_a_3329_, v_fn_3330_, v_arg_3325_, v___x_3343_, v_a_3342_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
return v___x_3344_;
}
else
{
lean_dec_ref(v_fn_3330_);
lean_dec_ref(v_a_3329_);
lean_dec_ref(v_arg_3325_);
return v___x_3341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0___boxed(lean_object* v_arg_3345_, lean_object* v___x_3346_, lean_object* v___x_3347_, lean_object* v___x_3348_, lean_object* v_a_3349_, lean_object* v_fn_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
uint8_t v___x_23412__boxed_3361_; lean_object* v_res_3362_; 
v___x_23412__boxed_3361_ = lean_unbox(v___x_3348_);
v_res_3362_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0(v_arg_3345_, v___x_3346_, v___x_3347_, v___x_23412__boxed_3361_, v_a_3349_, v_fn_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec(v___x_3347_);
lean_dec(v___x_3346_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1(uint8_t v___x_3366_, lean_object* v_goal_3367_, lean_object* v_args_3368_, lean_object* v_excessArgs_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
if (v___x_3366_ == 0)
{
lean_object* v_hypSimpMethods_3382_; 
v_hypSimpMethods_3382_ = lean_ctor_get(v___y_3370_, 2);
if (lean_obj_tag(v_hypSimpMethods_3382_) == 1)
{
lean_object* v_val_3383_; lean_object* v___x_3384_; 
v_val_3383_ = lean_ctor_get(v_hypSimpMethods_3382_, 0);
lean_inc(v_goal_3367_);
v___x_3384_ = l_Lean_MVarId_getType(v_goal_3367_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3475_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3475_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3475_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
if (lean_obj_tag(v_a_3385_) == 5)
{
lean_object* v_fn_3389_; lean_object* v_arg_3390_; lean_object* v___x_3391_; lean_object* v_simpState_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___f_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
lean_del_object(v___x_3387_);
v_fn_3389_ = lean_ctor_get(v_a_3385_, 0);
lean_inc_ref(v_fn_3389_);
v_arg_3390_ = lean_ctor_get(v_a_3385_, 1);
lean_inc_ref(v_arg_3390_);
v___x_3391_ = lean_st_ref_get(v___y_3371_);
v_simpState_3392_ = lean_ctor_get(v___x_3391_, 7);
lean_inc_ref(v_simpState_3392_);
lean_dec(v___x_3391_);
v___x_3393_ = lean_array_get_size(v_args_3368_);
v___x_3394_ = lean_array_get_size(v_excessArgs_3369_);
v___x_3395_ = lean_nat_add(v___x_3393_, v___x_3394_);
v___x_3396_ = lean_box(v___x_3366_);
v___f_3397_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3397_, 0, v_arg_3390_);
lean_closure_set(v___f_3397_, 1, v___x_3393_);
lean_closure_set(v___f_3397_, 2, v___x_3395_);
lean_closure_set(v___f_3397_, 3, v___x_3396_);
lean_closure_set(v___f_3397_, 4, v_a_3385_);
lean_closure_set(v___f_3397_, 5, v_fn_3389_);
v___x_3398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___closed__0));
lean_inc(v_val_3383_);
v___x_3399_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___f_3397_, v_val_3383_, v___x_3398_, v_simpState_3392_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v_fst_3401_; lean_object* v_snd_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3462_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3399_, 1);
v_fst_3401_ = lean_ctor_get(v_a_3400_, 0);
v_snd_3402_ = lean_ctor_get(v_a_3400_, 1);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_a_3400_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3404_ = v_a_3400_;
v_isShared_3405_ = v_isSharedCheck_3462_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_snd_3402_);
lean_inc(v_fst_3401_);
lean_dec(v_a_3400_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3462_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; lean_object* v_specBackwardRuleCache_3407_; lean_object* v_splitBackwardRuleCache_3408_; lean_object* v_latticeBackwardRuleCache_3409_; lean_object* v_frameBackwardRuleCache_3410_; lean_object* v_frameDB_3411_; lean_object* v_invariants_3412_; lean_object* v_vcs_3413_; lean_object* v_fuel_3414_; lean_object* v_inlineHandledInvariants_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3460_; 
v___x_3406_ = lean_st_ref_take(v___y_3371_);
v_specBackwardRuleCache_3407_ = lean_ctor_get(v___x_3406_, 0);
v_splitBackwardRuleCache_3408_ = lean_ctor_get(v___x_3406_, 1);
v_latticeBackwardRuleCache_3409_ = lean_ctor_get(v___x_3406_, 2);
v_frameBackwardRuleCache_3410_ = lean_ctor_get(v___x_3406_, 3);
v_frameDB_3411_ = lean_ctor_get(v___x_3406_, 4);
v_invariants_3412_ = lean_ctor_get(v___x_3406_, 5);
v_vcs_3413_ = lean_ctor_get(v___x_3406_, 6);
v_fuel_3414_ = lean_ctor_get(v___x_3406_, 8);
v_inlineHandledInvariants_3415_ = lean_ctor_get(v___x_3406_, 9);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v___x_3406_, 7);
lean_dec(v_unused_3461_);
v___x_3417_ = v___x_3406_;
v_isShared_3418_ = v_isSharedCheck_3460_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_inlineHandledInvariants_3415_);
lean_inc(v_fuel_3414_);
lean_inc(v_vcs_3413_);
lean_inc(v_invariants_3412_);
lean_inc(v_frameDB_3411_);
lean_inc(v_frameBackwardRuleCache_3410_);
lean_inc(v_latticeBackwardRuleCache_3409_);
lean_inc(v_splitBackwardRuleCache_3408_);
lean_inc(v_specBackwardRuleCache_3407_);
lean_dec(v___x_3406_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3460_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 7, v_snd_3402_);
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_specBackwardRuleCache_3407_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_splitBackwardRuleCache_3408_);
lean_ctor_set(v_reuseFailAlloc_3459_, 2, v_latticeBackwardRuleCache_3409_);
lean_ctor_set(v_reuseFailAlloc_3459_, 3, v_frameBackwardRuleCache_3410_);
lean_ctor_set(v_reuseFailAlloc_3459_, 4, v_frameDB_3411_);
lean_ctor_set(v_reuseFailAlloc_3459_, 5, v_invariants_3412_);
lean_ctor_set(v_reuseFailAlloc_3459_, 6, v_vcs_3413_);
lean_ctor_set(v_reuseFailAlloc_3459_, 7, v_snd_3402_);
lean_ctor_set(v_reuseFailAlloc_3459_, 8, v_fuel_3414_);
lean_ctor_set(v_reuseFailAlloc_3459_, 9, v_inlineHandledInvariants_3415_);
v___x_3420_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_st_ref_put(v___y_3371_, v___x_3420_);
v___x_3422_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_3401_, v_goal_3367_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3450_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3450_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3450_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
switch(lean_obj_tag(v_a_3423_))
{
case 0:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
lean_del_object(v___x_3404_);
v___x_3427_ = lean_box(0);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3427_);
v___x_3429_ = v___x_3425_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
case 1:
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
lean_del_object(v___x_3404_);
v___x_3431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3431_);
v___x_3433_ = v___x_3425_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
default: 
{
lean_object* v_mvarId_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3449_; 
v_mvarId_3435_ = lean_ctor_get(v_a_3423_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_a_3423_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3437_ = v_a_3423_;
v_isShared_3438_ = v_isSharedCheck_3449_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_mvarId_3435_);
lean_dec(v_a_3423_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3449_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3441_; 
v___x_3439_ = lean_box(0);
if (v_isShared_3405_ == 0)
{
lean_ctor_set_tag(v___x_3404_, 1);
lean_ctor_set(v___x_3404_, 1, v___x_3439_);
lean_ctor_set(v___x_3404_, 0, v_mvarId_3435_);
v___x_3441_ = v___x_3404_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_mvarId_3435_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3443_; 
if (v_isShared_3438_ == 0)
{
lean_ctor_set_tag(v___x_3437_, 1);
lean_ctor_set(v___x_3437_, 0, v___x_3441_);
v___x_3443_ = v___x_3437_;
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
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3443_);
v___x_3445_ = v___x_3425_;
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
}
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_del_object(v___x_3404_);
v_a_3451_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3422_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3422_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec(v_goal_3367_);
v_a_3463_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3399_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3399_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
lean_dec(v_a_3385_);
lean_dec(v_goal_3367_);
v___x_3471_ = lean_box(0);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3471_);
v___x_3473_ = v___x_3387_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec(v_goal_3367_);
v_a_3476_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3384_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3384_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
lean_dec(v_goal_3367_);
v___x_3484_ = lean_box(0);
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
return v___x_3485_;
}
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec(v_goal_3367_);
v___x_3486_ = lean_box(0);
v___x_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
return v___x_3487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___boxed(lean_object* v___x_3488_, lean_object* v_goal_3489_, lean_object* v_args_3490_, lean_object* v_excessArgs_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
uint8_t v___x_23474__boxed_3504_; lean_object* v_res_3505_; 
v___x_23474__boxed_3504_ = lean_unbox(v___x_3488_);
v_res_3505_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1(v___x_23474__boxed_3504_, v_goal_3489_, v_args_3490_, v_excessArgs_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec_ref(v_excessArgs_3491_);
lean_dec_ref(v_args_3490_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(lean_object* v_goal_3506_, lean_object* v_info_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_){
_start:
{
lean_object* v_args_3520_; lean_object* v_excessArgs_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; lean_object* v___x_3525_; lean_object* v___y_3526_; lean_object* v___x_3527_; 
v_args_3520_ = lean_ctor_get(v_info_3507_, 1);
lean_inc_ref(v_args_3520_);
v_excessArgs_3521_ = lean_ctor_get(v_info_3507_, 2);
lean_inc_ref(v_excessArgs_3521_);
lean_dec_ref(v_info_3507_);
v___x_3522_ = lean_array_get_size(v_excessArgs_3521_);
v___x_3523_ = lean_unsigned_to_nat(0u);
v___x_3524_ = lean_nat_dec_eq(v___x_3522_, v___x_3523_);
v___x_3525_ = lean_box(v___x_3524_);
lean_inc(v_goal_3506_);
v___y_3526_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___boxed), 16, 4);
lean_closure_set(v___y_3526_, 0, v___x_3525_);
lean_closure_set(v___y_3526_, 1, v_goal_3506_);
lean_closure_set(v___y_3526_, 2, v_args_3520_);
lean_closure_set(v___y_3526_, 3, v_excessArgs_3521_);
v___x_3527_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_3506_, v___y_3526_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___boxed(lean_object* v_goal_3528_, lean_object* v_info_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(v_goal_3528_, v_info_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(lean_object* v_as_x27_3543_, lean_object* v_b_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
if (lean_obj_tag(v_as_x27_3543_) == 0)
{
lean_object* v___x_3554_; 
v___x_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3554_, 0, v_b_3544_);
return v___x_3554_;
}
else
{
lean_object* v_head_3555_; lean_object* v_tail_3556_; lean_object* v___x_3557_; 
v_head_3555_ = lean_ctor_get(v_as_x27_3543_, 0);
v_tail_3556_ = lean_ctor_get(v_as_x27_3543_, 1);
lean_inc(v_head_3555_);
v___x_3557_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_head_3555_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
switch(lean_obj_tag(v_a_3558_))
{
case 0:
{
lean_object* v___x_3559_; 
lean_inc(v_head_3555_);
v___x_3559_ = lean_array_push(v_b_3544_, v_head_3555_);
v_as_x27_3543_ = v_tail_3556_;
v_b_3544_ = v___x_3559_;
goto _start;
}
case 1:
{
v_as_x27_3543_ = v_tail_3556_;
goto _start;
}
default: 
{
lean_object* v_mvarId_3562_; lean_object* v___x_3563_; 
v_mvarId_3562_ = lean_ctor_get(v_a_3558_, 0);
lean_inc(v_mvarId_3562_);
lean_dec_ref_known(v_a_3558_, 1);
v___x_3563_ = lean_array_push(v_b_3544_, v_mvarId_3562_);
v_as_x27_3543_ = v_tail_3556_;
v_b_3544_ = v___x_3563_;
goto _start;
}
}
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_dec_ref(v_b_3544_);
v_a_3565_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3557_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3557_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg___boxed(lean_object* v_as_x27_3573_, lean_object* v_b_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3573_, v_b_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v_as_x27_3573_);
return v_res_3584_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__0));
v___x_3587_ = l_Lean_stringToMessageData(v___x_3586_);
return v___x_3587_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3(void){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__2));
v___x_3590_ = l_Lean_stringToMessageData(v___x_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(lean_object* v_goal_3591_, lean_object* v_info_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3592_);
lean_inc_ref(v___x_3605_);
v___x_3606_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v___x_3605_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3749_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3749_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3749_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
if (lean_obj_tag(v_a_3607_) == 1)
{
lean_object* v_val_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3744_; 
lean_del_object(v___x_3609_);
v_val_3611_ = lean_ctor_get(v_a_3607_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v_a_3607_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3613_ = v_a_3607_;
v_isShared_3614_ = v_isSharedCheck_3744_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_val_3611_);
lean_dec(v_a_3607_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3744_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; 
if (lean_obj_tag(v_val_3611_) == 2)
{
lean_object* v_keyedConfig_3683_; uint8_t v_trackZetaDelta_3684_; lean_object* v_zetaDeltaSet_3685_; lean_object* v_lctx_3686_; lean_object* v_localInstances_3687_; lean_object* v_defEqCtx_x3f_3688_; lean_object* v_synthPendingDepth_3689_; lean_object* v_customCanUnfoldPredicate_x3f_3690_; uint8_t v_univApprox_3691_; uint8_t v_inTypeClassResolution_3692_; uint8_t v_cacheInferType_3693_; uint8_t v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v_keyedConfig_3683_ = lean_ctor_get(v_a_3600_, 0);
v_trackZetaDelta_3684_ = lean_ctor_get_uint8(v_a_3600_, sizeof(void*)*7);
v_zetaDeltaSet_3685_ = lean_ctor_get(v_a_3600_, 1);
v_lctx_3686_ = lean_ctor_get(v_a_3600_, 2);
v_localInstances_3687_ = lean_ctor_get(v_a_3600_, 3);
v_defEqCtx_x3f_3688_ = lean_ctor_get(v_a_3600_, 4);
v_synthPendingDepth_3689_ = lean_ctor_get(v_a_3600_, 5);
v_customCanUnfoldPredicate_x3f_3690_ = lean_ctor_get(v_a_3600_, 6);
v_univApprox_3691_ = lean_ctor_get_uint8(v_a_3600_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3692_ = lean_ctor_get_uint8(v_a_3600_, sizeof(void*)*7 + 2);
v_cacheInferType_3693_ = lean_ctor_get_uint8(v_a_3600_, sizeof(void*)*7 + 3);
v___x_3694_ = 2;
lean_inc_ref(v_keyedConfig_3683_);
v___x_3695_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3694_, v_keyedConfig_3683_);
lean_inc(v_customCanUnfoldPredicate_x3f_3690_);
lean_inc(v_synthPendingDepth_3689_);
lean_inc(v_defEqCtx_x3f_3688_);
lean_inc_ref(v_localInstances_3687_);
lean_inc_ref(v_lctx_3686_);
lean_inc(v_zetaDeltaSet_3685_);
v___x_3696_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3696_, 0, v___x_3695_);
lean_ctor_set(v___x_3696_, 1, v_zetaDeltaSet_3685_);
lean_ctor_set(v___x_3696_, 2, v_lctx_3686_);
lean_ctor_set(v___x_3696_, 3, v_localInstances_3687_);
lean_ctor_set(v___x_3696_, 4, v_defEqCtx_x3f_3688_);
lean_ctor_set(v___x_3696_, 5, v_synthPendingDepth_3689_);
lean_ctor_set(v___x_3696_, 6, v_customCanUnfoldPredicate_x3f_3690_);
lean_ctor_set_uint8(v___x_3696_, sizeof(void*)*7, v_trackZetaDelta_3684_);
lean_ctor_set_uint8(v___x_3696_, sizeof(void*)*7 + 1, v_univApprox_3691_);
lean_ctor_set_uint8(v___x_3696_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3692_);
lean_ctor_set_uint8(v___x_3696_, sizeof(void*)*7 + 3, v_cacheInferType_3693_);
v___x_3697_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_3605_, v___x_3696_, v_a_3601_, v_a_3602_, v_a_3603_);
lean_dec_ref_known(v___x_3696_, 7);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref_known(v___x_3697_, 1);
if (lean_obj_tag(v_a_3698_) == 1)
{
lean_object* v_val_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3735_; 
lean_dec_ref_known(v_val_3611_, 1);
lean_del_object(v___x_3613_);
lean_dec_ref(v___x_3605_);
v_val_3699_ = lean_ctor_get(v_a_3698_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_a_3698_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3701_ = v_a_3698_;
v_isShared_3702_ = v_isSharedCheck_3735_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_val_3699_);
lean_dec(v_a_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3735_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_Meta_Sym_shareCommonInc(v_val_3699_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; lean_object* v___x_3705_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_a_3704_);
lean_dec_ref_known(v___x_3703_, 1);
v___x_3705_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3591_, v_info_3592_, v_a_3704_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3718_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3708_ = v___x_3705_;
v_isShared_3709_ = v_isSharedCheck_3718_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3718_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3713_; 
v___x_3710_ = lean_box(0);
v___x_3711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3711_, 0, v_a_3706_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v___x_3711_);
v___x_3713_ = v___x_3701_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3711_);
v___x_3713_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
lean_object* v___x_3715_; 
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 0, v___x_3713_);
v___x_3715_ = v___x_3708_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_del_object(v___x_3701_);
v_a_3719_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3705_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3705_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_del_object(v___x_3701_);
lean_dec_ref(v_info_3592_);
lean_dec(v_goal_3591_);
v_a_3727_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3703_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3703_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
else
{
lean_dec(v_a_3698_);
v___y_3616_ = v_a_3593_;
v___y_3617_ = v_a_3594_;
v___y_3618_ = v_a_3595_;
v___y_3619_ = v_a_3596_;
v___y_3620_ = v_a_3597_;
v___y_3621_ = v_a_3598_;
v___y_3622_ = v_a_3599_;
v___y_3623_ = v_a_3600_;
v___y_3624_ = v_a_3601_;
v___y_3625_ = v_a_3602_;
v___y_3626_ = v_a_3603_;
goto v___jp_3615_;
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec_ref_known(v_val_3611_, 1);
lean_del_object(v___x_3613_);
lean_dec_ref(v___x_3605_);
lean_dec_ref(v_info_3592_);
lean_dec(v_goal_3591_);
v_a_3736_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3697_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3697_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
v___y_3616_ = v_a_3593_;
v___y_3617_ = v_a_3594_;
v___y_3618_ = v_a_3595_;
v___y_3619_ = v_a_3596_;
v___y_3620_ = v_a_3597_;
v___y_3621_ = v_a_3598_;
v___y_3622_ = v_a_3599_;
v___y_3623_ = v_a_3600_;
v___y_3624_ = v_a_3601_;
v___y_3625_ = v_a_3602_;
v___y_3626_ = v_a_3603_;
goto v___jp_3615_;
}
v___jp_3615_:
{
lean_object* v___x_3627_; 
v___x_3627_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_val_3611_, v_info_3592_, v___y_3617_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3628_);
lean_dec_ref_known(v___x_3627_, 1);
v___x_3629_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1);
v___x_3630_ = l_Lean_indentExpr(v___x_3605_);
lean_inc_ref(v___x_3630_);
v___x_3631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3629_);
lean_ctor_set(v___x_3631_, 1, v___x_3630_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v___x_3631_);
v___x_3633_ = v___x_3613_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_3628_, v_goal_3591_, v___x_3633_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_a_3635_);
lean_dec_ref_known(v___x_3634_, 1);
if (lean_obj_tag(v_a_3635_) == 1)
{
lean_object* v_mvarIds_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3662_; 
lean_dec_ref(v___x_3630_);
v_mvarIds_3636_ = lean_ctor_get(v_a_3635_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_a_3635_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3638_ = v_a_3635_;
v_isShared_3639_ = v_isSharedCheck_3662_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_mvarIds_3636_);
lean_dec(v_a_3635_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3662_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0));
v___x_3641_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_mvarIds_3636_, v___x_3640_, v___y_3616_, v___y_3617_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v_mvarIds_3636_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3653_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3653_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3653_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3646_ = lean_array_to_list(v_a_3642_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v___x_3646_);
v___x_3648_ = v___x_3638_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3646_);
v___x_3648_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3650_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3648_);
v___x_3650_ = v___x_3644_;
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
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_del_object(v___x_3638_);
v_a_3654_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3641_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3641_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
lean_dec(v_a_3635_);
v___x_3663_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
lean_ctor_set(v___x_3664_, 1, v___x_3630_);
v___x_3665_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3664_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
return v___x_3665_;
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec_ref(v___x_3630_);
v_a_3666_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3634_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3634_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_del_object(v___x_3613_);
lean_dec_ref(v___x_3605_);
lean_dec(v_goal_3591_);
v_a_3675_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3627_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3627_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_dec(v_a_3607_);
lean_dec_ref(v___x_3605_);
lean_dec_ref(v_info_3592_);
lean_dec(v_goal_3591_);
v___x_3745_ = lean_box(0);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3745_);
v___x_3747_ = v___x_3609_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec_ref(v___x_3605_);
lean_dec_ref(v_info_3592_);
lean_dec(v_goal_3591_);
v_a_3750_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3606_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3606_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___boxed(lean_object* v_goal_3758_, lean_object* v_info_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(v_goal_3758_, v_info_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_);
lean_dec(v_a_3770_);
lean_dec_ref(v_a_3769_);
lean_dec(v_a_3768_);
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0(lean_object* v_as_3773_, lean_object* v_as_x27_3774_, lean_object* v_b_3775_, lean_object* v_a_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3774_, v_b_3775_, v___y_3777_, v___y_3778_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___boxed(lean_object* v_as_3790_, lean_object* v_as_x27_3791_, lean_object* v_b_3792_, lean_object* v_a_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0(v_as_3790_, v_as_x27_3791_, v_b_3792_, v_a_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v_as_x27_3791_);
lean_dec(v_as_3790_);
return v_res_3806_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1(void){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__0));
v___x_3809_ = l_Lean_stringToMessageData(v___x_3808_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(lean_object* v_goal_3810_, lean_object* v_info_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_){
_start:
{
lean_object* v___x_3824_; lean_object* v_f_3825_; lean_object* v___x_3826_; 
v___x_3824_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3811_);
v_f_3825_ = l_Lean_Expr_getAppFn(v___x_3824_);
v___x_3826_ = l_Lean_Expr_fvarId_x3f(v_f_3825_);
lean_dec_ref(v_f_3825_);
if (lean_obj_tag(v___x_3826_) == 1)
{
lean_object* v_val_3827_; uint8_t v___x_3828_; lean_object* v___x_3829_; 
v_val_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc_n(v_val_3827_, 2);
lean_dec_ref_known(v___x_3826_, 1);
v___x_3828_ = 0;
v___x_3829_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_3827_, v___x_3828_, v_a_3819_, v_a_3821_, v_a_3822_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3917_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3832_ = v___x_3829_;
v_isShared_3833_ = v_isSharedCheck_3917_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3829_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3917_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
if (lean_obj_tag(v_a_3830_) == 1)
{
lean_object* v_val_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3912_; 
lean_del_object(v___x_3832_);
v_val_3834_ = lean_ctor_get(v_a_3830_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_a_3830_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3836_ = v_a_3830_;
v_isShared_3837_ = v_isSharedCheck_3912_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_val_3834_);
lean_dec(v_a_3830_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3912_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v_options_3884_; uint8_t v_hasTrace_3885_; 
v_options_3884_ = lean_ctor_get(v_a_3821_, 2);
v_hasTrace_3885_ = lean_ctor_get_uint8(v_options_3884_, sizeof(void*)*1);
if (v_hasTrace_3885_ == 0)
{
lean_dec(v_val_3827_);
v___y_3839_ = v_a_3812_;
v___y_3840_ = v_a_3813_;
v___y_3841_ = v_a_3814_;
v___y_3842_ = v_a_3815_;
v___y_3843_ = v_a_3816_;
v___y_3844_ = v_a_3817_;
v___y_3845_ = v_a_3818_;
v___y_3846_ = v_a_3819_;
v___y_3847_ = v_a_3820_;
v___y_3848_ = v_a_3821_;
v___y_3849_ = v_a_3822_;
goto v___jp_3838_;
}
else
{
lean_object* v_inheritedTraceOptions_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v_inheritedTraceOptions_3886_ = lean_ctor_get(v_a_3821_, 13);
v___x_3887_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_3888_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_3889_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3886_, v_options_3884_, v___x_3888_);
if (v___x_3889_ == 0)
{
lean_dec(v_val_3827_);
v___y_3839_ = v_a_3812_;
v___y_3840_ = v_a_3813_;
v___y_3841_ = v_a_3814_;
v___y_3842_ = v_a_3815_;
v___y_3843_ = v_a_3816_;
v___y_3844_ = v_a_3817_;
v___y_3845_ = v_a_3818_;
v___y_3846_ = v_a_3819_;
v___y_3847_ = v_a_3820_;
v___y_3848_ = v_a_3821_;
v___y_3849_ = v_a_3822_;
goto v___jp_3838_;
}
else
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Lean_FVarId_getUserName___redArg(v_val_3827_, v_a_3819_, v_a_3821_, v_a_3822_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v___x_3892_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1);
v___x_3893_ = l_Lean_MessageData_ofName(v_a_3891_);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3892_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3887_, v___x_3894_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_dec_ref_known(v___x_3895_, 1);
v___y_3839_ = v_a_3812_;
v___y_3840_ = v_a_3813_;
v___y_3841_ = v_a_3814_;
v___y_3842_ = v_a_3815_;
v___y_3843_ = v_a_3816_;
v___y_3844_ = v_a_3817_;
v___y_3845_ = v_a_3818_;
v___y_3846_ = v_a_3819_;
v___y_3847_ = v_a_3820_;
v___y_3848_ = v_a_3821_;
v___y_3849_ = v_a_3822_;
goto v___jp_3838_;
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_dec_ref(v___x_3824_);
lean_dec_ref(v_info_3811_);
lean_dec(v_goal_3810_);
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3895_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3895_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
else
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_dec_ref(v___x_3824_);
lean_dec_ref(v_info_3811_);
lean_dec(v_goal_3810_);
v_a_3904_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3890_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3890_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
v___jp_3838_:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3850_ = l_Lean_Expr_getAppNumArgs(v___x_3824_);
v___x_3851_ = lean_mk_empty_array_with_capacity(v___x_3850_);
lean_dec(v___x_3850_);
v___x_3852_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3824_, v___x_3851_);
v___x_3853_ = l_Lean_Expr_betaRev(v_val_3834_, v___x_3852_, v___x_3828_, v___x_3828_);
lean_dec_ref(v___x_3852_);
v___x_3854_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3853_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3856_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref_known(v___x_3854_, 1);
v___x_3856_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3810_, v_info_3811_, v_a_3855_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3867_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3859_ = v___x_3856_;
v_isShared_3860_ = v_isSharedCheck_3867_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3856_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3867_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v_a_3857_);
v___x_3862_ = v___x_3836_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3864_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v___x_3862_);
v___x_3864_ = v___x_3859_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3862_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_del_object(v___x_3836_);
v_a_3868_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3856_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3856_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
lean_del_object(v___x_3836_);
lean_dec_ref(v_info_3811_);
lean_dec(v_goal_3810_);
v_a_3876_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3854_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3854_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
}
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec(v_a_3830_);
lean_dec(v_val_3827_);
lean_dec_ref(v___x_3824_);
lean_dec_ref(v_info_3811_);
lean_dec(v_goal_3810_);
v___x_3913_ = lean_box(0);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v___x_3913_);
v___x_3915_ = v___x_3832_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec(v_val_3827_);
lean_dec_ref(v___x_3824_);
lean_dec_ref(v_info_3811_);
lean_dec(v_goal_3810_);
v_a_3918_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3829_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3829_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
else
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_dec(v___x_3826_);
lean_dec_ref(v___x_3824_);
lean_dec_ref(v_info_3811_);
lean_dec(v_goal_3810_);
v___x_3926_ = lean_box(0);
v___x_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
return v___x_3927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___boxed(lean_object* v_goal_3928_, lean_object* v_info_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(v_goal_3928_, v_info_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f(lean_object* v_goal_3943_, lean_object* v_info_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_){
_start:
{
lean_object* v___x_3957_; lean_object* v_a_3959_; lean_object* v_f_4020_; 
v___x_3957_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3944_);
v_f_4020_ = l_Lean_Expr_getAppFn(v___x_3957_);
if (lean_obj_tag(v_f_4020_) == 11)
{
lean_object* v_keyedConfig_4021_; uint8_t v_trackZetaDelta_4022_; lean_object* v_zetaDeltaSet_4023_; lean_object* v_lctx_4024_; lean_object* v_localInstances_4025_; lean_object* v_defEqCtx_x3f_4026_; lean_object* v_synthPendingDepth_4027_; lean_object* v_customCanUnfoldPredicate_x3f_4028_; uint8_t v_univApprox_4029_; uint8_t v_inTypeClassResolution_4030_; uint8_t v_cacheInferType_4031_; uint8_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v_keyedConfig_4021_ = lean_ctor_get(v_a_3952_, 0);
v_trackZetaDelta_4022_ = lean_ctor_get_uint8(v_a_3952_, sizeof(void*)*7);
v_zetaDeltaSet_4023_ = lean_ctor_get(v_a_3952_, 1);
v_lctx_4024_ = lean_ctor_get(v_a_3952_, 2);
v_localInstances_4025_ = lean_ctor_get(v_a_3952_, 3);
v_defEqCtx_x3f_4026_ = lean_ctor_get(v_a_3952_, 4);
v_synthPendingDepth_4027_ = lean_ctor_get(v_a_3952_, 5);
v_customCanUnfoldPredicate_x3f_4028_ = lean_ctor_get(v_a_3952_, 6);
v_univApprox_4029_ = lean_ctor_get_uint8(v_a_3952_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4030_ = lean_ctor_get_uint8(v_a_3952_, sizeof(void*)*7 + 2);
v_cacheInferType_4031_ = lean_ctor_get_uint8(v_a_3952_, sizeof(void*)*7 + 3);
v___x_4032_ = 3;
lean_inc_ref(v_keyedConfig_4021_);
v___x_4033_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4032_, v_keyedConfig_4021_);
lean_inc(v_customCanUnfoldPredicate_x3f_4028_);
lean_inc(v_synthPendingDepth_4027_);
lean_inc(v_defEqCtx_x3f_4026_);
lean_inc_ref(v_localInstances_4025_);
lean_inc_ref(v_lctx_4024_);
lean_inc(v_zetaDeltaSet_4023_);
v___x_4034_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
lean_ctor_set(v___x_4034_, 1, v_zetaDeltaSet_4023_);
lean_ctor_set(v___x_4034_, 2, v_lctx_4024_);
lean_ctor_set(v___x_4034_, 3, v_localInstances_4025_);
lean_ctor_set(v___x_4034_, 4, v_defEqCtx_x3f_4026_);
lean_ctor_set(v___x_4034_, 5, v_synthPendingDepth_4027_);
lean_ctor_set(v___x_4034_, 6, v_customCanUnfoldPredicate_x3f_4028_);
lean_ctor_set_uint8(v___x_4034_, sizeof(void*)*7, v_trackZetaDelta_4022_);
lean_ctor_set_uint8(v___x_4034_, sizeof(void*)*7 + 1, v_univApprox_4029_);
lean_ctor_set_uint8(v___x_4034_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4030_);
lean_ctor_set_uint8(v___x_4034_, sizeof(void*)*7 + 3, v_cacheInferType_4031_);
v___x_4035_ = l_Lean_Meta_reduceProj_x3f(v_f_4020_, v___x_4034_, v_a_3953_, v_a_3954_, v_a_3955_);
lean_dec_ref_known(v___x_4034_, 7);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
lean_dec_ref_known(v___x_4035_, 1);
v_a_3959_ = v_a_4036_;
goto v___jp_3958_;
}
else
{
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4037_; 
v_a_4037_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4035_, 1);
v_a_3959_ = v_a_4037_;
goto v___jp_3958_;
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec_ref(v___x_3957_);
lean_dec_ref(v_info_3944_);
lean_dec(v_goal_3943_);
v_a_4038_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4035_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4035_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
else
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
lean_dec_ref(v_f_4020_);
lean_dec_ref(v___x_3957_);
lean_dec_ref(v_info_3944_);
lean_dec(v_goal_3943_);
v___x_4046_ = lean_box(0);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
v___jp_3958_:
{
if (lean_obj_tag(v_a_3959_) == 1)
{
lean_object* v_val_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_4017_; 
v_val_3960_ = lean_ctor_get(v_a_3959_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v_a_3959_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_3962_ = v_a_3959_;
v_isShared_3963_ = v_isSharedCheck_4017_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_val_3960_);
lean_dec(v_a_3959_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_4017_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_Meta_Sym_unfoldReducible(v_val_3960_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3966_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3964_, 1);
v___x_3966_ = l_Lean_Meta_Sym_shareCommon(v_a_3965_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___x_3966_, 1);
v___x_3968_ = l_Lean_Expr_getAppNumArgs(v___x_3957_);
v___x_3969_ = lean_mk_empty_array_with_capacity(v___x_3968_);
lean_dec(v___x_3968_);
v___x_3970_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3957_, v___x_3969_);
v___x_3971_ = l_Lean_Meta_Sym_betaRevS(v_a_3967_, v___x_3970_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; lean_object* v___x_3973_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3972_);
lean_dec_ref_known(v___x_3971_, 1);
v___x_3973_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3943_, v_info_3944_, v_a_3972_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3984_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3976_ = v___x_3973_;
v_isShared_3977_ = v_isSharedCheck_3984_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3984_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 0, v_a_3974_);
v___x_3979_ = v___x_3962_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3981_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v___x_3979_);
v___x_3981_ = v___x_3976_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3979_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
else
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3992_; 
lean_del_object(v___x_3962_);
v_a_3985_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3987_ = v___x_3973_;
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3973_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_del_object(v___x_3962_);
lean_dec_ref(v_info_3944_);
lean_dec(v_goal_3943_);
v_a_3993_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3971_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3971_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_del_object(v___x_3962_);
lean_dec_ref(v___x_3957_);
lean_dec_ref(v_info_3944_);
lean_dec(v_goal_3943_);
v_a_4001_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3966_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3966_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_del_object(v___x_3962_);
lean_dec_ref(v___x_3957_);
lean_dec_ref(v_info_3944_);
lean_dec(v_goal_3943_);
v_a_4009_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_3964_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_3964_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
lean_dec(v_a_3959_);
lean_dec_ref(v___x_3957_);
lean_dec_ref(v_info_3944_);
lean_dec(v_goal_3943_);
v___x_4018_ = lean_box(0);
v___x_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4018_);
return v___x_4019_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f___boxed(lean_object* v_goal_4048_, lean_object* v_info_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f(v_goal_4048_, v_info_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
lean_dec(v_a_4058_);
lean_dec_ref(v_a_4057_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
return v_res_4062_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0));
v___x_4065_ = l_Lean_stringToMessageData(v___x_4064_);
return v___x_4065_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3(void){
_start:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4067_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2));
v___x_4068_ = l_Lean_stringToMessageData(v___x_4067_);
return v___x_4068_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4));
v___x_4071_ = l_Lean_stringToMessageData(v___x_4070_);
return v___x_4071_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6));
v___x_4074_ = l_Lean_stringToMessageData(v___x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object* v_a_4075_, lean_object* v_a_4076_){
_start:
{
if (lean_obj_tag(v_a_4075_) == 0)
{
lean_object* v___x_4077_; 
v___x_4077_ = l_List_reverse___redArg(v_a_4076_);
return v___x_4077_;
}
else
{
lean_object* v_head_4078_; lean_object* v_tail_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4107_; 
v_head_4078_ = lean_ctor_get(v_a_4075_, 0);
v_tail_4079_ = lean_ctor_get(v_a_4075_, 1);
v_isSharedCheck_4107_ = !lean_is_exclusive(v_a_4075_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4081_ = v_a_4075_;
v_isShared_4082_ = v_isSharedCheck_4107_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_tail_4079_);
lean_inc(v_head_4078_);
lean_dec(v_a_4075_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4107_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___y_4084_; 
switch(lean_obj_tag(v_head_4078_))
{
case 0:
{
lean_object* v_declName_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v_declName_4089_ = lean_ctor_get(v_head_4078_, 0);
lean_inc(v_declName_4089_);
lean_dec_ref_known(v_head_4078_, 1);
v___x_4090_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_4091_ = l_Lean_MessageData_ofName(v_declName_4089_);
v___x_4092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___y_4084_ = v___x_4092_;
goto v___jp_4083_;
}
case 1:
{
lean_object* v_fvarId_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v_fvarId_4093_ = lean_ctor_get(v_head_4078_, 0);
lean_inc(v_fvarId_4093_);
lean_dec_ref_known(v_head_4078_, 1);
v___x_4094_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_4095_ = l_Lean_mkFVar(v_fvarId_4093_);
v___x_4096_ = l_Lean_MessageData_ofExpr(v___x_4095_);
v___x_4097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4094_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
v___y_4084_ = v___x_4097_;
goto v___jp_4083_;
}
default: 
{
lean_object* v_ref_4098_; lean_object* v_proof_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v_ref_4098_ = lean_ctor_get(v_head_4078_, 1);
lean_inc(v_ref_4098_);
v_proof_4099_ = lean_ctor_get(v_head_4078_, 2);
lean_inc_ref(v_proof_4099_);
lean_dec_ref_known(v_head_4078_, 3);
v___x_4100_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_4101_ = l_Lean_MessageData_ofSyntax(v_ref_4098_);
v___x_4102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4100_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
v___x_4103_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_4104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4102_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = l_Lean_MessageData_ofExpr(v_proof_4099_);
v___x_4106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4104_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v___y_4084_ = v___x_4106_;
goto v___jp_4083_;
}
}
v___jp_4083_:
{
lean_object* v___x_4086_; 
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 1, v_a_4076_);
lean_ctor_set(v___x_4081_, 0, v___y_4084_);
v___x_4086_ = v___x_4081_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___y_4084_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v_a_4076_);
v___x_4086_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
v_a_4075_ = v_tail_4079_;
v_a_4076_ = v___x_4086_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t v_sz_4108_, size_t v_i_4109_, lean_object* v_bs_4110_){
_start:
{
uint8_t v___x_4111_; 
v___x_4111_ = lean_usize_dec_lt(v_i_4109_, v_sz_4108_);
if (v___x_4111_ == 0)
{
return v_bs_4110_;
}
else
{
lean_object* v_v_4112_; lean_object* v_proof_4113_; lean_object* v___x_4114_; lean_object* v_bs_x27_4115_; size_t v___x_4116_; size_t v___x_4117_; lean_object* v___x_4118_; 
v_v_4112_ = lean_array_uget_borrowed(v_bs_4110_, v_i_4109_);
v_proof_4113_ = lean_ctor_get(v_v_4112_, 1);
lean_inc_ref(v_proof_4113_);
v___x_4114_ = lean_unsigned_to_nat(0u);
v_bs_x27_4115_ = lean_array_uset(v_bs_4110_, v_i_4109_, v___x_4114_);
v___x_4116_ = ((size_t)1ULL);
v___x_4117_ = lean_usize_add(v_i_4109_, v___x_4116_);
v___x_4118_ = lean_array_uset(v_bs_x27_4115_, v_i_4109_, v_proof_4113_);
v_i_4109_ = v___x_4117_;
v_bs_4110_ = v___x_4118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object* v_sz_4120_, lean_object* v_i_4121_, lean_object* v_bs_4122_){
_start:
{
size_t v_sz_boxed_4123_; size_t v_i_boxed_4124_; lean_object* v_res_4125_; 
v_sz_boxed_4123_ = lean_unbox_usize(v_sz_4120_);
lean_dec(v_sz_4120_);
v_i_boxed_4124_ = lean_unbox_usize(v_i_4121_);
lean_dec(v_i_4121_);
v_res_4125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_boxed_4123_, v_i_boxed_4124_, v_bs_4122_);
return v_res_4125_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1(void){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0));
v___x_4128_ = l_Lean_stringToMessageData(v___x_4127_);
return v___x_4128_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2));
v___x_4131_ = l_Lean_stringToMessageData(v___x_4130_);
return v___x_4131_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4133_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4));
v___x_4134_ = l_Lean_stringToMessageData(v___x_4133_);
return v___x_4134_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6));
v___x_4137_ = l_Lean_stringToMessageData(v___x_4136_);
return v___x_4137_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9(void){
_start:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8));
v___x_4140_ = l_Lean_stringToMessageData(v___x_4139_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object* v_prog_4141_, lean_object* v_monad_4142_, lean_object* v_thms_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
uint8_t v_errorOnMissingSpec_4150_; 
v_errorOnMissingSpec_4150_ = lean_ctor_get_uint8(v_a_4144_, sizeof(void*)*5 + 2);
if (v_errorOnMissingSpec_4150_ == 0)
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4151_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_4151_, 0, v_prog_4141_);
lean_ctor_set(v___x_4151_, 1, v_monad_4142_);
lean_ctor_set(v___x_4151_, 2, v_thms_4143_);
v___x_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
v___x_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
return v___x_4153_;
}
else
{
lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; 
v___x_4154_ = lean_array_get_size(v_thms_4143_);
v___x_4155_ = lean_unsigned_to_nat(0u);
v___x_4156_ = lean_nat_dec_eq(v___x_4154_, v___x_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; size_t v_sz_4166_; size_t v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4157_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1);
v___x_4158_ = l_Lean_MessageData_ofExpr(v_prog_4141_);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4157_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3);
v___x_4161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = l_Lean_MessageData_ofExpr(v_monad_4142_);
v___x_4163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4161_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
v___x_4164_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5);
v___x_4165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4163_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v_sz_4166_ = lean_array_size(v_thms_4143_);
v___x_4167_ = ((size_t)0ULL);
v___x_4168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_4166_, v___x_4167_, v_thms_4143_);
v___x_4169_ = lean_array_to_list(v___x_4168_);
v___x_4170_ = lean_box(0);
v___x_4171_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1(v___x_4169_, v___x_4170_);
v___x_4172_ = l_Lean_MessageData_ofList(v___x_4171_);
v___x_4173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4165_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
v___x_4174_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_4175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4173_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
v___x_4176_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_4175_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
return v___x_4176_;
}
else
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
lean_dec_ref(v_thms_4143_);
lean_dec_ref(v_monad_4142_);
v___x_4177_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9);
v___x_4178_ = l_Lean_MessageData_ofExpr(v_prog_4141_);
v___x_4179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4177_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_4181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4179_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_4181_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
return v___x_4182_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object* v_prog_4183_, lean_object* v_monad_4184_, lean_object* v_thms_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_4183_, v_monad_4184_, v_thms_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
lean_dec_ref(v_a_4186_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec(lean_object* v_prog_4193_, lean_object* v_monad_4194_, lean_object* v_thms_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_4193_, v_monad_4194_, v_thms_4195_, v_a_4196_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object* v_prog_4209_, lean_object* v_monad_4210_, lean_object* v_thms_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec(v_prog_4209_, v_monad_4210_, v_thms_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
lean_dec(v_a_4222_);
lean_dec_ref(v_a_4221_);
lean_dec(v_a_4220_);
lean_dec_ref(v_a_4219_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
return v_res_4224_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1(void){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__0));
v___x_4227_ = l_Lean_stringToMessageData(v___x_4226_);
return v___x_4227_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3(void){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__2));
v___x_4230_ = l_Lean_stringToMessageData(v___x_4229_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(lean_object* v_prog_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v_untilPat_x3f_4240_; 
v_untilPat_x3f_4240_ = lean_ctor_get(v_a_4232_, 4);
if (lean_obj_tag(v_untilPat_x3f_4240_) == 1)
{
lean_object* v_val_4241_; uint8_t v___x_4242_; lean_object* v___x_4243_; 
v_val_4241_ = lean_ctor_get(v_untilPat_x3f_4240_, 0);
v___x_4242_ = 1;
lean_inc_ref(v_prog_4231_);
lean_inc(v_val_4241_);
v___x_4243_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_val_4241_, v_prog_4231_, v___x_4242_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4290_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4246_ = v___x_4243_;
v_isShared_4247_ = v_isSharedCheck_4290_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4243_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4290_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
if (lean_obj_tag(v_a_4244_) == 0)
{
uint8_t v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4251_; 
lean_dec_ref(v_prog_4231_);
v___x_4248_ = 0;
v___x_4249_ = lean_box(v___x_4248_);
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v___x_4249_);
v___x_4251_ = v___x_4246_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4249_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
else
{
lean_object* v_options_4253_; uint8_t v_hasTrace_4254_; 
lean_dec_ref_known(v_a_4244_, 1);
v_options_4253_ = lean_ctor_get(v_a_4237_, 2);
v_hasTrace_4254_ = lean_ctor_get_uint8(v_options_4253_, sizeof(void*)*1);
if (v_hasTrace_4254_ == 0)
{
lean_object* v___x_4255_; lean_object* v___x_4257_; 
lean_dec_ref(v_prog_4231_);
v___x_4255_ = lean_box(v___x_4242_);
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v___x_4255_);
v___x_4257_ = v___x_4246_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4255_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
else
{
lean_object* v_inheritedTraceOptions_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v_inheritedTraceOptions_4259_ = lean_ctor_get(v_a_4237_, 13);
v___x_4260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_4261_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_4262_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4259_, v_options_4253_, v___x_4261_);
if (v___x_4262_ == 0)
{
lean_object* v___x_4263_; lean_object* v___x_4265_; 
lean_dec_ref(v_prog_4231_);
v___x_4263_ = lean_box(v___x_4242_);
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v___x_4263_);
v___x_4265_ = v___x_4246_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4263_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
else
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
lean_del_object(v___x_4246_);
v___x_4267_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1);
v___x_4268_ = l_Lean_MessageData_ofExpr(v_prog_4231_);
v___x_4269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4267_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3);
v___x_4271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4269_);
lean_ctor_set(v___x_4271_, 1, v___x_4270_);
v___x_4272_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4260_, v___x_4271_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4280_; 
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4280_ == 0)
{
lean_object* v_unused_4281_; 
v_unused_4281_ = lean_ctor_get(v___x_4272_, 0);
lean_dec(v_unused_4281_);
v___x_4274_ = v___x_4272_;
v_isShared_4275_ = v_isSharedCheck_4280_;
goto v_resetjp_4273_;
}
else
{
lean_dec(v___x_4272_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4280_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4276_; lean_object* v___x_4278_; 
v___x_4276_ = lean_box(v___x_4242_);
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 0, v___x_4276_);
v___x_4278_ = v___x_4274_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4276_);
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
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
v_a_4282_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4272_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4272_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
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
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
lean_dec_ref(v_prog_4231_);
v_a_4291_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4243_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4243_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
else
{
uint8_t v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
lean_dec_ref(v_prog_4231_);
v___x_4299_ = 0;
v___x_4300_ = lean_box(v___x_4299_);
v___x_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4300_);
return v___x_4301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___boxed(lean_object* v_prog_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v_prog_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_);
lean_dec(v_a_4309_);
lean_dec_ref(v_a_4308_);
lean_dec(v_a_4307_);
lean_dec_ref(v_a_4306_);
lean_dec(v_a_4305_);
lean_dec_ref(v_a_4304_);
lean_dec_ref(v_a_4303_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern(lean_object* v_prog_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v___x_4325_; 
v___x_4325_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v_prog_4312_, v_a_4313_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___boxed(lean_object* v_prog_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern(v_prog_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_);
lean_dec(v_a_4337_);
lean_dec_ref(v_a_4336_);
lean_dec(v_a_4335_);
lean_dec_ref(v_a_4334_);
lean_dec(v_a_4333_);
lean_dec_ref(v_a_4332_);
lean_dec(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(lean_object* v_k_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v_b_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v___x_4354_; 
lean_inc(v___y_4352_);
lean_inc_ref(v___y_4351_);
lean_inc(v___y_4350_);
lean_inc_ref(v___y_4349_);
lean_inc(v___y_4347_);
lean_inc_ref(v___y_4346_);
lean_inc(v___y_4345_);
lean_inc_ref(v___y_4344_);
lean_inc(v___y_4343_);
lean_inc(v___y_4342_);
lean_inc_ref(v___y_4341_);
v___x_4354_ = lean_apply_13(v_k_4340_, v_b_4348_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, lean_box(0));
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v_b_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(v_k_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v_b_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(lean_object* v_name_4370_, lean_object* v_type_4371_, lean_object* v_val_4372_, lean_object* v_k_4373_, uint8_t v_nondep_4374_, uint8_t v_kind_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v___f_4388_; lean_object* v___x_4389_; 
lean_inc(v___y_4382_);
lean_inc_ref(v___y_4381_);
lean_inc(v___y_4380_);
lean_inc_ref(v___y_4379_);
lean_inc(v___y_4378_);
lean_inc(v___y_4377_);
lean_inc_ref(v___y_4376_);
v___f_4388_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_4388_, 0, v_k_4373_);
lean_closure_set(v___f_4388_, 1, v___y_4376_);
lean_closure_set(v___f_4388_, 2, v___y_4377_);
lean_closure_set(v___f_4388_, 3, v___y_4378_);
lean_closure_set(v___f_4388_, 4, v___y_4379_);
lean_closure_set(v___f_4388_, 5, v___y_4380_);
lean_closure_set(v___f_4388_, 6, v___y_4381_);
lean_closure_set(v___f_4388_, 7, v___y_4382_);
v___x_4389_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_4370_, v_type_4371_, v_val_4372_, v___f_4388_, v_nondep_4374_, v_kind_4375_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
if (lean_obj_tag(v___x_4389_) == 0)
{
return v___x_4389_;
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4389_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4389_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_name_4398_ = _args[0];
lean_object* v_type_4399_ = _args[1];
lean_object* v_val_4400_ = _args[2];
lean_object* v_k_4401_ = _args[3];
lean_object* v_nondep_4402_ = _args[4];
lean_object* v_kind_4403_ = _args[5];
lean_object* v___y_4404_ = _args[6];
lean_object* v___y_4405_ = _args[7];
lean_object* v___y_4406_ = _args[8];
lean_object* v___y_4407_ = _args[9];
lean_object* v___y_4408_ = _args[10];
lean_object* v___y_4409_ = _args[11];
lean_object* v___y_4410_ = _args[12];
lean_object* v___y_4411_ = _args[13];
lean_object* v___y_4412_ = _args[14];
lean_object* v___y_4413_ = _args[15];
lean_object* v___y_4414_ = _args[16];
lean_object* v___y_4415_ = _args[17];
_start:
{
uint8_t v_nondep_boxed_4416_; uint8_t v_kind_boxed_4417_; lean_object* v_res_4418_; 
v_nondep_boxed_4416_ = lean_unbox(v_nondep_4402_);
v_kind_boxed_4417_ = lean_unbox(v_kind_4403_);
v_res_4418_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4398_, v_type_4399_, v_val_4400_, v_k_4401_, v_nondep_boxed_4416_, v_kind_boxed_4417_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0(lean_object* v_00_u03b1_4419_, lean_object* v_name_4420_, lean_object* v_type_4421_, lean_object* v_val_4422_, lean_object* v_k_4423_, uint8_t v_nondep_4424_, uint8_t v_kind_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v___x_4438_; 
v___x_4438_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4420_, v_type_4421_, v_val_4422_, v_k_4423_, v_nondep_4424_, v_kind_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_4439_ = _args[0];
lean_object* v_name_4440_ = _args[1];
lean_object* v_type_4441_ = _args[2];
lean_object* v_val_4442_ = _args[3];
lean_object* v_k_4443_ = _args[4];
lean_object* v_nondep_4444_ = _args[5];
lean_object* v_kind_4445_ = _args[6];
lean_object* v___y_4446_ = _args[7];
lean_object* v___y_4447_ = _args[8];
lean_object* v___y_4448_ = _args[9];
lean_object* v___y_4449_ = _args[10];
lean_object* v___y_4450_ = _args[11];
lean_object* v___y_4451_ = _args[12];
lean_object* v___y_4452_ = _args[13];
lean_object* v___y_4453_ = _args[14];
lean_object* v___y_4454_ = _args[15];
lean_object* v___y_4455_ = _args[16];
lean_object* v___y_4456_ = _args[17];
lean_object* v___y_4457_ = _args[18];
_start:
{
uint8_t v_nondep_boxed_4458_; uint8_t v_kind_boxed_4459_; lean_object* v_res_4460_; 
v_nondep_boxed_4458_ = lean_unbox(v_nondep_4444_);
v_kind_boxed_4459_ = lean_unbox(v_kind_4445_);
v_res_4460_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0(v_00_u03b1_4439_, v_name_4440_, v_type_4441_, v_val_4442_, v_k_4443_, v_nondep_boxed_4458_, v_kind_boxed_4459_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0___boxed(lean_object* v_acc_4461_, lean_object* v_declInfos_4462_, lean_object* v_k_4463_, lean_object* v_fv_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0(v_acc_4461_, v_declInfos_4462_, v_k_4463_, v_fv_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(lean_object* v_declInfos_4478_, lean_object* v_k_4479_, lean_object* v_acc_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; uint8_t v___x_4495_; 
v___x_4493_ = lean_array_get_size(v_acc_4480_);
v___x_4494_ = lean_array_get_size(v_declInfos_4478_);
v___x_4495_ = lean_nat_dec_lt(v___x_4493_, v___x_4494_);
if (v___x_4495_ == 0)
{
lean_object* v___x_4496_; 
lean_dec_ref(v_declInfos_4478_);
lean_inc(v_a_4491_);
lean_inc_ref(v_a_4490_);
lean_inc(v_a_4489_);
lean_inc_ref(v_a_4488_);
lean_inc(v_a_4487_);
lean_inc_ref(v_a_4486_);
lean_inc(v_a_4485_);
lean_inc_ref(v_a_4484_);
lean_inc(v_a_4483_);
lean_inc(v_a_4482_);
lean_inc_ref(v_a_4481_);
v___x_4496_ = lean_apply_13(v_k_4479_, v_acc_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, lean_box(0));
return v___x_4496_;
}
else
{
lean_object* v___x_4497_; lean_object* v_snd_4498_; lean_object* v_fst_4499_; lean_object* v_fst_4500_; lean_object* v_snd_4501_; lean_object* v___f_4502_; uint8_t v___x_4503_; uint8_t v___x_4504_; lean_object* v___x_4505_; 
v___x_4497_ = lean_array_fget_borrowed(v_declInfos_4478_, v___x_4493_);
v_snd_4498_ = lean_ctor_get(v___x_4497_, 1);
v_fst_4499_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_fst_4499_);
v_fst_4500_ = lean_ctor_get(v_snd_4498_, 0);
lean_inc(v_fst_4500_);
v_snd_4501_ = lean_ctor_get(v_snd_4498_, 1);
lean_inc(v_snd_4501_);
v___f_4502_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4502_, 0, v_acc_4480_);
lean_closure_set(v___f_4502_, 1, v_declInfos_4478_);
lean_closure_set(v___f_4502_, 2, v_k_4479_);
v___x_4503_ = 0;
v___x_4504_ = 0;
v___x_4505_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_fst_4499_, v_fst_4500_, v_snd_4501_, v___f_4502_, v___x_4503_, v___x_4504_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_);
return v___x_4505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0(lean_object* v_acc_4506_, lean_object* v_declInfos_4507_, lean_object* v_k_4508_, lean_object* v_fv_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4522_ = lean_array_push(v_acc_4506_, v_fv_4509_);
v___x_4523_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4507_, v_k_4508_, v___x_4522_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___boxed(lean_object* v_declInfos_4524_, lean_object* v_k_4525_, lean_object* v_acc_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4524_, v_k_4525_, v_acc_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
lean_dec(v_a_4537_);
lean_dec_ref(v_a_4536_);
lean_dec(v_a_4535_);
lean_dec_ref(v_a_4534_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_match__1_splitter___redArg(lean_object* v_x_4540_, lean_object* v_h__1_4541_){
_start:
{
lean_object* v_snd_4542_; lean_object* v_fst_4543_; lean_object* v_fst_4544_; lean_object* v_snd_4545_; lean_object* v___x_4546_; 
v_snd_4542_ = lean_ctor_get(v_x_4540_, 1);
lean_inc(v_snd_4542_);
v_fst_4543_ = lean_ctor_get(v_x_4540_, 0);
lean_inc(v_fst_4543_);
lean_dec_ref(v_x_4540_);
v_fst_4544_ = lean_ctor_get(v_snd_4542_, 0);
lean_inc(v_fst_4544_);
v_snd_4545_ = lean_ctor_get(v_snd_4542_, 1);
lean_inc(v_snd_4545_);
lean_dec(v_snd_4542_);
v___x_4546_ = lean_apply_3(v_h__1_4541_, v_fst_4543_, v_fst_4544_, v_snd_4545_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_match__1_splitter(lean_object* v_motive_4547_, lean_object* v_x_4548_, lean_object* v_h__1_4549_){
_start:
{
lean_object* v_snd_4550_; lean_object* v_fst_4551_; lean_object* v_fst_4552_; lean_object* v_snd_4553_; lean_object* v___x_4554_; 
v_snd_4550_ = lean_ctor_get(v_x_4548_, 1);
lean_inc(v_snd_4550_);
v_fst_4551_ = lean_ctor_get(v_x_4548_, 0);
lean_inc(v_fst_4551_);
lean_dec_ref(v_x_4548_);
v_fst_4552_ = lean_ctor_get(v_snd_4550_, 0);
lean_inc(v_fst_4552_);
v_snd_4553_ = lean_ctor_get(v_snd_4550_, 1);
lean_inc(v_snd_4553_);
lean_dec(v_snd_4550_);
v___x_4554_ = lean_apply_3(v_h__1_4549_, v_fst_4551_, v_fst_4552_, v_snd_4553_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND(lean_object* v_declInfos_4557_, lean_object* v_k_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___closed__0));
v___x_4572_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4557_, v_k_4558_, v___x_4571_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___boxed(lean_object* v_declInfos_4573_, lean_object* v_k_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND(v_declInfos_4573_, v_k_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
lean_dec(v_a_4585_);
lean_dec_ref(v_a_4584_);
lean_dec(v_a_4583_);
lean_dec_ref(v_a_4582_);
lean_dec(v_a_4581_);
lean_dec_ref(v_a_4580_);
lean_dec(v_a_4579_);
lean_dec_ref(v_a_4578_);
lean_dec(v_a_4577_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
return v_res_4587_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0(lean_object* v_x_4588_){
_start:
{
uint8_t v___x_4589_; 
v___x_4589_ = 0;
return v___x_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0___boxed(lean_object* v_x_4590_){
_start:
{
uint8_t v_res_4591_; lean_object* v_r_4592_; 
v_res_4591_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0(v_x_4590_);
lean_dec(v_x_4590_);
v_r_4592_ = lean_box(v_res_4591_);
return v_r_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1(lean_object* v_frameStx_4593_, lean_object* v___x_4594_, uint8_t v___x_4595_, lean_object* v___x_4596_, lean_object* v_fvs_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v___x_4605_; 
v___x_4605_ = l_Lean_Elab_Term_elabTermEnsuringType(v_frameStx_4593_, v___x_4594_, v___x_4595_, v___x_4595_, v___x_4596_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; uint8_t v___x_4607_; lean_object* v___x_4608_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_a_4606_);
lean_dec_ref_known(v___x_4605_, 1);
v___x_4607_ = 0;
v___x_4608_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4607_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4608_) == 0)
{
uint8_t v___x_4609_; lean_object* v___x_4610_; 
lean_dec_ref_known(v___x_4608_, 1);
v___x_4609_ = 1;
v___x_4610_ = l_Lean_Meta_mkLetFVars(v_fvs_4597_, v_a_4606_, v___x_4595_, v___x_4595_, v___x_4609_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
return v___x_4610_;
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
lean_dec(v_a_4606_);
v_a_4611_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4608_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4608_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
else
{
return v___x_4605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1___boxed(lean_object* v_frameStx_4619_, lean_object* v___x_4620_, lean_object* v___x_4621_, lean_object* v___x_4622_, lean_object* v_fvs_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_){
_start:
{
uint8_t v___x_12406__boxed_4631_; lean_object* v_res_4632_; 
v___x_12406__boxed_4631_ = lean_unbox(v___x_4621_);
v_res_4632_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1(v_frameStx_4619_, v___x_4620_, v___x_12406__boxed_4631_, v___x_4622_, v_fvs_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec_ref(v_fvs_4623_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2(lean_object* v_resourceTy_4638_, lean_object* v_frameStx_4639_, lean_object* v___f_4640_, lean_object* v_fvs_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_){
_start:
{
lean_object* v___x_4654_; uint8_t v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___f_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4654_, 0, v_resourceTy_4638_);
v___x_4655_ = 1;
v___x_4656_ = lean_box(0);
v___x_4657_ = lean_box(v___x_4655_);
v___f_4658_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4658_, 0, v_frameStx_4639_);
lean_closure_set(v___f_4658_, 1, v___x_4654_);
lean_closure_set(v___f_4658_, 2, v___x_4657_);
lean_closure_set(v___f_4658_, 3, v___x_4656_);
lean_closure_set(v___f_4658_, 4, v_fvs_4641_);
v___x_4659_ = lean_box(0);
v___x_4660_ = lean_box(1);
v___x_4661_ = 0;
v___x_4662_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__0));
v___x_4663_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_4663_, 0, v___x_4656_);
lean_ctor_set(v___x_4663_, 1, v___x_4659_);
lean_ctor_set(v___x_4663_, 2, v___x_4656_);
lean_ctor_set(v___x_4663_, 3, v___f_4640_);
lean_ctor_set(v___x_4663_, 4, v___x_4660_);
lean_ctor_set(v___x_4663_, 5, v___x_4660_);
lean_ctor_set(v___x_4663_, 6, v___x_4656_);
lean_ctor_set(v___x_4663_, 7, v___x_4662_);
lean_ctor_set_uint8(v___x_4663_, sizeof(void*)*8, v___x_4655_);
lean_ctor_set_uint8(v___x_4663_, sizeof(void*)*8 + 1, v___x_4655_);
lean_ctor_set_uint8(v___x_4663_, sizeof(void*)*8 + 2, v___x_4655_);
lean_ctor_set_uint8(v___x_4663_, sizeof(void*)*8 + 3, v___x_4655_);
lean_ctor_set_uint8(v___x_4663_, sizeof(void*)*8 + 4, v___x_4661_);
lean_ctor_set_uint8(v___x_4663_, sizeof(void*)*8 + 5, v___x_4661_);
lean_ctor_set_uint8(v___x_4663_, sizeof(void*)*8 + 6, v___x_4661_);
lean_ctor_set_uint8(v___x_4663_, sizeof(void*)*8 + 7, v___x_4661_);
lean_ctor_set_uint8(v___x_4663_, sizeof(void*)*8 + 8, v___x_4655_);
lean_ctor_set_uint8(v___x_4663_, sizeof(void*)*8 + 9, v___x_4661_);
lean_ctor_set_uint8(v___x_4663_, sizeof(void*)*8 + 10, v___x_4655_);
v___x_4664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__1));
v___x_4665_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_4658_, v___x_4663_, v___x_4664_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v_fst_4667_; lean_object* v___x_4668_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4665_, 1);
v_fst_4667_ = lean_ctor_get(v_a_4666_, 0);
lean_inc(v_fst_4667_);
lean_dec(v_a_4666_);
v___x_4668_ = l_Lean_Meta_Sym_instantiateMVarsS(v_fst_4667_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
return v___x_4668_;
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4676_; 
v_a_4669_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4671_ = v___x_4665_;
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4665_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4674_; 
if (v_isShared_4672_ == 0)
{
v___x_4674_ = v___x_4671_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4669_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___boxed(lean_object* v_resourceTy_4677_, lean_object* v_frameStx_4678_, lean_object* v___f_4679_, lean_object* v_fvs_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2(v_resourceTy_4677_, v_frameStx_4678_, v___f_4679_, v_fvs_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
return v_res_4693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(lean_object* v_as_4694_, size_t v_sz_4695_, size_t v_i_4696_, lean_object* v_b_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_){
_start:
{
lean_object* v_a_4704_; uint8_t v___x_4708_; 
v___x_4708_ = lean_usize_dec_lt(v_i_4696_, v_sz_4695_);
if (v___x_4708_ == 0)
{
lean_object* v___x_4709_; 
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v_b_4697_);
return v___x_4709_;
}
else
{
lean_object* v_snd_4710_; lean_object* v_fst_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4757_; 
v_snd_4710_ = lean_ctor_get(v_b_4697_, 1);
v_fst_4711_ = lean_ctor_get(v_b_4697_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v_b_4697_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4713_ = v_b_4697_;
v_isShared_4714_ = v_isSharedCheck_4757_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_snd_4710_);
lean_inc(v_fst_4711_);
lean_dec(v_b_4697_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4757_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v_array_4715_; lean_object* v_start_4716_; lean_object* v_stop_4717_; uint8_t v___x_4718_; 
v_array_4715_ = lean_ctor_get(v_snd_4710_, 0);
v_start_4716_ = lean_ctor_get(v_snd_4710_, 1);
v_stop_4717_ = lean_ctor_get(v_snd_4710_, 2);
v___x_4718_ = lean_nat_dec_lt(v_start_4716_, v_stop_4717_);
if (v___x_4718_ == 0)
{
lean_object* v___x_4720_; 
if (v_isShared_4714_ == 0)
{
v___x_4720_ = v___x_4713_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_fst_4711_);
lean_ctor_set(v_reuseFailAlloc_4722_, 1, v_snd_4710_);
v___x_4720_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4721_; 
v___x_4721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
return v___x_4721_;
}
}
else
{
lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4753_; 
lean_inc(v_stop_4717_);
lean_inc(v_start_4716_);
lean_inc_ref(v_array_4715_);
v_isSharedCheck_4753_ = !lean_is_exclusive(v_snd_4710_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; lean_object* v_unused_4755_; lean_object* v_unused_4756_; 
v_unused_4754_ = lean_ctor_get(v_snd_4710_, 2);
lean_dec(v_unused_4754_);
v_unused_4755_ = lean_ctor_get(v_snd_4710_, 1);
lean_dec(v_unused_4755_);
v_unused_4756_ = lean_ctor_get(v_snd_4710_, 0);
lean_dec(v_unused_4756_);
v___x_4724_ = v_snd_4710_;
v_isShared_4725_ = v_isSharedCheck_4753_;
goto v_resetjp_4723_;
}
else
{
lean_dec(v_snd_4710_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4753_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v_a_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4731_; 
v_a_4726_ = lean_array_uget_borrowed(v_as_4694_, v_i_4696_);
v___x_4727_ = lean_array_fget(v_array_4715_, v_start_4716_);
v___x_4728_ = lean_unsigned_to_nat(1u);
v___x_4729_ = lean_nat_add(v_start_4716_, v___x_4728_);
lean_dec(v_start_4716_);
if (v_isShared_4725_ == 0)
{
lean_ctor_set(v___x_4724_, 1, v___x_4729_);
v___x_4731_ = v___x_4724_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_array_4715_);
lean_ctor_set(v_reuseFailAlloc_4752_, 1, v___x_4729_);
lean_ctor_set(v_reuseFailAlloc_4752_, 2, v_stop_4717_);
v___x_4731_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
if (lean_obj_tag(v_a_4726_) == 1)
{
lean_object* v_val_4732_; lean_object* v___x_4733_; 
v_val_4732_ = lean_ctor_get(v_a_4726_, 0);
lean_inc(v___y_4701_);
lean_inc_ref(v___y_4700_);
lean_inc(v___y_4699_);
lean_inc_ref(v___y_4698_);
lean_inc(v___x_4727_);
v___x_4733_ = lean_infer_type(v___x_4727_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; lean_object* v___x_4736_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___x_4733_, 1);
if (v_isShared_4714_ == 0)
{
lean_ctor_set(v___x_4713_, 1, v___x_4727_);
lean_ctor_set(v___x_4713_, 0, v_a_4734_);
v___x_4736_ = v___x_4713_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_a_4734_);
lean_ctor_set(v_reuseFailAlloc_4740_, 1, v___x_4727_);
v___x_4736_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
lean_inc(v_val_4732_);
v___x_4737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4737_, 0, v_val_4732_);
lean_ctor_set(v___x_4737_, 1, v___x_4736_);
v___x_4738_ = lean_array_push(v_fst_4711_, v___x_4737_);
v___x_4739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4739_, 0, v___x_4738_);
lean_ctor_set(v___x_4739_, 1, v___x_4731_);
v_a_4704_ = v___x_4739_;
goto v___jp_4703_;
}
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
lean_dec_ref(v___x_4731_);
lean_dec(v___x_4727_);
lean_del_object(v___x_4713_);
lean_dec(v_fst_4711_);
v_a_4741_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4743_ = v___x_4733_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4733_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4746_; 
if (v_isShared_4744_ == 0)
{
v___x_4746_ = v___x_4743_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4741_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
else
{
lean_object* v___x_4750_; 
lean_dec(v___x_4727_);
if (v_isShared_4714_ == 0)
{
lean_ctor_set(v___x_4713_, 1, v___x_4731_);
v___x_4750_ = v___x_4713_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_fst_4711_);
lean_ctor_set(v_reuseFailAlloc_4751_, 1, v___x_4731_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
v_a_4704_ = v___x_4750_;
goto v___jp_4703_;
}
}
}
}
}
}
}
v___jp_4703_:
{
size_t v___x_4705_; size_t v___x_4706_; 
v___x_4705_ = ((size_t)1ULL);
v___x_4706_ = lean_usize_add(v_i_4696_, v___x_4705_);
v_i_4696_ = v___x_4706_;
v_b_4697_ = v_a_4704_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg___boxed(lean_object* v_as_4758_, lean_object* v_sz_4759_, lean_object* v_i_4760_, lean_object* v_b_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
size_t v_sz_boxed_4767_; size_t v_i_boxed_4768_; lean_object* v_res_4769_; 
v_sz_boxed_4767_ = lean_unbox_usize(v_sz_4759_);
lean_dec(v_sz_4759_);
v_i_boxed_4768_ = lean_unbox_usize(v_i_4760_);
lean_dec(v_i_4760_);
v_res_4769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_as_4758_, v_sz_boxed_4767_, v_i_boxed_4768_, v_b_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec_ref(v_as_4758_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(lean_object* v_resourceTy_4773_, lean_object* v_entry_4774_, lean_object* v_res_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v_args_4788_; lean_object* v_varNames_4789_; lean_object* v_frameStx_4790_; lean_object* v___x_4791_; lean_object* v_decls_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; size_t v_sz_4796_; size_t v___x_4797_; lean_object* v___x_4798_; 
v_args_4788_ = lean_ctor_get(v_res_4775_, 1);
lean_inc_ref(v_args_4788_);
lean_dec_ref(v_res_4775_);
v_varNames_4789_ = lean_ctor_get(v_entry_4774_, 1);
lean_inc_ref(v_varNames_4789_);
v_frameStx_4790_ = lean_ctor_get(v_entry_4774_, 2);
lean_inc(v_frameStx_4790_);
lean_dec_ref(v_entry_4774_);
v___x_4791_ = lean_unsigned_to_nat(0u);
v_decls_4792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__0));
v___x_4793_ = lean_array_get_size(v_args_4788_);
v___x_4794_ = l_Array_toSubarray___redArg(v_args_4788_, v___x_4791_, v___x_4793_);
v___x_4795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4795_, 0, v_decls_4792_);
lean_ctor_set(v___x_4795_, 1, v___x_4794_);
v_sz_4796_ = lean_array_size(v_varNames_4789_);
v___x_4797_ = ((size_t)0ULL);
v___x_4798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_varNames_4789_, v_sz_4796_, v___x_4797_, v___x_4795_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
lean_dec_ref(v_varNames_4789_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; lean_object* v_fst_4800_; lean_object* v_keyedConfig_4801_; uint8_t v_trackZetaDelta_4802_; lean_object* v_zetaDeltaSet_4803_; lean_object* v_lctx_4804_; lean_object* v_localInstances_4805_; lean_object* v_defEqCtx_x3f_4806_; lean_object* v_synthPendingDepth_4807_; lean_object* v_customCanUnfoldPredicate_x3f_4808_; uint8_t v_univApprox_4809_; uint8_t v_inTypeClassResolution_4810_; uint8_t v_cacheInferType_4811_; lean_object* v___f_4812_; lean_object* v___f_4813_; uint8_t v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
lean_inc(v_a_4799_);
lean_dec_ref_known(v___x_4798_, 1);
v_fst_4800_ = lean_ctor_get(v_a_4799_, 0);
lean_inc(v_fst_4800_);
lean_dec(v_a_4799_);
v_keyedConfig_4801_ = lean_ctor_get(v_a_4783_, 0);
v_trackZetaDelta_4802_ = lean_ctor_get_uint8(v_a_4783_, sizeof(void*)*7);
v_zetaDeltaSet_4803_ = lean_ctor_get(v_a_4783_, 1);
v_lctx_4804_ = lean_ctor_get(v_a_4783_, 2);
v_localInstances_4805_ = lean_ctor_get(v_a_4783_, 3);
v_defEqCtx_x3f_4806_ = lean_ctor_get(v_a_4783_, 4);
v_synthPendingDepth_4807_ = lean_ctor_get(v_a_4783_, 5);
v_customCanUnfoldPredicate_x3f_4808_ = lean_ctor_get(v_a_4783_, 6);
v_univApprox_4809_ = lean_ctor_get_uint8(v_a_4783_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4810_ = lean_ctor_get_uint8(v_a_4783_, sizeof(void*)*7 + 2);
v_cacheInferType_4811_ = lean_ctor_get_uint8(v_a_4783_, sizeof(void*)*7 + 3);
v___f_4812_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__1));
v___f_4813_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___boxed), 16, 3);
lean_closure_set(v___f_4813_, 0, v_resourceTy_4773_);
lean_closure_set(v___f_4813_, 1, v_frameStx_4790_);
lean_closure_set(v___f_4813_, 2, v___f_4812_);
v___x_4814_ = 1;
lean_inc_ref(v_keyedConfig_4801_);
v___x_4815_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4814_, v_keyedConfig_4801_);
lean_inc(v_customCanUnfoldPredicate_x3f_4808_);
lean_inc(v_synthPendingDepth_4807_);
lean_inc(v_defEqCtx_x3f_4806_);
lean_inc_ref(v_localInstances_4805_);
lean_inc_ref(v_lctx_4804_);
lean_inc(v_zetaDeltaSet_4803_);
v___x_4816_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
lean_ctor_set(v___x_4816_, 1, v_zetaDeltaSet_4803_);
lean_ctor_set(v___x_4816_, 2, v_lctx_4804_);
lean_ctor_set(v___x_4816_, 3, v_localInstances_4805_);
lean_ctor_set(v___x_4816_, 4, v_defEqCtx_x3f_4806_);
lean_ctor_set(v___x_4816_, 5, v_synthPendingDepth_4807_);
lean_ctor_set(v___x_4816_, 6, v_customCanUnfoldPredicate_x3f_4808_);
lean_ctor_set_uint8(v___x_4816_, sizeof(void*)*7, v_trackZetaDelta_4802_);
lean_ctor_set_uint8(v___x_4816_, sizeof(void*)*7 + 1, v_univApprox_4809_);
lean_ctor_set_uint8(v___x_4816_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4810_);
lean_ctor_set_uint8(v___x_4816_, sizeof(void*)*7 + 3, v_cacheInferType_4811_);
v___x_4817_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_fst_4800_, v___f_4813_, v_decls_4792_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v___x_4816_, v_a_4784_, v_a_4785_, v_a_4786_);
lean_dec_ref_known(v___x_4816_, 7);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
else
{
return v___x_4817_;
}
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4833_; 
lean_dec(v_frameStx_4790_);
lean_dec_ref(v_resourceTy_4773_);
v_a_4826_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4828_ = v___x_4798_;
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4798_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___boxed(lean_object* v_resourceTy_4834_, lean_object* v_entry_4835_, lean_object* v_res_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(v_resourceTy_4834_, v_entry_4835_, v_res_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
lean_dec(v_a_4847_);
lean_dec_ref(v_a_4846_);
lean_dec(v_a_4845_);
lean_dec_ref(v_a_4844_);
lean_dec(v_a_4843_);
lean_dec_ref(v_a_4842_);
lean_dec(v_a_4841_);
lean_dec_ref(v_a_4840_);
lean_dec(v_a_4839_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0(lean_object* v_as_4850_, size_t v_sz_4851_, size_t v_i_4852_, lean_object* v_b_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v___x_4866_; 
v___x_4866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_as_4850_, v_sz_4851_, v_i_4852_, v_b_4853_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___boxed(lean_object* v_as_4867_, lean_object* v_sz_4868_, lean_object* v_i_4869_, lean_object* v_b_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
size_t v_sz_boxed_4883_; size_t v_i_boxed_4884_; lean_object* v_res_4885_; 
v_sz_boxed_4883_ = lean_unbox_usize(v_sz_4868_);
lean_dec(v_sz_4868_);
v_i_boxed_4884_ = lean_unbox_usize(v_i_4869_);
lean_dec(v_i_4869_);
v_res_4885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0(v_as_4867_, v_sz_boxed_4883_, v_i_boxed_4884_, v_b_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_);
lean_dec(v___y_4881_);
lean_dec_ref(v___y_4880_);
lean_dec(v___y_4879_);
lean_dec_ref(v___y_4878_);
lean_dec(v___y_4877_);
lean_dec_ref(v___y_4876_);
lean_dec(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec_ref(v_as_4867_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(lean_object* v___x_4886_, lean_object* v___x_4887_, lean_object* v_as_4888_, size_t v_sz_4889_, size_t v_i_4890_, lean_object* v_b_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v_a_4900_; uint8_t v___x_4904_; 
v___x_4904_ = lean_usize_dec_lt(v_i_4890_, v_sz_4889_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4905_; 
lean_dec_ref(v___x_4887_);
v___x_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4905_, 0, v_b_4891_);
return v___x_4905_;
}
else
{
lean_object* v_a_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; uint8_t v_retired_4909_; 
v_a_4906_ = lean_array_uget_borrowed(v_as_4888_, v_i_4890_);
v___x_4907_ = l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default;
v___x_4908_ = lean_array_get_borrowed(v___x_4907_, v___x_4886_, v_a_4906_);
v_retired_4909_ = lean_ctor_get_uint8(v___x_4908_, sizeof(void*)*4);
if (v_retired_4909_ == 0)
{
lean_object* v_pat_4910_; lean_object* v_srcIdx_4911_; lean_object* v___x_4912_; 
v_pat_4910_ = lean_ctor_get(v___x_4908_, 0);
v_srcIdx_4911_ = lean_ctor_get(v___x_4908_, 3);
lean_inc_ref(v___x_4887_);
lean_inc_ref(v_pat_4910_);
v___x_4912_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pat_4910_, v___x_4887_, v___x_4904_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref_known(v___x_4912_, 1);
if (lean_obj_tag(v_a_4913_) == 1)
{
if (lean_obj_tag(v_b_4891_) == 0)
{
lean_object* v_val_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4922_; 
v_val_4914_ = lean_ctor_get(v_a_4913_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v_a_4913_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4916_ = v_a_4913_;
v_isShared_4917_ = v_isSharedCheck_4922_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_val_4914_);
lean_dec(v_a_4913_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4922_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4918_; lean_object* v___x_4920_; 
lean_inc(v___x_4908_);
v___x_4918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4908_);
lean_ctor_set(v___x_4918_, 1, v_val_4914_);
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 0, v___x_4918_);
v___x_4920_ = v___x_4916_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
v_a_4900_ = v___x_4920_;
goto v___jp_4899_;
}
}
}
else
{
lean_object* v_val_4923_; lean_object* v_fst_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4942_; 
v_val_4923_ = lean_ctor_get(v_b_4891_, 0);
lean_inc(v_val_4923_);
v_fst_4924_ = lean_ctor_get(v_val_4923_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v_val_4923_);
if (v_isSharedCheck_4942_ == 0)
{
lean_object* v_unused_4943_; 
v_unused_4943_ = lean_ctor_get(v_val_4923_, 1);
lean_dec(v_unused_4943_);
v___x_4926_ = v_val_4923_;
v_isShared_4927_ = v_isSharedCheck_4942_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_fst_4924_);
lean_dec(v_val_4923_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4942_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v_val_4928_; lean_object* v_srcIdx_4929_; uint8_t v___x_4930_; 
v_val_4928_ = lean_ctor_get(v_a_4913_, 0);
lean_inc(v_val_4928_);
lean_dec_ref_known(v_a_4913_, 1);
v_srcIdx_4929_ = lean_ctor_get(v_fst_4924_, 3);
lean_inc(v_srcIdx_4929_);
lean_dec(v_fst_4924_);
v___x_4930_ = lean_nat_dec_lt(v_srcIdx_4911_, v_srcIdx_4929_);
lean_dec(v_srcIdx_4929_);
if (v___x_4930_ == 0)
{
lean_dec(v_val_4928_);
lean_del_object(v___x_4926_);
v_a_4900_ = v_b_4891_;
goto v___jp_4899_;
}
else
{
lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4940_; 
v_isSharedCheck_4940_ = !lean_is_exclusive(v_b_4891_);
if (v_isSharedCheck_4940_ == 0)
{
lean_object* v_unused_4941_; 
v_unused_4941_ = lean_ctor_get(v_b_4891_, 0);
lean_dec(v_unused_4941_);
v___x_4932_ = v_b_4891_;
v_isShared_4933_ = v_isSharedCheck_4940_;
goto v_resetjp_4931_;
}
else
{
lean_dec(v_b_4891_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4940_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
lean_inc(v___x_4908_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 1, v_val_4928_);
lean_ctor_set(v___x_4926_, 0, v___x_4908_);
v___x_4935_ = v___x_4926_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4908_);
lean_ctor_set(v_reuseFailAlloc_4939_, 1, v_val_4928_);
v___x_4935_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4937_; 
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4935_);
v___x_4937_ = v___x_4932_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4935_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
v_a_4900_ = v___x_4937_;
goto v___jp_4899_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_4913_);
v_a_4900_ = v_b_4891_;
goto v___jp_4899_;
}
}
else
{
lean_object* v_a_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4951_; 
lean_dec(v_b_4891_);
lean_dec_ref(v___x_4887_);
v_a_4944_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4946_ = v___x_4912_;
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4912_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___x_4949_; 
if (v_isShared_4947_ == 0)
{
v___x_4949_ = v___x_4946_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_a_4944_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
}
else
{
v_a_4900_ = v_b_4891_;
goto v___jp_4899_;
}
}
v___jp_4899_:
{
size_t v___x_4901_; size_t v___x_4902_; 
v___x_4901_ = ((size_t)1ULL);
v___x_4902_ = lean_usize_add(v_i_4890_, v___x_4901_);
v_i_4890_ = v___x_4902_;
v_b_4891_ = v_a_4900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object* v___x_4952_, lean_object* v___x_4953_, lean_object* v_as_4954_, lean_object* v_sz_4955_, lean_object* v_i_4956_, lean_object* v_b_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
size_t v_sz_boxed_4965_; size_t v_i_boxed_4966_; lean_object* v_res_4967_; 
v_sz_boxed_4965_ = lean_unbox_usize(v_sz_4955_);
lean_dec(v_sz_4955_);
v_i_boxed_4966_ = lean_unbox_usize(v_i_4956_);
lean_dec(v_i_4956_);
v_res_4967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v___x_4952_, v___x_4953_, v_as_4954_, v_sz_boxed_4965_, v_i_boxed_4966_, v_b_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
lean_dec_ref(v_as_4954_);
lean_dec_ref(v___x_4952_);
return v_res_4967_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1(void){
_start:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4969_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__0));
v___x_4970_ = l_Lean_stringToMessageData(v___x_4969_);
return v___x_4970_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3(void){
_start:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4972_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__2));
v___x_4973_ = l_Lean_stringToMessageData(v___x_4972_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(lean_object* v_fp_4974_, lean_object* v_info_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_){
_start:
{
lean_object* v___x_4988_; lean_object* v_frameDB_4989_; lean_object* v_tree_4990_; lean_object* v_entries_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_5128_; 
v___x_4988_ = lean_st_ref_get(v_a_4977_);
v_frameDB_4989_ = lean_ctor_get(v___x_4988_, 4);
lean_inc_ref(v_frameDB_4989_);
lean_dec(v___x_4988_);
v_tree_4990_ = lean_ctor_get(v_frameDB_4989_, 0);
v_entries_4991_ = lean_ctor_get(v_frameDB_4989_, 1);
v_isSharedCheck_5128_ = !lean_is_exclusive(v_frameDB_4989_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_4993_ = v_frameDB_4989_;
v_isShared_4994_ = v_isSharedCheck_5128_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_entries_4991_);
lean_inc(v_tree_4990_);
lean_dec(v_frameDB_4989_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_5128_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; uint8_t v___x_4997_; 
v___x_4995_ = lean_array_get_size(v_entries_4991_);
v___x_4996_ = lean_unsigned_to_nat(0u);
v___x_4997_ = lean_nat_dec_eq(v___x_4995_, v___x_4996_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; lean_object* v_mctx_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; size_t v_sz_5003_; size_t v___x_5004_; lean_object* v___x_5005_; 
v___x_4998_ = lean_st_ref_get(v_a_4984_);
v_mctx_4999_ = lean_ctor_get(v___x_4998_, 0);
lean_inc_ref(v_mctx_4999_);
lean_dec(v___x_4998_);
v___x_5000_ = lean_box(0);
v___x_5001_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_4975_);
v___x_5002_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_4999_, v_tree_4990_, v___x_5001_);
lean_dec_ref(v_tree_4990_);
lean_dec_ref(v_mctx_4999_);
v_sz_5003_ = lean_array_size(v___x_5002_);
v___x_5004_ = ((size_t)0ULL);
lean_inc_ref(v___x_5001_);
v___x_5005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v_entries_4991_, v___x_5001_, v___x_5002_, v_sz_5003_, v___x_5004_, v___x_5000_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
lean_dec_ref(v___x_5002_);
lean_dec_ref(v_entries_4991_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5117_; 
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5008_ = v___x_5005_;
v_isShared_5009_ = v_isSharedCheck_5117_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_5005_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5117_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
if (lean_obj_tag(v_a_5006_) == 1)
{
lean_object* v_val_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5113_; 
lean_del_object(v___x_5008_);
v_val_5010_ = lean_ctor_get(v_a_5006_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v_a_5006_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5012_ = v_a_5006_;
v_isShared_5013_ = v_isSharedCheck_5113_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_val_5010_);
lean_dec(v_a_5006_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5113_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v_fst_5014_; lean_object* v_snd_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5112_; 
v_fst_5014_ = lean_ctor_get(v_val_5010_, 0);
v_snd_5015_ = lean_ctor_get(v_val_5010_, 1);
v_isSharedCheck_5112_ = !lean_is_exclusive(v_val_5010_);
if (v_isSharedCheck_5112_ == 0)
{
v___x_5017_ = v_val_5010_;
v_isShared_5018_ = v_isSharedCheck_5112_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_snd_5015_);
lean_inc(v_fst_5014_);
lean_dec(v_val_5010_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5112_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5019_; lean_object* v_frameDB_5020_; lean_object* v_specBackwardRuleCache_5021_; lean_object* v_splitBackwardRuleCache_5022_; lean_object* v_latticeBackwardRuleCache_5023_; lean_object* v_frameBackwardRuleCache_5024_; lean_object* v_invariants_5025_; lean_object* v_vcs_5026_; lean_object* v_simpState_5027_; lean_object* v_fuel_5028_; lean_object* v_inlineHandledInvariants_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5111_; 
v___x_5019_ = lean_st_ref_take(v_a_4977_);
v_frameDB_5020_ = lean_ctor_get(v___x_5019_, 4);
v_specBackwardRuleCache_5021_ = lean_ctor_get(v___x_5019_, 0);
v_splitBackwardRuleCache_5022_ = lean_ctor_get(v___x_5019_, 1);
v_latticeBackwardRuleCache_5023_ = lean_ctor_get(v___x_5019_, 2);
v_frameBackwardRuleCache_5024_ = lean_ctor_get(v___x_5019_, 3);
v_invariants_5025_ = lean_ctor_get(v___x_5019_, 5);
v_vcs_5026_ = lean_ctor_get(v___x_5019_, 6);
v_simpState_5027_ = lean_ctor_get(v___x_5019_, 7);
v_fuel_5028_ = lean_ctor_get(v___x_5019_, 8);
v_inlineHandledInvariants_5029_ = lean_ctor_get(v___x_5019_, 9);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5031_ = v___x_5019_;
v_isShared_5032_ = v_isSharedCheck_5111_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_inlineHandledInvariants_5029_);
lean_inc(v_fuel_5028_);
lean_inc(v_simpState_5027_);
lean_inc(v_vcs_5026_);
lean_inc(v_invariants_5025_);
lean_inc(v_frameDB_5020_);
lean_inc(v_frameBackwardRuleCache_5024_);
lean_inc(v_latticeBackwardRuleCache_5023_);
lean_inc(v_splitBackwardRuleCache_5022_);
lean_inc(v_specBackwardRuleCache_5021_);
lean_dec(v___x_5019_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5111_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v_tree_5033_; lean_object* v_entries_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5110_; 
v_tree_5033_ = lean_ctor_get(v_frameDB_5020_, 0);
v_entries_5034_ = lean_ctor_get(v_frameDB_5020_, 1);
v_isSharedCheck_5110_ = !lean_is_exclusive(v_frameDB_5020_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5036_ = v_frameDB_5020_;
v_isShared_5037_ = v_isSharedCheck_5110_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_entries_5034_);
lean_inc(v_tree_5033_);
lean_dec(v_frameDB_5020_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5110_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v_pat_5038_; lean_object* v_varNames_5039_; lean_object* v_frameStx_5040_; lean_object* v_srcIdx_5041_; uint8_t v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5046_; 
v_pat_5038_ = lean_ctor_get(v_fst_5014_, 0);
v_varNames_5039_ = lean_ctor_get(v_fst_5014_, 1);
v_frameStx_5040_ = lean_ctor_get(v_fst_5014_, 2);
v_srcIdx_5041_ = lean_ctor_get(v_fst_5014_, 3);
v___x_5042_ = 1;
lean_inc(v_srcIdx_5041_);
lean_inc(v_frameStx_5040_);
lean_inc_ref(v_varNames_5039_);
lean_inc_ref(v_pat_5038_);
v___x_5043_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_5043_, 0, v_pat_5038_);
lean_ctor_set(v___x_5043_, 1, v_varNames_5039_);
lean_ctor_set(v___x_5043_, 2, v_frameStx_5040_);
lean_ctor_set(v___x_5043_, 3, v_srcIdx_5041_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*4, v___x_5042_);
v___x_5044_ = lean_array_set(v_entries_5034_, v_srcIdx_5041_, v___x_5043_);
if (v_isShared_5037_ == 0)
{
lean_ctor_set(v___x_5036_, 1, v___x_5044_);
v___x_5046_ = v___x_5036_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_tree_5033_);
lean_ctor_set(v_reuseFailAlloc_5109_, 1, v___x_5044_);
v___x_5046_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
lean_object* v___x_5048_; 
if (v_isShared_5032_ == 0)
{
lean_ctor_set(v___x_5031_, 4, v___x_5046_);
v___x_5048_ = v___x_5031_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v_specBackwardRuleCache_5021_);
lean_ctor_set(v_reuseFailAlloc_5108_, 1, v_splitBackwardRuleCache_5022_);
lean_ctor_set(v_reuseFailAlloc_5108_, 2, v_latticeBackwardRuleCache_5023_);
lean_ctor_set(v_reuseFailAlloc_5108_, 3, v_frameBackwardRuleCache_5024_);
lean_ctor_set(v_reuseFailAlloc_5108_, 4, v___x_5046_);
lean_ctor_set(v_reuseFailAlloc_5108_, 5, v_invariants_5025_);
lean_ctor_set(v_reuseFailAlloc_5108_, 6, v_vcs_5026_);
lean_ctor_set(v_reuseFailAlloc_5108_, 7, v_simpState_5027_);
lean_ctor_set(v_reuseFailAlloc_5108_, 8, v_fuel_5028_);
lean_ctor_set(v_reuseFailAlloc_5108_, 9, v_inlineHandledInvariants_5029_);
v___x_5048_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
lean_object* v___x_5049_; lean_object* v_mkResourceTy_5050_; lean_object* v___x_5051_; 
v___x_5049_ = lean_st_ref_put(v_a_4977_, v___x_5048_);
v_mkResourceTy_5050_ = lean_ctor_get(v_fp_4974_, 3);
lean_inc_ref(v_mkResourceTy_5050_);
lean_dec_ref(v_fp_4974_);
lean_inc(v_a_4986_);
lean_inc_ref(v_a_4985_);
lean_inc(v_a_4984_);
lean_inc_ref(v_a_4983_);
v___x_5051_ = lean_apply_6(v_mkResourceTy_5050_, v_info_4975_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, lean_box(0));
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v_a_5052_; lean_object* v___x_5053_; 
v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
lean_inc(v_a_5052_);
lean_dec_ref_known(v___x_5051_, 1);
v___x_5053_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(v_a_5052_, v_fst_5014_, v_snd_5015_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5091_; 
v_a_5054_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5056_ = v___x_5053_;
v_isShared_5057_ = v_isSharedCheck_5091_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_5053_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5091_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v_options_5065_; uint8_t v_hasTrace_5066_; 
v_options_5065_ = lean_ctor_get(v_a_4985_, 2);
v_hasTrace_5066_ = lean_ctor_get_uint8(v_options_5065_, sizeof(void*)*1);
if (v_hasTrace_5066_ == 0)
{
lean_del_object(v___x_5017_);
lean_dec_ref(v___x_5001_);
lean_del_object(v___x_4993_);
goto v___jp_5058_;
}
else
{
lean_object* v_inheritedTraceOptions_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; uint8_t v___x_5070_; 
v_inheritedTraceOptions_5067_ = lean_ctor_get(v_a_4985_, 13);
v___x_5068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5069_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5070_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5067_, v_options_5065_, v___x_5069_);
if (v___x_5070_ == 0)
{
lean_del_object(v___x_5017_);
lean_dec_ref(v___x_5001_);
lean_del_object(v___x_4993_);
goto v___jp_5058_;
}
else
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5074_; 
v___x_5071_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1, &l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1);
v___x_5072_ = l_Lean_MessageData_ofExpr(v___x_5001_);
if (v_isShared_5018_ == 0)
{
lean_ctor_set_tag(v___x_5017_, 7);
lean_ctor_set(v___x_5017_, 1, v___x_5072_);
lean_ctor_set(v___x_5017_, 0, v___x_5071_);
v___x_5074_ = v___x_5017_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v___x_5071_);
lean_ctor_set(v_reuseFailAlloc_5090_, 1, v___x_5072_);
v___x_5074_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5075_; lean_object* v___x_5077_; 
v___x_5075_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3);
if (v_isShared_4994_ == 0)
{
lean_ctor_set_tag(v___x_4993_, 7);
lean_ctor_set(v___x_4993_, 1, v___x_5075_);
lean_ctor_set(v___x_4993_, 0, v___x_5074_);
v___x_5077_ = v___x_4993_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5074_);
lean_ctor_set(v_reuseFailAlloc_5089_, 1, v___x_5075_);
v___x_5077_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; 
lean_inc(v_a_5054_);
v___x_5078_ = l_Lean_indentExpr(v_a_5054_);
v___x_5079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5079_, 0, v___x_5077_);
lean_ctor_set(v___x_5079_, 1, v___x_5078_);
v___x_5080_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5068_, v___x_5079_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
if (lean_obj_tag(v___x_5080_) == 0)
{
lean_dec_ref_known(v___x_5080_, 1);
goto v___jp_5058_;
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
lean_del_object(v___x_5056_);
lean_dec(v_a_5054_);
lean_del_object(v___x_5012_);
v_a_5081_ = lean_ctor_get(v___x_5080_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5080_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5083_ = v___x_5080_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5080_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5081_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
}
}
}
v___jp_5058_:
{
lean_object* v___x_5060_; 
if (v_isShared_5013_ == 0)
{
lean_ctor_set(v___x_5012_, 0, v_a_5054_);
v___x_5060_ = v___x_5012_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5054_);
v___x_5060_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
lean_object* v___x_5062_; 
if (v_isShared_5057_ == 0)
{
lean_ctor_set(v___x_5056_, 0, v___x_5060_);
v___x_5062_ = v___x_5056_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
}
}
}
else
{
lean_object* v_a_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5099_; 
lean_del_object(v___x_5017_);
lean_del_object(v___x_5012_);
lean_dec_ref(v___x_5001_);
lean_del_object(v___x_4993_);
v_a_5092_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5094_ = v___x_5053_;
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v___x_5053_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5097_; 
if (v_isShared_5095_ == 0)
{
v___x_5097_ = v___x_5094_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5092_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
return v___x_5097_;
}
}
}
}
else
{
lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5107_; 
lean_del_object(v___x_5017_);
lean_dec(v_snd_5015_);
lean_dec(v_fst_5014_);
lean_del_object(v___x_5012_);
lean_dec_ref(v___x_5001_);
lean_del_object(v___x_4993_);
v_a_5100_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5102_ = v___x_5051_;
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_5051_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5105_; 
if (v_isShared_5103_ == 0)
{
v___x_5105_ = v___x_5102_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
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
else
{
lean_object* v___x_5115_; 
lean_dec(v_a_5006_);
lean_dec_ref(v___x_5001_);
lean_del_object(v___x_4993_);
lean_dec_ref(v_info_4975_);
lean_dec_ref(v_fp_4974_);
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 0, v___x_5000_);
v___x_5115_ = v___x_5008_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5000_);
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
lean_dec_ref(v___x_5001_);
lean_del_object(v___x_4993_);
lean_dec_ref(v_info_4975_);
lean_dec_ref(v_fp_4974_);
v_a_5118_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5120_ = v___x_5005_;
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5005_);
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
}
else
{
lean_object* v___x_5126_; lean_object* v___x_5127_; 
lean_del_object(v___x_4993_);
lean_dec_ref(v_entries_4991_);
lean_dec_ref(v_tree_4990_);
lean_dec_ref(v_info_4975_);
lean_dec_ref(v_fp_4974_);
v___x_5126_ = lean_box(0);
v___x_5127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5127_, 0, v___x_5126_);
return v___x_5127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___boxed(lean_object* v_fp_5129_, lean_object* v_info_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(v_fp_5129_, v_info_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_);
lean_dec(v_a_5141_);
lean_dec_ref(v_a_5140_);
lean_dec(v_a_5139_);
lean_dec_ref(v_a_5138_);
lean_dec(v_a_5137_);
lean_dec_ref(v_a_5136_);
lean_dec(v_a_5135_);
lean_dec_ref(v_a_5134_);
lean_dec(v_a_5133_);
lean_dec(v_a_5132_);
lean_dec_ref(v_a_5131_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0(lean_object* v___x_5144_, lean_object* v___x_5145_, lean_object* v_as_5146_, size_t v_sz_5147_, size_t v_i_5148_, lean_object* v_b_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
lean_object* v___x_5162_; 
v___x_5162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v___x_5144_, v___x_5145_, v_as_5146_, v_sz_5147_, v_i_5148_, v_b_5149_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
return v___x_5162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___boxed(lean_object** _args){
lean_object* v___x_5163_ = _args[0];
lean_object* v___x_5164_ = _args[1];
lean_object* v_as_5165_ = _args[2];
lean_object* v_sz_5166_ = _args[3];
lean_object* v_i_5167_ = _args[4];
lean_object* v_b_5168_ = _args[5];
lean_object* v___y_5169_ = _args[6];
lean_object* v___y_5170_ = _args[7];
lean_object* v___y_5171_ = _args[8];
lean_object* v___y_5172_ = _args[9];
lean_object* v___y_5173_ = _args[10];
lean_object* v___y_5174_ = _args[11];
lean_object* v___y_5175_ = _args[12];
lean_object* v___y_5176_ = _args[13];
lean_object* v___y_5177_ = _args[14];
lean_object* v___y_5178_ = _args[15];
lean_object* v___y_5179_ = _args[16];
lean_object* v___y_5180_ = _args[17];
_start:
{
size_t v_sz_boxed_5181_; size_t v_i_boxed_5182_; lean_object* v_res_5183_; 
v_sz_boxed_5181_ = lean_unbox_usize(v_sz_5166_);
lean_dec(v_sz_5166_);
v_i_boxed_5182_ = lean_unbox_usize(v_i_5167_);
lean_dec(v_i_5167_);
v_res_5183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0(v___x_5163_, v___x_5164_, v_as_5165_, v_sz_boxed_5181_, v_i_boxed_5182_, v_b_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
lean_dec(v___y_5177_);
lean_dec_ref(v___y_5176_);
lean_dec(v___y_5175_);
lean_dec_ref(v___y_5174_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
lean_dec(v___y_5171_);
lean_dec(v___y_5170_);
lean_dec_ref(v___y_5169_);
lean_dec_ref(v_as_5165_);
lean_dec_ref(v___x_5163_);
return v_res_5183_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost(lean_object* v_post_5191_){
_start:
{
lean_object* v___y_5193_; uint8_t v___x_5198_; 
v___x_5198_ = l_Lean_Expr_isLambda(v_post_5191_);
if (v___x_5198_ == 0)
{
v___y_5193_ = v_post_5191_;
goto v___jp_5192_;
}
else
{
lean_object* v___x_5199_; 
v___x_5199_ = l_Lean_Expr_bindingBody_x21(v_post_5191_);
lean_dec_ref(v_post_5191_);
v___y_5193_ = v___x_5199_;
goto v___jp_5192_;
}
v___jp_5192_:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; uint8_t v___x_5197_; 
v___x_5194_ = l_Lean_Expr_consumeMData(v___y_5193_);
lean_dec_ref(v___y_5193_);
v___x_5195_ = l_Lean_Expr_getAppFn(v___x_5194_);
lean_dec_ref(v___x_5194_);
v___x_5196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2));
v___x_5197_ = l_Lean_Expr_isConstOf(v___x_5195_, v___x_5196_);
lean_dec_ref(v___x_5195_);
return v___x_5197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___boxed(lean_object* v_post_5200_){
_start:
{
uint8_t v_res_5201_; lean_object* v_r_5202_; 
v_res_5201_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost(v_post_5200_);
v_r_5202_ = lean_box(v_res_5201_);
return v_r_5202_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1(void){
_start:
{
lean_object* v___x_5204_; lean_object* v___x_5205_; 
v___x_5204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__0));
v___x_5205_ = l_Lean_stringToMessageData(v___x_5204_);
return v___x_5205_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3(void){
_start:
{
lean_object* v___x_5207_; lean_object* v___x_5208_; 
v___x_5207_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__2));
v___x_5208_ = l_Lean_stringToMessageData(v___x_5207_);
return v___x_5208_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5(void){
_start:
{
lean_object* v___x_5210_; lean_object* v___x_5211_; 
v___x_5210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__4));
v___x_5211_ = l_Lean_stringToMessageData(v___x_5210_);
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule(lean_object* v_goal_5212_, lean_object* v_info_5213_, lean_object* v_fp_5214_, lean_object* v_split_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_){
_start:
{
lean_object* v___x_5228_; 
lean_inc_ref(v_info_5213_);
v___x_5228_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_5214_, v_info_5213_, v_a_5217_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v_a_5229_; lean_object* v_rule_5230_; lean_object* v_splitVCIdx_5231_; lean_object* v_frameIdx_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
lean_inc(v_a_5229_);
lean_dec_ref_known(v___x_5228_, 1);
v_rule_5230_ = lean_ctor_get(v_a_5229_, 0);
lean_inc_ref(v_rule_5230_);
v_splitVCIdx_5231_ = lean_ctor_get(v_a_5229_, 1);
lean_inc(v_splitVCIdx_5231_);
v_frameIdx_5232_ = lean_ctor_get(v_a_5229_, 2);
lean_inc(v_frameIdx_5232_);
lean_dec(v_a_5229_);
v___x_5233_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1);
v___x_5234_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5213_);
v___x_5235_ = l_Lean_indentExpr(v___x_5234_);
lean_inc_ref(v___x_5235_);
v___x_5236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5236_, 0, v___x_5233_);
lean_ctor_set(v___x_5236_, 1, v___x_5235_);
v___x_5237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5236_);
v___x_5238_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_5230_, v_goal_5212_, v___x_5237_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
if (lean_obj_tag(v___x_5238_) == 0)
{
lean_object* v_a_5239_; 
v_a_5239_ = lean_ctor_get(v___x_5238_, 0);
lean_inc(v_a_5239_);
lean_dec_ref_known(v___x_5238_, 1);
if (lean_obj_tag(v_a_5239_) == 1)
{
lean_object* v_mvarIds_5240_; lean_object* v_frame_5241_; lean_object* v_residualPre_5242_; lean_object* v_splitVCProof_5243_; lean_object* v_subgoals_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; 
lean_dec_ref(v___x_5235_);
v_mvarIds_5240_ = lean_ctor_get(v_a_5239_, 0);
lean_inc(v_mvarIds_5240_);
lean_dec_ref_known(v_a_5239_, 1);
v_frame_5241_ = lean_ctor_get(v_split_5215_, 0);
lean_inc_ref(v_frame_5241_);
v_residualPre_5242_ = lean_ctor_get(v_split_5215_, 1);
lean_inc(v_residualPre_5242_);
v_splitVCProof_5243_ = lean_ctor_get(v_split_5215_, 2);
lean_inc_ref(v_splitVCProof_5243_);
v_subgoals_5244_ = lean_ctor_get(v_split_5215_, 3);
lean_inc(v_subgoals_5244_);
lean_dec_ref(v_split_5215_);
v___x_5245_ = lean_box(0);
v___x_5246_ = lean_array_mk(v_mvarIds_5240_);
v___x_5247_ = lean_array_get(v___x_5245_, v___x_5246_, v_frameIdx_5232_);
lean_dec(v_frameIdx_5232_);
v___x_5248_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v___x_5247_, v_frame_5241_, v_a_5224_);
lean_dec_ref(v___x_5248_);
v___x_5249_ = lean_array_get(v___x_5245_, v___x_5246_, v_splitVCIdx_5231_);
lean_dec(v_splitVCIdx_5231_);
lean_inc(v___x_5249_);
v___x_5250_ = l_Lean_MVarId_getType(v___x_5249_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
if (lean_obj_tag(v___x_5250_) == 0)
{
lean_object* v_a_5251_; lean_object* v___y_5253_; lean_object* v___y_5254_; lean_object* v___y_5255_; lean_object* v___y_5256_; lean_object* v___x_5261_; uint8_t v___x_5262_; 
v_a_5251_ = lean_ctor_get(v___x_5250_, 0);
lean_inc_n(v_a_5251_, 2);
lean_dec_ref_known(v___x_5250_, 1);
v___x_5261_ = l_Lean_Expr_cleanupAnnotations(v_a_5251_);
v___x_5262_ = l_Lean_Expr_isApp(v___x_5261_);
if (v___x_5262_ == 0)
{
lean_dec_ref(v___x_5261_);
lean_dec(v___x_5249_);
lean_dec_ref(v___x_5246_);
lean_dec(v_subgoals_5244_);
lean_dec_ref(v_splitVCProof_5243_);
lean_dec(v_residualPre_5242_);
lean_dec_ref(v_info_5213_);
v___y_5253_ = v_a_5223_;
v___y_5254_ = v_a_5224_;
v___y_5255_ = v_a_5225_;
v___y_5256_ = v_a_5226_;
goto v___jp_5252_;
}
else
{
lean_object* v_arg_5263_; lean_object* v___x_5264_; uint8_t v___x_5265_; 
v_arg_5263_ = lean_ctor_get(v___x_5261_, 1);
lean_inc_ref(v_arg_5263_);
v___x_5264_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5261_);
v___x_5265_ = l_Lean_Expr_isApp(v___x_5264_);
if (v___x_5265_ == 0)
{
lean_dec_ref(v___x_5264_);
lean_dec_ref(v_arg_5263_);
lean_dec(v___x_5249_);
lean_dec_ref(v___x_5246_);
lean_dec(v_subgoals_5244_);
lean_dec_ref(v_splitVCProof_5243_);
lean_dec(v_residualPre_5242_);
lean_dec_ref(v_info_5213_);
v___y_5253_ = v_a_5223_;
v___y_5254_ = v_a_5224_;
v___y_5255_ = v_a_5225_;
v___y_5256_ = v_a_5226_;
goto v___jp_5252_;
}
else
{
lean_object* v___x_5266_; uint8_t v___x_5267_; 
v___x_5266_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5264_);
v___x_5267_ = l_Lean_Expr_isApp(v___x_5266_);
if (v___x_5267_ == 0)
{
lean_dec_ref(v___x_5266_);
lean_dec_ref(v_arg_5263_);
lean_dec(v___x_5249_);
lean_dec_ref(v___x_5246_);
lean_dec(v_subgoals_5244_);
lean_dec_ref(v_splitVCProof_5243_);
lean_dec(v_residualPre_5242_);
lean_dec_ref(v_info_5213_);
v___y_5253_ = v_a_5223_;
v___y_5254_ = v_a_5224_;
v___y_5255_ = v_a_5225_;
v___y_5256_ = v_a_5226_;
goto v___jp_5252_;
}
else
{
lean_object* v___x_5268_; uint8_t v___x_5269_; 
v___x_5268_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5266_);
v___x_5269_ = l_Lean_Expr_isApp(v___x_5268_);
if (v___x_5269_ == 0)
{
lean_dec_ref(v___x_5268_);
lean_dec_ref(v_arg_5263_);
lean_dec(v___x_5249_);
lean_dec_ref(v___x_5246_);
lean_dec(v_subgoals_5244_);
lean_dec_ref(v_splitVCProof_5243_);
lean_dec(v_residualPre_5242_);
lean_dec_ref(v_info_5213_);
v___y_5253_ = v_a_5223_;
v___y_5254_ = v_a_5224_;
v___y_5255_ = v_a_5225_;
v___y_5256_ = v_a_5226_;
goto v___jp_5252_;
}
else
{
lean_object* v___x_5270_; lean_object* v___x_5271_; uint8_t v___x_5272_; 
v___x_5270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5268_);
v___x_5271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10));
v___x_5272_ = l_Lean_Expr_isConstOf(v___x_5270_, v___x_5271_);
lean_dec_ref(v___x_5270_);
if (v___x_5272_ == 0)
{
lean_dec_ref(v_arg_5263_);
lean_dec(v___x_5249_);
lean_dec_ref(v___x_5246_);
lean_dec(v_subgoals_5244_);
lean_dec_ref(v_splitVCProof_5243_);
lean_dec(v_residualPre_5242_);
lean_dec_ref(v_info_5213_);
v___y_5253_ = v_a_5223_;
v___y_5254_ = v_a_5224_;
v___y_5255_ = v_a_5225_;
v___y_5256_ = v_a_5226_;
goto v___jp_5252_;
}
else
{
lean_object* v_excessArgs_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5287_; 
lean_dec(v_a_5251_);
v_excessArgs_5273_ = lean_ctor_get(v_info_5213_, 2);
lean_inc_ref(v_excessArgs_5273_);
lean_dec_ref(v_info_5213_);
v___x_5274_ = lean_array_get_size(v_excessArgs_5273_);
lean_dec_ref(v_excessArgs_5273_);
v___x_5275_ = l_Lean_Expr_stripArgsN(v_arg_5263_, v___x_5274_);
lean_dec_ref(v_arg_5263_);
v___x_5276_ = l_Lean_Expr_appArg_x21(v___x_5275_);
lean_dec_ref(v___x_5275_);
v___x_5277_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_residualPre_5242_, v___x_5276_, v_a_5224_);
lean_dec_ref(v___x_5277_);
v___x_5278_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v___x_5249_, v_splitVCProof_5243_, v_a_5224_);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5287_ == 0)
{
lean_object* v_unused_5288_; 
v_unused_5288_ = lean_ctor_get(v___x_5278_, 0);
lean_dec(v_unused_5288_);
v___x_5280_ = v___x_5278_;
v_isShared_5281_ = v_isSharedCheck_5287_;
goto v_resetjp_5279_;
}
else
{
lean_dec(v___x_5278_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5287_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5285_; 
v___x_5282_ = lean_array_to_list(v___x_5246_);
v___x_5283_ = l_List_appendTR___redArg(v___x_5282_, v_subgoals_5244_);
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 0, v___x_5283_);
v___x_5285_ = v___x_5280_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5283_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
}
}
}
}
v___jp_5252_:
{
lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___x_5257_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3);
v___x_5258_ = l_Lean_indentExpr(v_a_5251_);
v___x_5259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5259_, 0, v___x_5257_);
lean_ctor_set(v___x_5259_, 1, v___x_5258_);
v___x_5260_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5259_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
return v___x_5260_;
}
}
else
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5296_; 
lean_dec(v___x_5249_);
lean_dec_ref(v___x_5246_);
lean_dec(v_subgoals_5244_);
lean_dec_ref(v_splitVCProof_5243_);
lean_dec(v_residualPre_5242_);
lean_dec_ref(v_info_5213_);
v_a_5289_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5291_ = v___x_5250_;
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5250_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v___x_5294_; 
if (v_isShared_5292_ == 0)
{
v___x_5294_ = v___x_5291_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
return v___x_5294_;
}
}
}
}
else
{
lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
lean_dec(v_a_5239_);
lean_dec(v_frameIdx_5232_);
lean_dec(v_splitVCIdx_5231_);
lean_dec_ref(v_split_5215_);
lean_dec_ref(v_info_5213_);
v___x_5297_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5);
v___x_5298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5297_);
lean_ctor_set(v___x_5298_, 1, v___x_5235_);
v___x_5299_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5298_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
return v___x_5299_;
}
}
else
{
lean_object* v_a_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5307_; 
lean_dec_ref(v___x_5235_);
lean_dec(v_frameIdx_5232_);
lean_dec(v_splitVCIdx_5231_);
lean_dec_ref(v_split_5215_);
lean_dec_ref(v_info_5213_);
v_a_5300_ = lean_ctor_get(v___x_5238_, 0);
v_isSharedCheck_5307_ = !lean_is_exclusive(v___x_5238_);
if (v_isSharedCheck_5307_ == 0)
{
v___x_5302_ = v___x_5238_;
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_a_5300_);
lean_dec(v___x_5238_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v___x_5305_; 
if (v_isShared_5303_ == 0)
{
v___x_5305_ = v___x_5302_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5300_);
v___x_5305_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
return v___x_5305_;
}
}
}
}
else
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5315_; 
lean_dec_ref(v_split_5215_);
lean_dec_ref(v_info_5213_);
lean_dec(v_goal_5212_);
v_a_5308_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5315_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5315_ == 0)
{
v___x_5310_ = v___x_5228_;
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5228_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5313_; 
if (v_isShared_5311_ == 0)
{
v___x_5313_ = v___x_5310_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5308_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
return v___x_5313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___boxed(lean_object* v_goal_5316_, lean_object* v_info_5317_, lean_object* v_fp_5318_, lean_object* v_split_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_){
_start:
{
lean_object* v_res_5332_; 
v_res_5332_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule(v_goal_5316_, v_info_5317_, v_fp_5318_, v_split_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec_ref(v_a_5323_);
lean_dec(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0(lean_object* v_mkOpAppM_5333_, lean_object* v_info_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_){
_start:
{
lean_object* v___x_5342_; 
lean_inc(v___y_5340_);
lean_inc_ref(v___y_5339_);
lean_inc(v___y_5338_);
lean_inc_ref(v___y_5337_);
v___x_5342_ = lean_apply_6(v_mkOpAppM_5333_, v_info_5334_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, lean_box(0));
if (lean_obj_tag(v___x_5342_) == 0)
{
lean_object* v_a_5343_; lean_object* v___x_5344_; 
v_a_5343_ = lean_ctor_get(v___x_5342_, 0);
lean_inc(v_a_5343_);
lean_dec_ref_known(v___x_5342_, 1);
v___x_5344_ = l_Lean_Meta_Sym_shareCommon(v_a_5343_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
return v___x_5344_;
}
else
{
return v___x_5342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0___boxed(lean_object* v_mkOpAppM_5345_, lean_object* v_info_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_){
_start:
{
lean_object* v_res_5354_; 
v_res_5354_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0(v_mkOpAppM_5345_, v_info_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_);
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
return v_res_5354_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(lean_object* v_a_5355_, lean_object* v_a_5356_){
_start:
{
if (lean_obj_tag(v_a_5355_) == 0)
{
lean_object* v___x_5357_; 
v___x_5357_ = l_List_reverse___redArg(v_a_5356_);
return v___x_5357_;
}
else
{
lean_object* v_head_5358_; lean_object* v_tail_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5368_; 
v_head_5358_ = lean_ctor_get(v_a_5355_, 0);
v_tail_5359_ = lean_ctor_get(v_a_5355_, 1);
v_isSharedCheck_5368_ = !lean_is_exclusive(v_a_5355_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5361_ = v_a_5355_;
v_isShared_5362_ = v_isSharedCheck_5368_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_tail_5359_);
lean_inc(v_head_5358_);
lean_dec(v_a_5355_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5368_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v___x_5363_; lean_object* v___x_5365_; 
v___x_5363_ = l_Lean_MessageData_ofExpr(v_head_5358_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 1, v_a_5356_);
lean_ctor_set(v___x_5361_, 0, v___x_5363_);
v___x_5365_ = v___x_5361_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v___x_5363_);
lean_ctor_set(v_reuseFailAlloc_5367_, 1, v_a_5356_);
v___x_5365_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
v_a_5355_ = v_tail_5359_;
v_a_5356_ = v___x_5365_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(lean_object* v_a_5369_, lean_object* v_x_5370_){
_start:
{
if (lean_obj_tag(v_x_5370_) == 0)
{
lean_object* v___x_5371_; 
v___x_5371_ = lean_box(0);
return v___x_5371_;
}
else
{
lean_object* v_key_5372_; lean_object* v_value_5373_; lean_object* v_tail_5374_; uint8_t v___x_5375_; 
v_key_5372_ = lean_ctor_get(v_x_5370_, 0);
v_value_5373_ = lean_ctor_get(v_x_5370_, 1);
v_tail_5374_ = lean_ctor_get(v_x_5370_, 2);
v___x_5375_ = lean_name_eq(v_key_5372_, v_a_5369_);
if (v___x_5375_ == 0)
{
v_x_5370_ = v_tail_5374_;
goto _start;
}
else
{
lean_object* v___x_5377_; 
lean_inc(v_value_5373_);
v___x_5377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5377_, 0, v_value_5373_);
return v___x_5377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg___boxed(lean_object* v_a_5378_, lean_object* v_x_5379_){
_start:
{
lean_object* v_res_5380_; 
v_res_5380_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(v_a_5378_, v_x_5379_);
lean_dec(v_x_5379_);
lean_dec(v_a_5378_);
return v_res_5380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(lean_object* v_m_5381_, lean_object* v_a_5382_){
_start:
{
lean_object* v_buckets_5383_; lean_object* v___x_5384_; uint64_t v___y_5386_; 
v_buckets_5383_ = lean_ctor_get(v_m_5381_, 1);
v___x_5384_ = lean_array_get_size(v_buckets_5383_);
if (lean_obj_tag(v_a_5382_) == 0)
{
uint64_t v___x_5400_; 
v___x_5400_ = 1723ULL;
v___y_5386_ = v___x_5400_;
goto v___jp_5385_;
}
else
{
uint64_t v_hash_5401_; 
v_hash_5401_ = lean_ctor_get_uint64(v_a_5382_, sizeof(void*)*2);
v___y_5386_ = v_hash_5401_;
goto v___jp_5385_;
}
v___jp_5385_:
{
uint64_t v___x_5387_; uint64_t v___x_5388_; uint64_t v_fold_5389_; uint64_t v___x_5390_; uint64_t v___x_5391_; uint64_t v___x_5392_; size_t v___x_5393_; size_t v___x_5394_; size_t v___x_5395_; size_t v___x_5396_; size_t v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; 
v___x_5387_ = 32ULL;
v___x_5388_ = lean_uint64_shift_right(v___y_5386_, v___x_5387_);
v_fold_5389_ = lean_uint64_xor(v___y_5386_, v___x_5388_);
v___x_5390_ = 16ULL;
v___x_5391_ = lean_uint64_shift_right(v_fold_5389_, v___x_5390_);
v___x_5392_ = lean_uint64_xor(v_fold_5389_, v___x_5391_);
v___x_5393_ = lean_uint64_to_usize(v___x_5392_);
v___x_5394_ = lean_usize_of_nat(v___x_5384_);
v___x_5395_ = ((size_t)1ULL);
v___x_5396_ = lean_usize_sub(v___x_5394_, v___x_5395_);
v___x_5397_ = lean_usize_land(v___x_5393_, v___x_5396_);
v___x_5398_ = lean_array_uget_borrowed(v_buckets_5383_, v___x_5397_);
v___x_5399_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(v_a_5382_, v___x_5398_);
return v___x_5399_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg___boxed(lean_object* v_m_5402_, lean_object* v_a_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(v_m_5402_, v_a_5403_);
lean_dec(v_a_5403_);
lean_dec_ref(v_m_5402_);
return v_res_5404_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1(void){
_start:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; 
v___x_5406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__0));
v___x_5407_ = l_Lean_stringToMessageData(v___x_5406_);
return v___x_5407_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3(void){
_start:
{
lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__2));
v___x_5410_ = l_Lean_stringToMessageData(v___x_5409_);
return v___x_5410_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5(void){
_start:
{
lean_object* v___x_5412_; lean_object* v___x_5413_; 
v___x_5412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__4));
v___x_5413_ = l_Lean_stringToMessageData(v___x_5412_);
return v___x_5413_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7(void){
_start:
{
lean_object* v___x_5415_; lean_object* v___x_5416_; 
v___x_5415_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__6));
v___x_5416_ = l_Lean_stringToMessageData(v___x_5415_);
return v___x_5416_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9(void){
_start:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__8));
v___x_5419_ = l_Lean_stringToMessageData(v___x_5418_);
return v___x_5419_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11(void){
_start:
{
lean_object* v___x_5421_; lean_object* v___x_5422_; 
v___x_5421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__10));
v___x_5422_ = l_Lean_stringToMessageData(v___x_5421_);
return v___x_5422_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13(void){
_start:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; 
v___x_5424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__12));
v___x_5425_ = l_Lean_stringToMessageData(v___x_5424_);
return v___x_5425_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15(void){
_start:
{
lean_object* v___x_5427_; lean_object* v___x_5428_; 
v___x_5427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__14));
v___x_5428_ = l_Lean_stringToMessageData(v___x_5427_);
return v___x_5428_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17(void){
_start:
{
lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__16));
v___x_5431_ = l_Lean_stringToMessageData(v___x_5430_);
return v___x_5431_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19(void){
_start:
{
lean_object* v___x_5433_; lean_object* v___x_5434_; 
v___x_5433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__18));
v___x_5434_ = l_Lean_stringToMessageData(v___x_5433_);
return v___x_5434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(lean_object* v_scope_5435_, lean_object* v_goal_5436_, lean_object* v_info_5437_, lean_object* v_thm_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_){
_start:
{
lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v___y_5455_; lean_object* v___y_5456_; lean_object* v___y_5457_; lean_object* v___y_5458_; lean_object* v___y_5459_; lean_object* v___y_5460_; lean_object* v___y_5461_; lean_object* v___y_5462_; lean_object* v___y_5463_; lean_object* v___y_5500_; lean_object* v___y_5501_; lean_object* v___y_5502_; lean_object* v___y_5503_; lean_object* v___y_5504_; lean_object* v___y_5505_; lean_object* v___y_5506_; lean_object* v___y_5507_; lean_object* v___y_5508_; lean_object* v___y_5509_; lean_object* v___y_5510_; lean_object* v___y_5511_; lean_object* v___y_5512_; lean_object* v___y_5513_; lean_object* v___y_5514_; lean_object* v___y_5539_; lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v___y_5542_; lean_object* v___y_5543_; lean_object* v___y_5544_; lean_object* v___y_5545_; lean_object* v___y_5546_; lean_object* v___y_5547_; lean_object* v___y_5548_; lean_object* v___y_5549_; lean_object* v___y_5550_; lean_object* v___y_5578_; lean_object* v___y_5579_; lean_object* v___y_5580_; lean_object* v___y_5581_; lean_object* v___y_5582_; lean_object* v___y_5583_; lean_object* v___y_5584_; lean_object* v___y_5585_; lean_object* v___y_5586_; lean_object* v___y_5587_; lean_object* v___y_5588_; lean_object* v___y_5589_; lean_object* v___y_5590_; lean_object* v___y_5621_; lean_object* v___y_5622_; lean_object* v___y_5675_; lean_object* v___y_5678_; lean_object* v___x_5708_; 
lean_inc_ref(v_info_5437_);
lean_inc_ref(v_thm_5438_);
v___x_5708_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(v_thm_5438_, v_info_5437_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
if (lean_obj_tag(v___x_5708_) == 0)
{
v___y_5678_ = v___x_5708_;
goto v___jp_5677_;
}
else
{
lean_object* v_a_5709_; lean_object* v___y_5711_; lean_object* v___y_5712_; lean_object* v___y_5713_; uint8_t v___y_5743_; uint8_t v___x_5774_; 
v_a_5709_ = lean_ctor_get(v___x_5708_, 0);
lean_inc(v_a_5709_);
v___x_5774_ = l_Lean_Exception_isInterrupt(v_a_5709_);
if (v___x_5774_ == 0)
{
uint8_t v___x_5775_; 
lean_inc(v_a_5709_);
v___x_5775_ = l_Lean_Exception_isRuntime(v_a_5709_);
v___y_5743_ = v___x_5775_;
goto v___jp_5742_;
}
else
{
v___y_5743_ = v___x_5774_;
goto v___jp_5742_;
}
v___jp_5710_:
{
lean_object* v_excessArgs_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; 
v_excessArgs_5714_ = lean_ctor_get(v_info_5437_, 2);
lean_inc_ref(v___y_5711_);
v___x_5715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___y_5711_);
lean_ctor_set(v___x_5715_, 1, v___y_5713_);
v___x_5716_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_5717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5715_);
lean_ctor_set(v___x_5717_, 1, v___x_5716_);
v___x_5718_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5437_);
v___x_5719_ = l_Lean_indentExpr(v___x_5718_);
v___x_5720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5717_);
lean_ctor_set(v___x_5720_, 1, v___x_5719_);
v___x_5721_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11);
v___x_5722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5720_);
lean_ctor_set(v___x_5722_, 1, v___x_5721_);
v___x_5723_ = l_Lean_Exception_toMessageData(v_a_5709_);
v___x_5724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5722_);
lean_ctor_set(v___x_5724_, 1, v___x_5723_);
v___x_5725_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13);
v___x_5726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5724_);
lean_ctor_set(v___x_5726_, 1, v___x_5725_);
v___x_5727_ = l_Lean_indentExpr(v___y_5712_);
v___x_5728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5726_);
lean_ctor_set(v___x_5728_, 1, v___x_5727_);
v___x_5729_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15);
v___x_5730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5728_);
lean_ctor_set(v___x_5730_, 1, v___x_5729_);
v___x_5731_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_5437_);
v___x_5732_ = l_Lean_indentExpr(v___x_5731_);
v___x_5733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5733_, 0, v___x_5730_);
lean_ctor_set(v___x_5733_, 1, v___x_5732_);
v___x_5734_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17);
v___x_5735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5733_);
lean_ctor_set(v___x_5735_, 1, v___x_5734_);
lean_inc_ref(v_excessArgs_5714_);
v___x_5736_ = lean_array_to_list(v_excessArgs_5714_);
v___x_5737_ = lean_box(0);
v___x_5738_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(v___x_5736_, v___x_5737_);
v___x_5739_ = l_Lean_MessageData_ofList(v___x_5738_);
v___x_5740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5735_);
lean_ctor_set(v___x_5740_, 1, v___x_5739_);
v___x_5741_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5740_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
v___y_5678_ = v___x_5741_;
goto v___jp_5677_;
}
v___jp_5742_:
{
if (v___y_5743_ == 0)
{
lean_object* v___x_5744_; 
lean_dec_ref_known(v___x_5708_, 1);
lean_inc(v_goal_5436_);
v___x_5744_ = l_Lean_MVarId_getType(v_goal_5436_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
if (lean_obj_tag(v___x_5744_) == 0)
{
lean_object* v_a_5745_; lean_object* v_proof_5746_; lean_object* v___x_5747_; 
v_a_5745_ = lean_ctor_get(v___x_5744_, 0);
lean_inc(v_a_5745_);
lean_dec_ref_known(v___x_5744_, 1);
v_proof_5746_ = lean_ctor_get(v_thm_5438_, 1);
v___x_5747_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19);
switch(lean_obj_tag(v_proof_5746_))
{
case 0:
{
lean_object* v_declName_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; 
v_declName_5748_ = lean_ctor_get(v_proof_5746_, 0);
v___x_5749_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_5748_);
v___x_5750_ = l_Lean_MessageData_ofName(v_declName_5748_);
v___x_5751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5749_);
lean_ctor_set(v___x_5751_, 1, v___x_5750_);
v___y_5711_ = v___x_5747_;
v___y_5712_ = v_a_5745_;
v___y_5713_ = v___x_5751_;
goto v___jp_5710_;
}
case 1:
{
lean_object* v_fvarId_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; 
v_fvarId_5752_ = lean_ctor_get(v_proof_5746_, 0);
v___x_5753_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_5752_);
v___x_5754_ = l_Lean_mkFVar(v_fvarId_5752_);
v___x_5755_ = l_Lean_MessageData_ofExpr(v___x_5754_);
v___x_5756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5753_);
lean_ctor_set(v___x_5756_, 1, v___x_5755_);
v___y_5711_ = v___x_5747_;
v___y_5712_ = v_a_5745_;
v___y_5713_ = v___x_5756_;
goto v___jp_5710_;
}
default: 
{
lean_object* v_ref_5757_; lean_object* v_proof_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; 
v_ref_5757_ = lean_ctor_get(v_proof_5746_, 1);
v_proof_5758_ = lean_ctor_get(v_proof_5746_, 2);
v___x_5759_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_5757_);
v___x_5760_ = l_Lean_MessageData_ofSyntax(v_ref_5757_);
v___x_5761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5761_, 0, v___x_5759_);
lean_ctor_set(v___x_5761_, 1, v___x_5760_);
v___x_5762_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_5763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5763_, 0, v___x_5761_);
lean_ctor_set(v___x_5763_, 1, v___x_5762_);
lean_inc_ref(v_proof_5758_);
v___x_5764_ = l_Lean_MessageData_ofExpr(v_proof_5758_);
v___x_5765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5765_, 0, v___x_5763_);
lean_ctor_set(v___x_5765_, 1, v___x_5764_);
v___y_5711_ = v___x_5747_;
v___y_5712_ = v_a_5745_;
v___y_5713_ = v___x_5765_;
goto v___jp_5710_;
}
}
}
else
{
lean_object* v_a_5766_; lean_object* v___x_5768_; uint8_t v_isShared_5769_; uint8_t v_isSharedCheck_5773_; 
lean_dec(v_a_5709_);
lean_dec_ref(v_thm_5438_);
lean_dec_ref(v_info_5437_);
lean_dec(v_goal_5436_);
lean_dec_ref(v_scope_5435_);
v_a_5766_ = lean_ctor_get(v___x_5744_, 0);
v_isSharedCheck_5773_ = !lean_is_exclusive(v___x_5744_);
if (v_isSharedCheck_5773_ == 0)
{
v___x_5768_ = v___x_5744_;
v_isShared_5769_ = v_isSharedCheck_5773_;
goto v_resetjp_5767_;
}
else
{
lean_inc(v_a_5766_);
lean_dec(v___x_5744_);
v___x_5768_ = lean_box(0);
v_isShared_5769_ = v_isSharedCheck_5773_;
goto v_resetjp_5767_;
}
v_resetjp_5767_:
{
lean_object* v___x_5771_; 
if (v_isShared_5769_ == 0)
{
v___x_5771_ = v___x_5768_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_a_5766_);
v___x_5771_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
return v___x_5771_;
}
}
}
}
else
{
lean_dec(v_a_5709_);
v___y_5678_ = v___x_5708_;
goto v___jp_5677_;
}
}
}
v___jp_5451_:
{
lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5464_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1);
v___x_5465_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5437_);
lean_dec_ref(v_info_5437_);
v___x_5466_ = l_Lean_indentExpr(v___x_5465_);
v___x_5467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5467_, 0, v___x_5464_);
lean_ctor_set(v___x_5467_, 1, v___x_5466_);
v___x_5468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5468_, 0, v___x_5467_);
v___x_5469_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v___y_5452_, v_goal_5436_, v___x_5468_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
if (lean_obj_tag(v___x_5469_) == 0)
{
lean_object* v_a_5470_; lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5490_; 
v_a_5470_ = lean_ctor_get(v___x_5469_, 0);
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5469_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5472_ = v___x_5469_;
v_isShared_5473_ = v_isSharedCheck_5490_;
goto v_resetjp_5471_;
}
else
{
lean_inc(v_a_5470_);
lean_dec(v___x_5469_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5490_;
goto v_resetjp_5471_;
}
v_resetjp_5471_:
{
if (lean_obj_tag(v_a_5470_) == 1)
{
lean_object* v_mvarIds_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5485_; 
v_mvarIds_5474_ = lean_ctor_get(v_a_5470_, 0);
v_isSharedCheck_5485_ = !lean_is_exclusive(v_a_5470_);
if (v_isSharedCheck_5485_ == 0)
{
v___x_5476_ = v_a_5470_;
v_isShared_5477_ = v_isSharedCheck_5485_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_mvarIds_5474_);
lean_dec(v_a_5470_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5485_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5478_; lean_object* v___x_5480_; 
v___x_5478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5478_, 0, v_scope_5435_);
lean_ctor_set(v___x_5478_, 1, v_mvarIds_5474_);
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 0, v___x_5478_);
v___x_5480_ = v___x_5476_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5478_);
v___x_5480_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
lean_object* v___x_5482_; 
if (v_isShared_5473_ == 0)
{
lean_ctor_set(v___x_5472_, 0, v___x_5480_);
v___x_5482_ = v___x_5472_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5480_);
v___x_5482_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
return v___x_5482_;
}
}
}
}
else
{
lean_object* v___x_5486_; lean_object* v___x_5488_; 
lean_dec(v_a_5470_);
lean_dec_ref(v_scope_5435_);
v___x_5486_ = lean_box(0);
if (v_isShared_5473_ == 0)
{
lean_ctor_set(v___x_5472_, 0, v___x_5486_);
v___x_5488_ = v___x_5472_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v___x_5486_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
}
else
{
lean_object* v_a_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5498_; 
lean_dec_ref(v_scope_5435_);
v_a_5491_ = lean_ctor_get(v___x_5469_, 0);
v_isSharedCheck_5498_ = !lean_is_exclusive(v___x_5469_);
if (v_isSharedCheck_5498_ == 0)
{
v___x_5493_ = v___x_5469_;
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_a_5491_);
lean_dec(v___x_5469_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v___x_5496_; 
if (v_isShared_5494_ == 0)
{
v___x_5496_ = v___x_5493_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_a_5491_);
v___x_5496_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
return v___x_5496_;
}
}
}
}
v___jp_5499_:
{
lean_object* v_excessArgs_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; 
v_excessArgs_5515_ = lean_ctor_get(v_info_5437_, 2);
lean_inc_ref(v___y_5501_);
v___x_5516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5516_, 0, v___y_5501_);
lean_ctor_set(v___x_5516_, 1, v___y_5514_);
v___x_5517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_5518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5518_, 0, v___x_5516_);
lean_ctor_set(v___x_5518_, 1, v___x_5517_);
v___x_5519_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5437_);
v___x_5520_ = l_Lean_MessageData_ofExpr(v___x_5519_);
v___x_5521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5521_, 0, v___x_5518_);
lean_ctor_set(v___x_5521_, 1, v___x_5520_);
v___x_5522_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5);
v___x_5523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5523_, 0, v___x_5521_);
lean_ctor_set(v___x_5523_, 1, v___x_5522_);
lean_inc_ref(v_excessArgs_5515_);
v___x_5524_ = lean_array_to_list(v_excessArgs_5515_);
v___x_5525_ = lean_box(0);
v___x_5526_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(v___x_5524_, v___x_5525_);
v___x_5527_ = l_Lean_MessageData_ofList(v___x_5526_);
v___x_5528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5528_, 0, v___x_5523_);
lean_ctor_set(v___x_5528_, 1, v___x_5527_);
lean_inc(v___y_5510_);
v___x_5529_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___y_5510_, v___x_5528_, v___y_5513_, v___y_5504_, v___y_5506_, v___y_5505_);
if (lean_obj_tag(v___x_5529_) == 0)
{
lean_dec_ref_known(v___x_5529_, 1);
v___y_5452_ = v___y_5500_;
v___y_5453_ = v___y_5511_;
v___y_5454_ = v___y_5512_;
v___y_5455_ = v___y_5507_;
v___y_5456_ = v___y_5509_;
v___y_5457_ = v___y_5502_;
v___y_5458_ = v___y_5503_;
v___y_5459_ = v___y_5508_;
v___y_5460_ = v___y_5513_;
v___y_5461_ = v___y_5504_;
v___y_5462_ = v___y_5506_;
v___y_5463_ = v___y_5505_;
goto v___jp_5451_;
}
else
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5537_; 
lean_dec_ref(v___y_5500_);
lean_dec_ref(v_info_5437_);
lean_dec(v_goal_5436_);
lean_dec_ref(v_scope_5435_);
v_a_5530_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5537_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5532_ = v___x_5529_;
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5529_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v___x_5535_; 
if (v_isShared_5533_ == 0)
{
v___x_5535_ = v___x_5532_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_a_5530_);
v___x_5535_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
return v___x_5535_;
}
}
}
}
v___jp_5538_:
{
lean_object* v_options_5551_; uint8_t v_hasTrace_5552_; 
v_options_5551_ = lean_ctor_get(v___y_5549_, 2);
v_hasTrace_5552_ = lean_ctor_get_uint8(v_options_5551_, sizeof(void*)*1);
if (v_hasTrace_5552_ == 0)
{
lean_dec_ref(v_thm_5438_);
v___y_5452_ = v___y_5539_;
v___y_5453_ = v___y_5540_;
v___y_5454_ = v___y_5541_;
v___y_5455_ = v___y_5542_;
v___y_5456_ = v___y_5543_;
v___y_5457_ = v___y_5544_;
v___y_5458_ = v___y_5545_;
v___y_5459_ = v___y_5546_;
v___y_5460_ = v___y_5547_;
v___y_5461_ = v___y_5548_;
v___y_5462_ = v___y_5549_;
v___y_5463_ = v___y_5550_;
goto v___jp_5451_;
}
else
{
lean_object* v_inheritedTraceOptions_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; uint8_t v___x_5556_; 
v_inheritedTraceOptions_5553_ = lean_ctor_get(v___y_5549_, 13);
v___x_5554_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5555_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5556_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5553_, v_options_5551_, v___x_5555_);
if (v___x_5556_ == 0)
{
lean_dec_ref(v_thm_5438_);
v___y_5452_ = v___y_5539_;
v___y_5453_ = v___y_5540_;
v___y_5454_ = v___y_5541_;
v___y_5455_ = v___y_5542_;
v___y_5456_ = v___y_5543_;
v___y_5457_ = v___y_5544_;
v___y_5458_ = v___y_5545_;
v___y_5459_ = v___y_5546_;
v___y_5460_ = v___y_5547_;
v___y_5461_ = v___y_5548_;
v___y_5462_ = v___y_5549_;
v___y_5463_ = v___y_5550_;
goto v___jp_5451_;
}
else
{
lean_object* v_proof_5557_; lean_object* v___x_5558_; 
v_proof_5557_ = lean_ctor_get(v_thm_5438_, 1);
lean_inc_ref(v_proof_5557_);
lean_dec_ref(v_thm_5438_);
v___x_5558_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7);
switch(lean_obj_tag(v_proof_5557_))
{
case 0:
{
lean_object* v_declName_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; 
v_declName_5559_ = lean_ctor_get(v_proof_5557_, 0);
lean_inc(v_declName_5559_);
lean_dec_ref_known(v_proof_5557_, 1);
v___x_5560_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_5561_ = l_Lean_MessageData_ofName(v_declName_5559_);
v___x_5562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5562_, 0, v___x_5560_);
lean_ctor_set(v___x_5562_, 1, v___x_5561_);
v___y_5500_ = v___y_5539_;
v___y_5501_ = v___x_5558_;
v___y_5502_ = v___y_5544_;
v___y_5503_ = v___y_5545_;
v___y_5504_ = v___y_5548_;
v___y_5505_ = v___y_5550_;
v___y_5506_ = v___y_5549_;
v___y_5507_ = v___y_5542_;
v___y_5508_ = v___y_5546_;
v___y_5509_ = v___y_5543_;
v___y_5510_ = v___x_5554_;
v___y_5511_ = v___y_5540_;
v___y_5512_ = v___y_5541_;
v___y_5513_ = v___y_5547_;
v___y_5514_ = v___x_5562_;
goto v___jp_5499_;
}
case 1:
{
lean_object* v_fvarId_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; 
v_fvarId_5563_ = lean_ctor_get(v_proof_5557_, 0);
lean_inc(v_fvarId_5563_);
lean_dec_ref_known(v_proof_5557_, 1);
v___x_5564_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_5565_ = l_Lean_mkFVar(v_fvarId_5563_);
v___x_5566_ = l_Lean_MessageData_ofExpr(v___x_5565_);
v___x_5567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5567_, 0, v___x_5564_);
lean_ctor_set(v___x_5567_, 1, v___x_5566_);
v___y_5500_ = v___y_5539_;
v___y_5501_ = v___x_5558_;
v___y_5502_ = v___y_5544_;
v___y_5503_ = v___y_5545_;
v___y_5504_ = v___y_5548_;
v___y_5505_ = v___y_5550_;
v___y_5506_ = v___y_5549_;
v___y_5507_ = v___y_5542_;
v___y_5508_ = v___y_5546_;
v___y_5509_ = v___y_5543_;
v___y_5510_ = v___x_5554_;
v___y_5511_ = v___y_5540_;
v___y_5512_ = v___y_5541_;
v___y_5513_ = v___y_5547_;
v___y_5514_ = v___x_5567_;
goto v___jp_5499_;
}
default: 
{
lean_object* v_ref_5568_; lean_object* v_proof_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; 
v_ref_5568_ = lean_ctor_get(v_proof_5557_, 1);
lean_inc(v_ref_5568_);
v_proof_5569_ = lean_ctor_get(v_proof_5557_, 2);
lean_inc_ref(v_proof_5569_);
lean_dec_ref_known(v_proof_5557_, 3);
v___x_5570_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_5571_ = l_Lean_MessageData_ofSyntax(v_ref_5568_);
v___x_5572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5572_, 0, v___x_5570_);
lean_ctor_set(v___x_5572_, 1, v___x_5571_);
v___x_5573_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_5574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5574_, 0, v___x_5572_);
lean_ctor_set(v___x_5574_, 1, v___x_5573_);
v___x_5575_ = l_Lean_MessageData_ofExpr(v_proof_5569_);
v___x_5576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5576_, 0, v___x_5574_);
lean_ctor_set(v___x_5576_, 1, v___x_5575_);
v___y_5500_ = v___y_5539_;
v___y_5501_ = v___x_5558_;
v___y_5502_ = v___y_5544_;
v___y_5503_ = v___y_5545_;
v___y_5504_ = v___y_5548_;
v___y_5505_ = v___y_5550_;
v___y_5506_ = v___y_5549_;
v___y_5507_ = v___y_5542_;
v___y_5508_ = v___y_5546_;
v___y_5509_ = v___y_5543_;
v___y_5510_ = v___x_5554_;
v___y_5511_ = v___y_5540_;
v___y_5512_ = v___y_5541_;
v___y_5513_ = v___y_5547_;
v___y_5514_ = v___x_5576_;
goto v___jp_5499_;
}
}
}
}
}
v___jp_5577_:
{
lean_object* v___x_5591_; 
v___x_5591_ = l_Lean_Elab_Tactic_VCGen_FrameSplit_instantiateMVarsS(v___y_5578_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_);
if (lean_obj_tag(v___x_5591_) == 0)
{
lean_object* v_a_5592_; lean_object* v___x_5593_; 
v_a_5592_ = lean_ctor_get(v___x_5591_, 0);
lean_inc(v_a_5592_);
lean_dec_ref_known(v___x_5591_, 1);
v___x_5593_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule(v_goal_5436_, v_info_5437_, v___y_5579_, v_a_5592_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_);
if (lean_obj_tag(v___x_5593_) == 0)
{
lean_object* v_a_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5603_; 
v_a_5594_ = lean_ctor_get(v___x_5593_, 0);
v_isSharedCheck_5603_ = !lean_is_exclusive(v___x_5593_);
if (v_isSharedCheck_5603_ == 0)
{
v___x_5596_ = v___x_5593_;
v_isShared_5597_ = v_isSharedCheck_5603_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_a_5594_);
lean_dec(v___x_5593_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5603_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5601_; 
v___x_5598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5598_, 0, v_scope_5435_);
lean_ctor_set(v___x_5598_, 1, v_a_5594_);
v___x_5599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5599_, 0, v___x_5598_);
if (v_isShared_5597_ == 0)
{
lean_ctor_set(v___x_5596_, 0, v___x_5599_);
v___x_5601_ = v___x_5596_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v___x_5599_);
v___x_5601_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
return v___x_5601_;
}
}
}
else
{
lean_object* v_a_5604_; lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5611_; 
lean_dec_ref(v_scope_5435_);
v_a_5604_ = lean_ctor_get(v___x_5593_, 0);
v_isSharedCheck_5611_ = !lean_is_exclusive(v___x_5593_);
if (v_isSharedCheck_5611_ == 0)
{
v___x_5606_ = v___x_5593_;
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
else
{
lean_inc(v_a_5604_);
lean_dec(v___x_5593_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v___x_5609_; 
if (v_isShared_5607_ == 0)
{
v___x_5609_ = v___x_5606_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_a_5604_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
}
}
}
}
else
{
lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5619_; 
lean_dec_ref(v___y_5579_);
lean_dec_ref(v_info_5437_);
lean_dec(v_goal_5436_);
lean_dec_ref(v_scope_5435_);
v_a_5612_ = lean_ctor_get(v___x_5591_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5591_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5614_ = v___x_5591_;
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5591_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5617_; 
if (v_isShared_5615_ == 0)
{
v___x_5617_ = v___x_5614_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_a_5612_);
v___x_5617_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
return v___x_5617_;
}
}
}
}
v___jp_5620_:
{
lean_object* v___x_5623_; 
lean_inc_ref(v_info_5437_);
lean_inc_ref(v___y_5622_);
v___x_5623_ = l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(v___y_5622_, v_info_5437_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
if (lean_obj_tag(v___x_5623_) == 0)
{
lean_object* v_a_5624_; lean_object* v_mkOpAppM_5625_; lean_object* v_proc_5626_; lean_object* v___x_5627_; lean_object* v___f_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; 
v_a_5624_ = lean_ctor_get(v___x_5623_, 0);
lean_inc(v_a_5624_);
lean_dec_ref_known(v___x_5623_, 1);
v_mkOpAppM_5625_ = lean_ctor_get(v___y_5622_, 2);
v_proc_5626_ = lean_ctor_get(v___y_5622_, 4);
lean_inc_ref(v_thm_5438_);
v___x_5627_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorem_global_x3f(v_thm_5438_);
lean_inc_ref_n(v_info_5437_, 2);
lean_inc_ref(v_mkOpAppM_5625_);
v___f_5628_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5628_, 0, v_mkOpAppM_5625_);
lean_closure_set(v___f_5628_, 1, v_info_5437_);
lean_inc_ref(v___y_5621_);
lean_inc(v_goal_5436_);
v___x_5629_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5629_, 0, v_info_5437_);
lean_ctor_set(v___x_5629_, 1, v_goal_5436_);
lean_ctor_set(v___x_5629_, 2, v_a_5624_);
lean_ctor_set(v___x_5629_, 3, v___x_5627_);
lean_ctor_set(v___x_5629_, 4, v___y_5621_);
lean_ctor_set(v___x_5629_, 5, v___f_5628_);
lean_inc_ref(v_proc_5626_);
lean_inc(v_a_5449_);
lean_inc_ref(v_a_5448_);
lean_inc(v_a_5447_);
lean_inc_ref(v_a_5446_);
lean_inc(v_a_5445_);
lean_inc_ref(v_a_5444_);
v___x_5630_ = lean_apply_8(v_proc_5626_, v___x_5629_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_, lean_box(0));
if (lean_obj_tag(v___x_5630_) == 0)
{
lean_object* v_a_5631_; 
v_a_5631_ = lean_ctor_get(v___x_5630_, 0);
lean_inc(v_a_5631_);
lean_dec_ref_known(v___x_5630_, 1);
if (lean_obj_tag(v_a_5631_) == 1)
{
lean_object* v_options_5632_; uint8_t v_hasTrace_5633_; 
lean_dec_ref(v___y_5621_);
lean_dec_ref(v_thm_5438_);
v_options_5632_ = lean_ctor_get(v_a_5448_, 2);
v_hasTrace_5633_ = lean_ctor_get_uint8(v_options_5632_, sizeof(void*)*1);
if (v_hasTrace_5633_ == 0)
{
lean_object* v_val_5634_; 
v_val_5634_ = lean_ctor_get(v_a_5631_, 0);
lean_inc(v_val_5634_);
lean_dec_ref_known(v_a_5631_, 1);
v___y_5578_ = v_val_5634_;
v___y_5579_ = v___y_5622_;
v___y_5580_ = v_a_5439_;
v___y_5581_ = v_a_5440_;
v___y_5582_ = v_a_5441_;
v___y_5583_ = v_a_5442_;
v___y_5584_ = v_a_5443_;
v___y_5585_ = v_a_5444_;
v___y_5586_ = v_a_5445_;
v___y_5587_ = v_a_5446_;
v___y_5588_ = v_a_5447_;
v___y_5589_ = v_a_5448_;
v___y_5590_ = v_a_5449_;
goto v___jp_5577_;
}
else
{
lean_object* v_val_5635_; lean_object* v_inheritedTraceOptions_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; uint8_t v___x_5639_; 
v_val_5635_ = lean_ctor_get(v_a_5631_, 0);
lean_inc(v_val_5635_);
lean_dec_ref_known(v_a_5631_, 1);
v_inheritedTraceOptions_5636_ = lean_ctor_get(v_a_5448_, 13);
v___x_5637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5638_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5639_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5636_, v_options_5632_, v___x_5638_);
if (v___x_5639_ == 0)
{
v___y_5578_ = v_val_5635_;
v___y_5579_ = v___y_5622_;
v___y_5580_ = v_a_5439_;
v___y_5581_ = v_a_5440_;
v___y_5582_ = v_a_5441_;
v___y_5583_ = v_a_5442_;
v___y_5584_ = v_a_5443_;
v___y_5585_ = v_a_5444_;
v___y_5586_ = v_a_5445_;
v___y_5587_ = v_a_5446_;
v___y_5588_ = v_a_5447_;
v___y_5589_ = v_a_5448_;
v___y_5590_ = v_a_5449_;
goto v___jp_5577_;
}
else
{
lean_object* v_frame_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; 
v_frame_5640_ = lean_ctor_get(v_val_5635_, 0);
v___x_5641_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9);
v___x_5642_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5437_);
v___x_5643_ = l_Lean_MessageData_ofExpr(v___x_5642_);
v___x_5644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5641_);
lean_ctor_set(v___x_5644_, 1, v___x_5643_);
v___x_5645_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3);
v___x_5646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5646_, 0, v___x_5644_);
lean_ctor_set(v___x_5646_, 1, v___x_5645_);
lean_inc_ref(v_frame_5640_);
v___x_5647_ = l_Lean_indentExpr(v_frame_5640_);
v___x_5648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5646_);
lean_ctor_set(v___x_5648_, 1, v___x_5647_);
v___x_5649_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5637_, v___x_5648_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
if (lean_obj_tag(v___x_5649_) == 0)
{
lean_dec_ref_known(v___x_5649_, 1);
v___y_5578_ = v_val_5635_;
v___y_5579_ = v___y_5622_;
v___y_5580_ = v_a_5439_;
v___y_5581_ = v_a_5440_;
v___y_5582_ = v_a_5441_;
v___y_5583_ = v_a_5442_;
v___y_5584_ = v_a_5443_;
v___y_5585_ = v_a_5444_;
v___y_5586_ = v_a_5445_;
v___y_5587_ = v_a_5446_;
v___y_5588_ = v_a_5447_;
v___y_5589_ = v_a_5448_;
v___y_5590_ = v_a_5449_;
goto v___jp_5577_;
}
else
{
lean_object* v_a_5650_; lean_object* v___x_5652_; uint8_t v_isShared_5653_; uint8_t v_isSharedCheck_5657_; 
lean_dec(v_val_5635_);
lean_dec_ref(v___y_5622_);
lean_dec_ref(v_info_5437_);
lean_dec(v_goal_5436_);
lean_dec_ref(v_scope_5435_);
v_a_5650_ = lean_ctor_get(v___x_5649_, 0);
v_isSharedCheck_5657_ = !lean_is_exclusive(v___x_5649_);
if (v_isSharedCheck_5657_ == 0)
{
v___x_5652_ = v___x_5649_;
v_isShared_5653_ = v_isSharedCheck_5657_;
goto v_resetjp_5651_;
}
else
{
lean_inc(v_a_5650_);
lean_dec(v___x_5649_);
v___x_5652_ = lean_box(0);
v_isShared_5653_ = v_isSharedCheck_5657_;
goto v_resetjp_5651_;
}
v_resetjp_5651_:
{
lean_object* v___x_5655_; 
if (v_isShared_5653_ == 0)
{
v___x_5655_ = v___x_5652_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_a_5650_);
v___x_5655_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
return v___x_5655_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5631_);
lean_dec_ref(v___y_5622_);
v___y_5539_ = v___y_5621_;
v___y_5540_ = v_a_5439_;
v___y_5541_ = v_a_5440_;
v___y_5542_ = v_a_5441_;
v___y_5543_ = v_a_5442_;
v___y_5544_ = v_a_5443_;
v___y_5545_ = v_a_5444_;
v___y_5546_ = v_a_5445_;
v___y_5547_ = v_a_5446_;
v___y_5548_ = v_a_5447_;
v___y_5549_ = v_a_5448_;
v___y_5550_ = v_a_5449_;
goto v___jp_5538_;
}
}
else
{
lean_object* v_a_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
lean_dec_ref(v___y_5622_);
lean_dec_ref(v___y_5621_);
lean_dec_ref(v_thm_5438_);
lean_dec_ref(v_info_5437_);
lean_dec(v_goal_5436_);
lean_dec_ref(v_scope_5435_);
v_a_5658_ = lean_ctor_get(v___x_5630_, 0);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5630_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5660_ = v___x_5630_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_a_5658_);
lean_dec(v___x_5630_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
else
{
lean_object* v_a_5666_; lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5673_; 
lean_dec_ref(v___y_5622_);
lean_dec_ref(v___y_5621_);
lean_dec_ref(v_thm_5438_);
lean_dec_ref(v_info_5437_);
lean_dec(v_goal_5436_);
lean_dec_ref(v_scope_5435_);
v_a_5666_ = lean_ctor_get(v___x_5623_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5623_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5668_ = v___x_5623_;
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
else
{
lean_inc(v_a_5666_);
lean_dec(v___x_5623_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5671_; 
if (v_isShared_5669_ == 0)
{
v___x_5671_ = v___x_5668_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_a_5666_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
}
v___jp_5674_:
{
lean_object* v___x_5676_; 
v___x_5676_ = l_Lean_Elab_Tactic_VCGen_meetFrameProc;
v___y_5621_ = v___y_5675_;
v___y_5622_ = v___x_5676_;
goto v___jp_5620_;
}
v___jp_5677_:
{
if (lean_obj_tag(v___y_5678_) == 0)
{
lean_object* v_a_5679_; lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5699_; 
v_a_5679_ = lean_ctor_get(v___y_5678_, 0);
v_isSharedCheck_5699_ = !lean_is_exclusive(v___y_5678_);
if (v_isSharedCheck_5699_ == 0)
{
v___x_5681_ = v___y_5678_;
v_isShared_5682_ = v_isSharedCheck_5699_;
goto v_resetjp_5680_;
}
else
{
lean_inc(v_a_5679_);
lean_dec(v___y_5678_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5699_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
if (lean_obj_tag(v_a_5679_) == 1)
{
uint8_t v_conjunctivePre_5683_; 
lean_del_object(v___x_5681_);
v_conjunctivePre_5683_ = lean_ctor_get_uint8(v_thm_5438_, sizeof(void*)*4);
if (v_conjunctivePre_5683_ == 0)
{
lean_object* v_val_5684_; lean_object* v___x_5685_; uint8_t v___x_5686_; 
v_val_5684_ = lean_ctor_get(v_a_5679_, 0);
lean_inc(v_val_5684_);
lean_dec_ref_known(v_a_5679_, 1);
v___x_5685_ = l_Lean_Elab_Tactic_VCGen_WPApp_post(v_info_5437_);
v___x_5686_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost(v___x_5685_);
if (v___x_5686_ == 0)
{
lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; 
v___x_5687_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v_info_5437_);
v___x_5688_ = l_Lean_Expr_getAppFn(v___x_5687_);
lean_dec_ref(v___x_5687_);
v___x_5689_ = l_Lean_Expr_constName_x3f(v___x_5688_);
lean_dec_ref(v___x_5688_);
if (lean_obj_tag(v___x_5689_) == 0)
{
v___y_5675_ = v_val_5684_;
goto v___jp_5674_;
}
else
{
lean_object* v_val_5690_; lean_object* v_frameProcs_5691_; lean_object* v___x_5692_; 
v_val_5690_ = lean_ctor_get(v___x_5689_, 0);
lean_inc(v_val_5690_);
lean_dec_ref_known(v___x_5689_, 1);
v_frameProcs_5691_ = lean_ctor_get(v_a_5439_, 1);
v___x_5692_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(v_frameProcs_5691_, v_val_5690_);
lean_dec(v_val_5690_);
if (lean_obj_tag(v___x_5692_) == 0)
{
v___y_5675_ = v_val_5684_;
goto v___jp_5674_;
}
else
{
lean_object* v_val_5693_; 
v_val_5693_ = lean_ctor_get(v___x_5692_, 0);
lean_inc(v_val_5693_);
lean_dec_ref_known(v___x_5692_, 1);
v___y_5621_ = v_val_5684_;
v___y_5622_ = v_val_5693_;
goto v___jp_5620_;
}
}
}
else
{
v___y_5539_ = v_val_5684_;
v___y_5540_ = v_a_5439_;
v___y_5541_ = v_a_5440_;
v___y_5542_ = v_a_5441_;
v___y_5543_ = v_a_5442_;
v___y_5544_ = v_a_5443_;
v___y_5545_ = v_a_5444_;
v___y_5546_ = v_a_5445_;
v___y_5547_ = v_a_5446_;
v___y_5548_ = v_a_5447_;
v___y_5549_ = v_a_5448_;
v___y_5550_ = v_a_5449_;
goto v___jp_5538_;
}
}
else
{
lean_object* v_val_5694_; 
v_val_5694_ = lean_ctor_get(v_a_5679_, 0);
lean_inc(v_val_5694_);
lean_dec_ref_known(v_a_5679_, 1);
v___y_5539_ = v_val_5694_;
v___y_5540_ = v_a_5439_;
v___y_5541_ = v_a_5440_;
v___y_5542_ = v_a_5441_;
v___y_5543_ = v_a_5442_;
v___y_5544_ = v_a_5443_;
v___y_5545_ = v_a_5444_;
v___y_5546_ = v_a_5445_;
v___y_5547_ = v_a_5446_;
v___y_5548_ = v_a_5447_;
v___y_5549_ = v_a_5448_;
v___y_5550_ = v_a_5449_;
goto v___jp_5538_;
}
}
else
{
lean_object* v___x_5695_; lean_object* v___x_5697_; 
lean_dec(v_a_5679_);
lean_dec_ref(v_thm_5438_);
lean_dec_ref(v_info_5437_);
lean_dec(v_goal_5436_);
lean_dec_ref(v_scope_5435_);
v___x_5695_ = lean_box(0);
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 0, v___x_5695_);
v___x_5697_ = v___x_5681_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5695_);
v___x_5697_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
return v___x_5697_;
}
}
}
}
else
{
lean_object* v_a_5700_; lean_object* v___x_5702_; uint8_t v_isShared_5703_; uint8_t v_isSharedCheck_5707_; 
lean_dec_ref(v_thm_5438_);
lean_dec_ref(v_info_5437_);
lean_dec(v_goal_5436_);
lean_dec_ref(v_scope_5435_);
v_a_5700_ = lean_ctor_get(v___y_5678_, 0);
v_isSharedCheck_5707_ = !lean_is_exclusive(v___y_5678_);
if (v_isSharedCheck_5707_ == 0)
{
v___x_5702_ = v___y_5678_;
v_isShared_5703_ = v_isSharedCheck_5707_;
goto v_resetjp_5701_;
}
else
{
lean_inc(v_a_5700_);
lean_dec(v___y_5678_);
v___x_5702_ = lean_box(0);
v_isShared_5703_ = v_isSharedCheck_5707_;
goto v_resetjp_5701_;
}
v_resetjp_5701_:
{
lean_object* v___x_5705_; 
if (v_isShared_5703_ == 0)
{
v___x_5705_ = v___x_5702_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5706_; 
v_reuseFailAlloc_5706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5706_, 0, v_a_5700_);
v___x_5705_ = v_reuseFailAlloc_5706_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
return v___x_5705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___boxed(lean_object* v_scope_5776_, lean_object* v_goal_5777_, lean_object* v_info_5778_, lean_object* v_thm_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_){
_start:
{
lean_object* v_res_5792_; 
v_res_5792_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(v_scope_5776_, v_goal_5777_, v_info_5778_, v_thm_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_);
lean_dec(v_a_5790_);
lean_dec_ref(v_a_5789_);
lean_dec(v_a_5788_);
lean_dec_ref(v_a_5787_);
lean_dec(v_a_5786_);
lean_dec_ref(v_a_5785_);
lean_dec(v_a_5784_);
lean_dec_ref(v_a_5783_);
lean_dec(v_a_5782_);
lean_dec(v_a_5781_);
lean_dec_ref(v_a_5780_);
return v_res_5792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1(lean_object* v_00_u03b2_5793_, lean_object* v_m_5794_, lean_object* v_a_5795_){
_start:
{
lean_object* v___x_5796_; 
v___x_5796_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(v_m_5794_, v_a_5795_);
return v___x_5796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___boxed(lean_object* v_00_u03b2_5797_, lean_object* v_m_5798_, lean_object* v_a_5799_){
_start:
{
lean_object* v_res_5800_; 
v_res_5800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1(v_00_u03b2_5797_, v_m_5798_, v_a_5799_);
lean_dec(v_a_5799_);
lean_dec_ref(v_m_5798_);
return v_res_5800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1(lean_object* v_00_u03b2_5801_, lean_object* v_a_5802_, lean_object* v_x_5803_){
_start:
{
lean_object* v___x_5804_; 
v___x_5804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(v_a_5802_, v_x_5803_);
return v___x_5804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5805_, lean_object* v_a_5806_, lean_object* v_x_5807_){
_start:
{
lean_object* v_res_5808_; 
v_res_5808_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1(v_00_u03b2_5805_, v_a_5806_, v_x_5807_);
lean_dec(v_x_5807_);
lean_dec(v_a_5806_);
return v_res_5808_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_5813_; lean_object* v___x_5814_; 
v___x_5813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__1));
v___x_5814_ = l_Lean_stringToMessageData(v___x_5813_);
return v___x_5814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(lean_object* v_scope_5815_, lean_object* v_goal_5816_, lean_object* v_info_5817_, lean_object* v___x_5818_, lean_object* v_as_5819_, size_t v_sz_5820_, size_t v_i_5821_, lean_object* v_b_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_){
_start:
{
lean_object* v_a_5836_; uint8_t v___x_5840_; 
v___x_5840_ = lean_usize_dec_lt(v_i_5821_, v_sz_5820_);
if (v___x_5840_ == 0)
{
lean_object* v___x_5841_; 
lean_dec_ref(v___x_5818_);
lean_dec_ref(v_info_5817_);
lean_dec(v_goal_5816_);
lean_dec_ref(v_scope_5815_);
v___x_5841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5841_, 0, v_b_5822_);
return v___x_5841_;
}
else
{
lean_object* v_a_5842_; lean_object* v___x_5843_; 
lean_dec_ref(v_b_5822_);
v_a_5842_ = lean_array_uget_borrowed(v_as_5819_, v_i_5821_);
lean_inc(v_a_5842_);
lean_inc_ref(v_info_5817_);
lean_inc(v_goal_5816_);
lean_inc_ref(v_scope_5815_);
v___x_5843_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(v_scope_5815_, v_goal_5816_, v_info_5817_, v_a_5842_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
if (lean_obj_tag(v___x_5843_) == 0)
{
lean_object* v_a_5844_; lean_object* v___x_5846_; uint8_t v_isShared_5847_; uint8_t v_isSharedCheck_5896_; 
v_a_5844_ = lean_ctor_get(v___x_5843_, 0);
v_isSharedCheck_5896_ = !lean_is_exclusive(v___x_5843_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5846_ = v___x_5843_;
v_isShared_5847_ = v_isSharedCheck_5896_;
goto v_resetjp_5845_;
}
else
{
lean_inc(v_a_5844_);
lean_dec(v___x_5843_);
v___x_5846_ = lean_box(0);
v_isShared_5847_ = v_isSharedCheck_5896_;
goto v_resetjp_5845_;
}
v_resetjp_5845_:
{
lean_object* v___x_5848_; 
v___x_5848_ = lean_box(0);
if (lean_obj_tag(v_a_5844_) == 1)
{
lean_object* v___x_5849_; lean_object* v___x_5851_; 
lean_dec_ref(v___x_5818_);
lean_dec_ref(v_info_5817_);
lean_dec(v_goal_5816_);
lean_dec_ref(v_scope_5815_);
v___x_5849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5849_, 0, v_a_5844_);
lean_ctor_set(v___x_5849_, 1, v___x_5848_);
if (v_isShared_5847_ == 0)
{
lean_ctor_set(v___x_5846_, 0, v___x_5849_);
v___x_5851_ = v___x_5846_;
goto v_reusejp_5850_;
}
else
{
lean_object* v_reuseFailAlloc_5852_; 
v_reuseFailAlloc_5852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5852_, 0, v___x_5849_);
v___x_5851_ = v_reuseFailAlloc_5852_;
goto v_reusejp_5850_;
}
v_reusejp_5850_:
{
return v___x_5851_;
}
}
else
{
lean_object* v_options_5853_; lean_object* v_inheritedTraceOptions_5854_; uint8_t v_hasTrace_5855_; lean_object* v___x_5856_; 
lean_del_object(v___x_5846_);
lean_dec(v_a_5844_);
v_options_5853_ = lean_ctor_get(v___y_5832_, 2);
v_inheritedTraceOptions_5854_ = lean_ctor_get(v___y_5832_, 13);
v_hasTrace_5855_ = lean_ctor_get_uint8(v_options_5853_, sizeof(void*)*1);
v___x_5856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0));
if (v_hasTrace_5855_ == 0)
{
v_a_5836_ = v___x_5856_;
goto v___jp_5835_;
}
else
{
lean_object* v___x_5857_; lean_object* v___x_5858_; uint8_t v___x_5859_; 
v___x_5857_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5858_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5859_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5854_, v_options_5853_, v___x_5858_);
if (v___x_5859_ == 0)
{
v_a_5836_ = v___x_5856_;
goto v___jp_5835_;
}
else
{
lean_object* v_proof_5860_; lean_object* v___x_5861_; lean_object* v___y_5863_; 
v_proof_5860_ = lean_ctor_get(v_a_5842_, 1);
v___x_5861_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2);
switch(lean_obj_tag(v_proof_5860_))
{
case 0:
{
lean_object* v_declName_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; 
v_declName_5878_ = lean_ctor_get(v_proof_5860_, 0);
v___x_5879_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_5878_);
v___x_5880_ = l_Lean_MessageData_ofName(v_declName_5878_);
v___x_5881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5881_, 0, v___x_5879_);
lean_ctor_set(v___x_5881_, 1, v___x_5880_);
v___y_5863_ = v___x_5881_;
goto v___jp_5862_;
}
case 1:
{
lean_object* v_fvarId_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; 
v_fvarId_5882_ = lean_ctor_get(v_proof_5860_, 0);
v___x_5883_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_5882_);
v___x_5884_ = l_Lean_mkFVar(v_fvarId_5882_);
v___x_5885_ = l_Lean_MessageData_ofExpr(v___x_5884_);
v___x_5886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5886_, 0, v___x_5883_);
lean_ctor_set(v___x_5886_, 1, v___x_5885_);
v___y_5863_ = v___x_5886_;
goto v___jp_5862_;
}
default: 
{
lean_object* v_ref_5887_; lean_object* v_proof_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; 
v_ref_5887_ = lean_ctor_get(v_proof_5860_, 1);
v_proof_5888_ = lean_ctor_get(v_proof_5860_, 2);
v___x_5889_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_5887_);
v___x_5890_ = l_Lean_MessageData_ofSyntax(v_ref_5887_);
v___x_5891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5891_, 0, v___x_5889_);
lean_ctor_set(v___x_5891_, 1, v___x_5890_);
v___x_5892_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_5893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5893_, 0, v___x_5891_);
lean_ctor_set(v___x_5893_, 1, v___x_5892_);
lean_inc_ref(v_proof_5888_);
v___x_5894_ = l_Lean_MessageData_ofExpr(v_proof_5888_);
v___x_5895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5893_);
lean_ctor_set(v___x_5895_, 1, v___x_5894_);
v___y_5863_ = v___x_5895_;
goto v___jp_5862_;
}
}
v___jp_5862_:
{
lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; 
v___x_5864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5864_, 0, v___x_5861_);
lean_ctor_set(v___x_5864_, 1, v___y_5863_);
v___x_5865_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_5866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5866_, 0, v___x_5864_);
lean_ctor_set(v___x_5866_, 1, v___x_5865_);
lean_inc_ref(v___x_5818_);
v___x_5867_ = l_Lean_MessageData_ofExpr(v___x_5818_);
v___x_5868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5868_, 0, v___x_5866_);
lean_ctor_set(v___x_5868_, 1, v___x_5867_);
v___x_5869_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5857_, v___x_5868_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
if (lean_obj_tag(v___x_5869_) == 0)
{
lean_dec_ref_known(v___x_5869_, 1);
v_a_5836_ = v___x_5856_;
goto v___jp_5835_;
}
else
{
lean_object* v_a_5870_; lean_object* v___x_5872_; uint8_t v_isShared_5873_; uint8_t v_isSharedCheck_5877_; 
lean_dec_ref(v___x_5818_);
lean_dec_ref(v_info_5817_);
lean_dec(v_goal_5816_);
lean_dec_ref(v_scope_5815_);
v_a_5870_ = lean_ctor_get(v___x_5869_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v___x_5869_);
if (v_isSharedCheck_5877_ == 0)
{
v___x_5872_ = v___x_5869_;
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
else
{
lean_inc(v_a_5870_);
lean_dec(v___x_5869_);
v___x_5872_ = lean_box(0);
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
v_resetjp_5871_:
{
lean_object* v___x_5875_; 
if (v_isShared_5873_ == 0)
{
v___x_5875_ = v___x_5872_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5870_);
v___x_5875_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
return v___x_5875_;
}
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
lean_object* v_a_5897_; lean_object* v___x_5899_; uint8_t v_isShared_5900_; uint8_t v_isSharedCheck_5904_; 
lean_dec_ref(v___x_5818_);
lean_dec_ref(v_info_5817_);
lean_dec(v_goal_5816_);
lean_dec_ref(v_scope_5815_);
v_a_5897_ = lean_ctor_get(v___x_5843_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5843_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5899_ = v___x_5843_;
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
else
{
lean_inc(v_a_5897_);
lean_dec(v___x_5843_);
v___x_5899_ = lean_box(0);
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
v_resetjp_5898_:
{
lean_object* v___x_5902_; 
if (v_isShared_5900_ == 0)
{
v___x_5902_ = v___x_5899_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v_a_5897_);
v___x_5902_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
return v___x_5902_;
}
}
}
}
v___jp_5835_:
{
size_t v___x_5837_; size_t v___x_5838_; 
v___x_5837_ = ((size_t)1ULL);
v___x_5838_ = lean_usize_add(v_i_5821_, v___x_5837_);
lean_inc_ref(v_a_5836_);
v_i_5821_ = v___x_5838_;
v_b_5822_ = v_a_5836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___boxed(lean_object** _args){
lean_object* v_scope_5905_ = _args[0];
lean_object* v_goal_5906_ = _args[1];
lean_object* v_info_5907_ = _args[2];
lean_object* v___x_5908_ = _args[3];
lean_object* v_as_5909_ = _args[4];
lean_object* v_sz_5910_ = _args[5];
lean_object* v_i_5911_ = _args[6];
lean_object* v_b_5912_ = _args[7];
lean_object* v___y_5913_ = _args[8];
lean_object* v___y_5914_ = _args[9];
lean_object* v___y_5915_ = _args[10];
lean_object* v___y_5916_ = _args[11];
lean_object* v___y_5917_ = _args[12];
lean_object* v___y_5918_ = _args[13];
lean_object* v___y_5919_ = _args[14];
lean_object* v___y_5920_ = _args[15];
lean_object* v___y_5921_ = _args[16];
lean_object* v___y_5922_ = _args[17];
lean_object* v___y_5923_ = _args[18];
lean_object* v___y_5924_ = _args[19];
_start:
{
size_t v_sz_boxed_5925_; size_t v_i_boxed_5926_; lean_object* v_res_5927_; 
v_sz_boxed_5925_ = lean_unbox_usize(v_sz_5910_);
lean_dec(v_sz_5910_);
v_i_boxed_5926_ = lean_unbox_usize(v_i_5911_);
lean_dec(v_i_5911_);
v_res_5927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(v_scope_5905_, v_goal_5906_, v_info_5907_, v___x_5908_, v_as_5909_, v_sz_boxed_5925_, v_i_boxed_5926_, v_b_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_);
lean_dec(v___y_5923_);
lean_dec_ref(v___y_5922_);
lean_dec(v___y_5921_);
lean_dec_ref(v___y_5920_);
lean_dec(v___y_5919_);
lean_dec_ref(v___y_5918_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
lean_dec(v___y_5915_);
lean_dec(v___y_5914_);
lean_dec_ref(v___y_5913_);
lean_dec_ref(v_as_5909_);
return v_res_5927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0(lean_object* v_specs_5928_, lean_object* v___x_5929_, lean_object* v_scope_5930_, lean_object* v_goal_5931_, lean_object* v_info_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_, lean_object* v___y_5943_){
_start:
{
lean_object* v___x_5945_; 
lean_inc_ref(v___x_5929_);
v___x_5945_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_findSpecs(v_specs_5928_, v___x_5929_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_, v___y_5943_);
if (lean_obj_tag(v___x_5945_) == 0)
{
lean_object* v_a_5946_; lean_object* v___x_5947_; size_t v_sz_5948_; size_t v___x_5949_; lean_object* v___x_5950_; 
v_a_5946_ = lean_ctor_get(v___x_5945_, 0);
lean_inc(v_a_5946_);
lean_dec_ref_known(v___x_5945_, 1);
v___x_5947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0));
v_sz_5948_ = lean_array_size(v_a_5946_);
v___x_5949_ = ((size_t)0ULL);
lean_inc_ref(v___x_5929_);
lean_inc_ref(v_info_5932_);
v___x_5950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(v_scope_5930_, v_goal_5931_, v_info_5932_, v___x_5929_, v_a_5946_, v_sz_5948_, v___x_5949_, v___x_5947_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_, v___y_5943_);
if (lean_obj_tag(v___x_5950_) == 0)
{
lean_object* v_a_5951_; lean_object* v___x_5953_; uint8_t v_isShared_5954_; uint8_t v_isSharedCheck_5962_; 
v_a_5951_ = lean_ctor_get(v___x_5950_, 0);
v_isSharedCheck_5962_ = !lean_is_exclusive(v___x_5950_);
if (v_isSharedCheck_5962_ == 0)
{
v___x_5953_ = v___x_5950_;
v_isShared_5954_ = v_isSharedCheck_5962_;
goto v_resetjp_5952_;
}
else
{
lean_inc(v_a_5951_);
lean_dec(v___x_5950_);
v___x_5953_ = lean_box(0);
v_isShared_5954_ = v_isSharedCheck_5962_;
goto v_resetjp_5952_;
}
v_resetjp_5952_:
{
lean_object* v_fst_5955_; 
v_fst_5955_ = lean_ctor_get(v_a_5951_, 0);
lean_inc(v_fst_5955_);
lean_dec(v_a_5951_);
if (lean_obj_tag(v_fst_5955_) == 0)
{
lean_object* v___x_5956_; lean_object* v___x_5957_; 
lean_del_object(v___x_5953_);
v___x_5956_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v_info_5932_);
lean_dec_ref(v_info_5932_);
v___x_5957_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_5929_, v___x_5956_, v_a_5946_, v___y_5933_, v___y_5940_, v___y_5941_, v___y_5942_, v___y_5943_);
return v___x_5957_;
}
else
{
lean_object* v_val_5958_; lean_object* v___x_5960_; 
lean_dec(v_a_5946_);
lean_dec_ref(v_info_5932_);
lean_dec_ref(v___x_5929_);
v_val_5958_ = lean_ctor_get(v_fst_5955_, 0);
lean_inc(v_val_5958_);
lean_dec_ref_known(v_fst_5955_, 1);
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 0, v_val_5958_);
v___x_5960_ = v___x_5953_;
goto v_reusejp_5959_;
}
else
{
lean_object* v_reuseFailAlloc_5961_; 
v_reuseFailAlloc_5961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5961_, 0, v_val_5958_);
v___x_5960_ = v_reuseFailAlloc_5961_;
goto v_reusejp_5959_;
}
v_reusejp_5959_:
{
return v___x_5960_;
}
}
}
}
else
{
lean_object* v_a_5963_; lean_object* v___x_5965_; uint8_t v_isShared_5966_; uint8_t v_isSharedCheck_5970_; 
lean_dec(v_a_5946_);
lean_dec_ref(v_info_5932_);
lean_dec_ref(v___x_5929_);
v_a_5963_ = lean_ctor_get(v___x_5950_, 0);
v_isSharedCheck_5970_ = !lean_is_exclusive(v___x_5950_);
if (v_isSharedCheck_5970_ == 0)
{
v___x_5965_ = v___x_5950_;
v_isShared_5966_ = v_isSharedCheck_5970_;
goto v_resetjp_5964_;
}
else
{
lean_inc(v_a_5963_);
lean_dec(v___x_5950_);
v___x_5965_ = lean_box(0);
v_isShared_5966_ = v_isSharedCheck_5970_;
goto v_resetjp_5964_;
}
v_resetjp_5964_:
{
lean_object* v___x_5968_; 
if (v_isShared_5966_ == 0)
{
v___x_5968_ = v___x_5965_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5969_; 
v_reuseFailAlloc_5969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_a_5963_);
v___x_5968_ = v_reuseFailAlloc_5969_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
return v___x_5968_;
}
}
}
}
else
{
lean_object* v_a_5971_; lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_5978_; 
lean_dec_ref(v_info_5932_);
lean_dec(v_goal_5931_);
lean_dec_ref(v_scope_5930_);
lean_dec_ref(v___x_5929_);
v_a_5971_ = lean_ctor_get(v___x_5945_, 0);
v_isSharedCheck_5978_ = !lean_is_exclusive(v___x_5945_);
if (v_isSharedCheck_5978_ == 0)
{
v___x_5973_ = v___x_5945_;
v_isShared_5974_ = v_isSharedCheck_5978_;
goto v_resetjp_5972_;
}
else
{
lean_inc(v_a_5971_);
lean_dec(v___x_5945_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_5978_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v___x_5976_; 
if (v_isShared_5974_ == 0)
{
v___x_5976_ = v___x_5973_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5977_; 
v_reuseFailAlloc_5977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5977_, 0, v_a_5971_);
v___x_5976_ = v_reuseFailAlloc_5977_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
return v___x_5976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0___boxed(lean_object** _args){
lean_object* v_specs_5979_ = _args[0];
lean_object* v___x_5980_ = _args[1];
lean_object* v_scope_5981_ = _args[2];
lean_object* v_goal_5982_ = _args[3];
lean_object* v_info_5983_ = _args[4];
lean_object* v___y_5984_ = _args[5];
lean_object* v___y_5985_ = _args[6];
lean_object* v___y_5986_ = _args[7];
lean_object* v___y_5987_ = _args[8];
lean_object* v___y_5988_ = _args[9];
lean_object* v___y_5989_ = _args[10];
lean_object* v___y_5990_ = _args[11];
lean_object* v___y_5991_ = _args[12];
lean_object* v___y_5992_ = _args[13];
lean_object* v___y_5993_ = _args[14];
lean_object* v___y_5994_ = _args[15];
lean_object* v___y_5995_ = _args[16];
_start:
{
lean_object* v_res_5996_; 
v_res_5996_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0(v_specs_5979_, v___x_5980_, v_scope_5981_, v_goal_5982_, v_info_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_);
lean_dec(v___y_5994_);
lean_dec_ref(v___y_5993_);
lean_dec(v___y_5992_);
lean_dec_ref(v___y_5991_);
lean_dec(v___y_5990_);
lean_dec_ref(v___y_5989_);
lean_dec(v___y_5988_);
lean_dec_ref(v___y_5987_);
lean_dec(v___y_5986_);
lean_dec(v___y_5985_);
lean_dec_ref(v___y_5984_);
lean_dec_ref(v_specs_5979_);
return v_res_5996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(lean_object* v_scope_5997_, lean_object* v_goal_5998_, lean_object* v_info_5999_, lean_object* v_a_6000_, lean_object* v_a_6001_, lean_object* v_a_6002_, lean_object* v_a_6003_, lean_object* v_a_6004_, lean_object* v_a_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_){
_start:
{
lean_object* v_specs_6012_; lean_object* v___x_6013_; lean_object* v___f_6014_; lean_object* v___x_6015_; 
v_specs_6012_ = lean_ctor_get(v_scope_5997_, 0);
lean_inc_ref(v_specs_6012_);
v___x_6013_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5999_);
lean_inc(v_goal_5998_);
v___f_6014_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0___boxed), 17, 5);
lean_closure_set(v___f_6014_, 0, v_specs_6012_);
lean_closure_set(v___f_6014_, 1, v___x_6013_);
lean_closure_set(v___f_6014_, 2, v_scope_5997_);
lean_closure_set(v___f_6014_, 3, v_goal_5998_);
lean_closure_set(v___f_6014_, 4, v_info_5999_);
v___x_6015_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_5998_, v___f_6014_, v_a_6000_, v_a_6001_, v_a_6002_, v_a_6003_, v_a_6004_, v_a_6005_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_, v_a_6010_);
return v___x_6015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___boxed(lean_object* v_scope_6016_, lean_object* v_goal_6017_, lean_object* v_info_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_, lean_object* v_a_6025_, lean_object* v_a_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_){
_start:
{
lean_object* v_res_6031_; 
v_res_6031_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(v_scope_6016_, v_goal_6017_, v_info_6018_, v_a_6019_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_, v_a_6024_, v_a_6025_, v_a_6026_, v_a_6027_, v_a_6028_, v_a_6029_);
lean_dec(v_a_6029_);
lean_dec_ref(v_a_6028_);
lean_dec(v_a_6027_);
lean_dec_ref(v_a_6026_);
lean_dec(v_a_6025_);
lean_dec_ref(v_a_6024_);
lean_dec(v_a_6023_);
lean_dec_ref(v_a_6022_);
lean_dec(v_a_6021_);
lean_dec(v_a_6020_);
lean_dec_ref(v_a_6019_);
return v_res_6031_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6033_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__0));
v___x_6034_ = l_Lean_stringToMessageData(v___x_6033_);
return v___x_6034_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3(void){
_start:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; 
v___x_6036_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2));
v___x_6037_ = l_Lean_stringToMessageData(v___x_6036_);
return v___x_6037_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5(void){
_start:
{
lean_object* v___x_6039_; lean_object* v___x_6040_; 
v___x_6039_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4));
v___x_6040_ = l_Lean_stringToMessageData(v___x_6039_);
return v___x_6040_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7(void){
_start:
{
lean_object* v___x_6042_; lean_object* v___x_6043_; 
v___x_6042_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__6));
v___x_6043_ = l_Lean_stringToMessageData(v___x_6042_);
return v___x_6043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0(lean_object* v_goal_6046_, lean_object* v_scope_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_, lean_object* v___y_6058_){
_start:
{
lean_object* v_gs_6061_; lean_object* v_g_6065_; lean_object* v___y_6071_; lean_object* v___y_6072_; lean_object* v___y_6077_; lean_object* v_g_6078_; lean_object* v___y_6084_; lean_object* v_gs_6085_; lean_object* v___y_6089_; lean_object* v_g_6090_; lean_object* v___y_6091_; lean_object* v___y_6113_; lean_object* v___y_6114_; lean_object* v___y_6115_; lean_object* v___y_6116_; lean_object* v___y_6117_; lean_object* v___y_6118_; lean_object* v___y_6119_; lean_object* v___y_6120_; lean_object* v___y_6121_; lean_object* v___y_6122_; lean_object* v___y_6123_; lean_object* v___y_6124_; lean_object* v___y_6125_; lean_object* v___y_6137_; lean_object* v___y_6138_; lean_object* v___y_6139_; lean_object* v___y_6140_; lean_object* v___y_6141_; lean_object* v___y_6142_; lean_object* v___y_6143_; lean_object* v___y_6144_; lean_object* v___y_6145_; lean_object* v___y_6146_; lean_object* v___y_6147_; lean_object* v___y_6148_; lean_object* v___y_6149_; lean_object* v___y_6150_; lean_object* v___y_6151_; lean_object* v___x_6275_; 
v___x_6275_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v___y_6049_);
if (lean_obj_tag(v___x_6275_) == 0)
{
lean_object* v_a_6276_; lean_object* v___x_6278_; uint8_t v_isShared_6279_; uint8_t v_isSharedCheck_6540_; 
v_a_6276_ = lean_ctor_get(v___x_6275_, 0);
v_isSharedCheck_6540_ = !lean_is_exclusive(v___x_6275_);
if (v_isSharedCheck_6540_ == 0)
{
v___x_6278_ = v___x_6275_;
v_isShared_6279_ = v_isSharedCheck_6540_;
goto v_resetjp_6277_;
}
else
{
lean_inc(v_a_6276_);
lean_dec(v___x_6275_);
v___x_6278_ = lean_box(0);
v_isShared_6279_ = v_isSharedCheck_6540_;
goto v_resetjp_6277_;
}
v_resetjp_6277_:
{
uint8_t v___x_6280_; 
v___x_6280_ = lean_unbox(v_a_6276_);
lean_dec(v_a_6276_);
if (v___x_6280_ == 0)
{
lean_object* v___x_6281_; 
lean_del_object(v___x_6278_);
lean_inc(v_goal_6046_);
v___x_6281_ = l_Lean_MVarId_getType(v_goal_6046_, v___y_6055_, v___y_6056_, v___y_6057_, v___y_6058_);
if (lean_obj_tag(v___x_6281_) == 0)
{
lean_object* v_a_6282_; lean_object* v___x_6284_; uint8_t v_isShared_6285_; uint8_t v_isSharedCheck_6527_; 
v_a_6282_ = lean_ctor_get(v___x_6281_, 0);
v_isSharedCheck_6527_ = !lean_is_exclusive(v___x_6281_);
if (v_isSharedCheck_6527_ == 0)
{
v___x_6284_ = v___x_6281_;
v_isShared_6285_ = v_isSharedCheck_6527_;
goto v_resetjp_6283_;
}
else
{
lean_inc(v_a_6282_);
lean_dec(v___x_6281_);
v___x_6284_ = lean_box(0);
v_isShared_6285_ = v_isSharedCheck_6527_;
goto v_resetjp_6283_;
}
v_resetjp_6283_:
{
lean_object* v_options_6292_; lean_object* v_inheritedTraceOptions_6293_; uint8_t v_hasTrace_6294_; lean_object* v___x_6295_; lean_object* v___y_6297_; lean_object* v___y_6298_; lean_object* v___y_6299_; lean_object* v___y_6300_; lean_object* v___y_6301_; lean_object* v___y_6302_; lean_object* v___y_6303_; lean_object* v___y_6304_; lean_object* v___y_6305_; lean_object* v___y_6306_; lean_object* v___y_6307_; 
v_options_6292_ = lean_ctor_get(v___y_6057_, 2);
v_inheritedTraceOptions_6293_ = lean_ctor_get(v___y_6057_, 13);
v_hasTrace_6294_ = lean_ctor_get_uint8(v_options_6292_, sizeof(void*)*1);
v___x_6295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_6294_ == 0)
{
v___y_6297_ = v___y_6048_;
v___y_6298_ = v___y_6049_;
v___y_6299_ = v___y_6050_;
v___y_6300_ = v___y_6051_;
v___y_6301_ = v___y_6052_;
v___y_6302_ = v___y_6053_;
v___y_6303_ = v___y_6054_;
v___y_6304_ = v___y_6055_;
v___y_6305_ = v___y_6056_;
v___y_6306_ = v___y_6057_;
v___y_6307_ = v___y_6058_;
goto v___jp_6296_;
}
else
{
lean_object* v___x_6513_; uint8_t v___x_6514_; 
v___x_6513_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_6514_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6293_, v_options_6292_, v___x_6513_);
if (v___x_6514_ == 0)
{
v___y_6297_ = v___y_6048_;
v___y_6298_ = v___y_6049_;
v___y_6299_ = v___y_6050_;
v___y_6300_ = v___y_6051_;
v___y_6301_ = v___y_6052_;
v___y_6302_ = v___y_6053_;
v___y_6303_ = v___y_6054_;
v___y_6304_ = v___y_6055_;
v___y_6305_ = v___y_6056_;
v___y_6306_ = v___y_6057_;
v___y_6307_ = v___y_6058_;
goto v___jp_6296_;
}
else
{
lean_object* v___x_6515_; lean_object* v___x_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; 
v___x_6515_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7);
lean_inc(v_a_6282_);
v___x_6516_ = l_Lean_MessageData_ofExpr(v_a_6282_);
v___x_6517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6517_, 0, v___x_6515_);
lean_ctor_set(v___x_6517_, 1, v___x_6516_);
v___x_6518_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_6295_, v___x_6517_, v___y_6055_, v___y_6056_, v___y_6057_, v___y_6058_);
if (lean_obj_tag(v___x_6518_) == 0)
{
lean_dec_ref_known(v___x_6518_, 1);
v___y_6297_ = v___y_6048_;
v___y_6298_ = v___y_6049_;
v___y_6299_ = v___y_6050_;
v___y_6300_ = v___y_6051_;
v___y_6301_ = v___y_6052_;
v___y_6302_ = v___y_6053_;
v___y_6303_ = v___y_6054_;
v___y_6304_ = v___y_6055_;
v___y_6305_ = v___y_6056_;
v___y_6306_ = v___y_6057_;
v___y_6307_ = v___y_6058_;
goto v___jp_6296_;
}
else
{
lean_object* v_a_6519_; lean_object* v___x_6521_; uint8_t v_isShared_6522_; uint8_t v_isSharedCheck_6526_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6519_ = lean_ctor_get(v___x_6518_, 0);
v_isSharedCheck_6526_ = !lean_is_exclusive(v___x_6518_);
if (v_isSharedCheck_6526_ == 0)
{
v___x_6521_ = v___x_6518_;
v_isShared_6522_ = v_isSharedCheck_6526_;
goto v_resetjp_6520_;
}
else
{
lean_inc(v_a_6519_);
lean_dec(v___x_6518_);
v___x_6521_ = lean_box(0);
v_isShared_6522_ = v_isSharedCheck_6526_;
goto v_resetjp_6520_;
}
v_resetjp_6520_:
{
lean_object* v___x_6524_; 
if (v_isShared_6522_ == 0)
{
v___x_6524_ = v___x_6521_;
goto v_reusejp_6523_;
}
else
{
lean_object* v_reuseFailAlloc_6525_; 
v_reuseFailAlloc_6525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6525_, 0, v_a_6519_);
v___x_6524_ = v_reuseFailAlloc_6525_;
goto v_reusejp_6523_;
}
v_reusejp_6523_:
{
return v___x_6524_;
}
}
}
}
}
v___jp_6286_:
{
lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6290_; 
v___x_6287_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6287_, 0, v_a_6282_);
v___x_6288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6288_, 0, v___x_6287_);
if (v_isShared_6285_ == 0)
{
lean_ctor_set(v___x_6284_, 0, v___x_6288_);
v___x_6290_ = v___x_6284_;
goto v_reusejp_6289_;
}
else
{
lean_object* v_reuseFailAlloc_6291_; 
v_reuseFailAlloc_6291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6291_, 0, v___x_6288_);
v___x_6290_ = v_reuseFailAlloc_6291_;
goto v_reusejp_6289_;
}
v_reusejp_6289_:
{
return v___x_6290_;
}
}
v___jp_6296_:
{
lean_object* v___x_6308_; 
lean_inc(v_goal_6046_);
v___x_6308_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg(v_goal_6046_, v_a_6282_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6308_) == 0)
{
lean_object* v_a_6309_; 
v_a_6309_ = lean_ctor_get(v___x_6308_, 0);
lean_inc(v_a_6309_);
lean_dec_ref_known(v___x_6308_, 1);
if (lean_obj_tag(v_a_6309_) == 1)
{
lean_object* v_val_6310_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec(v_goal_6046_);
v_val_6310_ = lean_ctor_get(v_a_6309_, 0);
lean_inc(v_val_6310_);
lean_dec_ref_known(v_a_6309_, 1);
v_g_6065_ = v_val_6310_;
goto v___jp_6064_;
}
else
{
lean_object* v___x_6311_; 
lean_dec(v_a_6309_);
lean_inc(v_goal_6046_);
v___x_6311_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f(v_goal_6046_, v_a_6282_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6311_) == 0)
{
lean_object* v_a_6312_; 
v_a_6312_ = lean_ctor_get(v___x_6311_, 0);
lean_inc(v_a_6312_);
lean_dec_ref_known(v___x_6311_, 1);
if (lean_obj_tag(v_a_6312_) == 1)
{
lean_object* v_val_6313_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec(v_goal_6046_);
v_val_6313_ = lean_ctor_get(v_a_6312_, 0);
lean_inc(v_val_6313_);
lean_dec_ref_known(v_a_6312_, 1);
v_gs_6061_ = v_val_6313_;
goto v___jp_6060_;
}
else
{
lean_object* v___x_6314_; 
lean_dec(v_a_6312_);
lean_inc(v_a_6282_);
lean_inc(v_goal_6046_);
v___x_6314_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f(v_goal_6046_, v_a_6282_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6314_) == 0)
{
lean_object* v_a_6315_; 
v_a_6315_ = lean_ctor_get(v___x_6314_, 0);
lean_inc(v_a_6315_);
lean_dec_ref_known(v___x_6314_, 1);
if (lean_obj_tag(v_a_6315_) == 1)
{
lean_object* v_val_6316_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec(v_goal_6046_);
v_val_6316_ = lean_ctor_get(v_a_6315_, 0);
lean_inc(v_val_6316_);
lean_dec_ref_known(v_a_6315_, 1);
v_g_6065_ = v_val_6316_;
goto v___jp_6064_;
}
else
{
lean_object* v___x_6317_; 
lean_dec(v_a_6315_);
lean_inc(v_goal_6046_);
v___x_6317_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f(v_goal_6046_, v_a_6282_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6317_) == 0)
{
lean_object* v_a_6318_; 
v_a_6318_ = lean_ctor_get(v___x_6317_, 0);
lean_inc(v_a_6318_);
lean_dec_ref_known(v___x_6317_, 1);
if (lean_obj_tag(v_a_6318_) == 1)
{
lean_object* v_val_6319_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec(v_goal_6046_);
v_val_6319_ = lean_ctor_get(v_a_6318_, 0);
lean_inc(v_val_6319_);
lean_dec_ref_known(v_a_6318_, 1);
v_g_6065_ = v_val_6319_;
goto v___jp_6064_;
}
else
{
lean_object* v___x_6320_; 
lean_dec(v_a_6318_);
lean_inc(v_a_6282_);
lean_inc(v_goal_6046_);
v___x_6320_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f(v_goal_6046_, v_a_6282_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6320_) == 0)
{
lean_object* v_a_6321_; 
v_a_6321_ = lean_ctor_get(v___x_6320_, 0);
lean_inc(v_a_6321_);
lean_dec_ref_known(v___x_6320_, 1);
if (lean_obj_tag(v_a_6321_) == 1)
{
lean_object* v_val_6322_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec(v_goal_6046_);
v_val_6322_ = lean_ctor_get(v_a_6321_, 0);
lean_inc(v_val_6322_);
lean_dec_ref_known(v_a_6321_, 1);
v_g_6065_ = v_val_6322_;
goto v___jp_6064_;
}
else
{
lean_object* v___x_6323_; 
lean_dec(v_a_6321_);
lean_inc(v_a_6282_);
lean_inc(v_goal_6046_);
lean_inc_ref(v_scope_6047_);
v___x_6323_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f(v_scope_6047_, v_goal_6046_, v_a_6282_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6323_) == 0)
{
lean_object* v_a_6324_; 
v_a_6324_ = lean_ctor_get(v___x_6323_, 0);
lean_inc(v_a_6324_);
lean_dec_ref_known(v___x_6323_, 1);
if (lean_obj_tag(v_a_6324_) == 1)
{
lean_object* v_val_6325_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec(v_goal_6046_);
v_val_6325_ = lean_ctor_get(v_a_6324_, 0);
lean_inc(v_val_6325_);
lean_dec_ref_known(v_a_6324_, 1);
v_gs_6061_ = v_val_6325_;
goto v___jp_6060_;
}
else
{
lean_object* v___x_6326_; 
lean_dec(v_a_6324_);
lean_inc(v_a_6282_);
lean_inc(v_goal_6046_);
v___x_6326_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(v_goal_6046_, v_a_6282_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6326_) == 0)
{
lean_object* v_a_6327_; 
v_a_6327_ = lean_ctor_get(v___x_6326_, 0);
lean_inc(v_a_6327_);
lean_dec_ref_known(v___x_6326_, 1);
if (lean_obj_tag(v_a_6327_) == 1)
{
lean_object* v_val_6328_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec(v_goal_6046_);
v_val_6328_ = lean_ctor_get(v_a_6327_, 0);
lean_inc(v_val_6328_);
lean_dec_ref_known(v_a_6327_, 1);
v_g_6065_ = v_val_6328_;
goto v___jp_6064_;
}
else
{
lean_object* v___x_6329_; uint8_t v___x_6330_; 
lean_dec(v_a_6327_);
lean_inc(v_a_6282_);
v___x_6329_ = l_Lean_Expr_cleanupAnnotations(v_a_6282_);
v___x_6330_ = l_Lean_Expr_isApp(v___x_6329_);
if (v___x_6330_ == 0)
{
lean_dec_ref(v___x_6329_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
goto v___jp_6286_;
}
else
{
lean_object* v_arg_6331_; lean_object* v___x_6332_; uint8_t v___x_6333_; 
v_arg_6331_ = lean_ctor_get(v___x_6329_, 1);
lean_inc_ref(v_arg_6331_);
v___x_6332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6329_);
v___x_6333_ = l_Lean_Expr_isApp(v___x_6332_);
if (v___x_6333_ == 0)
{
lean_dec_ref(v___x_6332_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
goto v___jp_6286_;
}
else
{
lean_object* v_arg_6334_; lean_object* v___x_6335_; uint8_t v___x_6336_; 
v_arg_6334_ = lean_ctor_get(v___x_6332_, 1);
lean_inc_ref(v_arg_6334_);
v___x_6335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6332_);
v___x_6336_ = l_Lean_Expr_isApp(v___x_6335_);
if (v___x_6336_ == 0)
{
lean_dec_ref(v___x_6335_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
goto v___jp_6286_;
}
else
{
lean_object* v_arg_6337_; lean_object* v___x_6338_; uint8_t v___x_6339_; 
v_arg_6337_ = lean_ctor_get(v___x_6335_, 1);
lean_inc_ref(v_arg_6337_);
v___x_6338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6335_);
v___x_6339_ = l_Lean_Expr_isApp(v___x_6338_);
if (v___x_6339_ == 0)
{
lean_dec_ref(v___x_6338_);
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
goto v___jp_6286_;
}
else
{
lean_object* v_arg_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; uint8_t v___x_6343_; 
v_arg_6340_ = lean_ctor_get(v___x_6338_, 1);
lean_inc_ref(v_arg_6340_);
v___x_6341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6338_);
v___x_6342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10));
v___x_6343_ = l_Lean_Expr_isConstOf(v___x_6341_, v___x_6342_);
lean_dec_ref(v___x_6341_);
if (v___x_6343_ == 0)
{
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
goto v___jp_6286_;
}
else
{
lean_object* v___x_6344_; 
lean_del_object(v___x_6284_);
lean_inc(v_goal_6046_);
v___x_6344_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(v_goal_6046_, v___y_6297_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6344_) == 0)
{
lean_object* v_a_6345_; 
v_a_6345_ = lean_ctor_get(v___x_6344_, 0);
lean_inc(v_a_6345_);
lean_dec_ref_known(v___x_6344_, 1);
if (lean_obj_tag(v_a_6345_) == 1)
{
lean_object* v_val_6346_; 
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_a_6282_);
lean_dec(v_goal_6046_);
v_val_6346_ = lean_ctor_get(v_a_6345_, 0);
lean_inc(v_val_6346_);
lean_dec_ref_known(v_a_6345_, 1);
v_gs_6061_ = v_val_6346_;
goto v___jp_6060_;
}
else
{
lean_object* v___x_6347_; 
lean_dec(v_a_6345_);
lean_inc(v_a_6282_);
lean_inc_ref(v_arg_6334_);
lean_inc(v_goal_6046_);
lean_inc_ref(v_scope_6047_);
v___x_6347_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(v_scope_6047_, v_goal_6046_, v_arg_6340_, v_arg_6334_, v_a_6282_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6347_) == 0)
{
lean_object* v_a_6348_; lean_object* v___x_6350_; uint8_t v_isShared_6351_; uint8_t v_isSharedCheck_6440_; 
v_a_6348_ = lean_ctor_get(v___x_6347_, 0);
v_isSharedCheck_6440_ = !lean_is_exclusive(v___x_6347_);
if (v_isSharedCheck_6440_ == 0)
{
v___x_6350_ = v___x_6347_;
v_isShared_6351_ = v_isSharedCheck_6440_;
goto v_resetjp_6349_;
}
else
{
lean_inc(v_a_6348_);
lean_dec(v___x_6347_);
v___x_6350_ = lean_box(0);
v_isShared_6351_ = v_isSharedCheck_6440_;
goto v_resetjp_6349_;
}
v_resetjp_6349_:
{
if (lean_obj_tag(v_a_6348_) == 1)
{
lean_object* v_val_6352_; lean_object* v_fst_6353_; lean_object* v_snd_6354_; lean_object* v___x_6356_; uint8_t v_isShared_6357_; uint8_t v_isSharedCheck_6364_; 
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_a_6282_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_val_6352_ = lean_ctor_get(v_a_6348_, 0);
lean_inc(v_val_6352_);
lean_dec_ref_known(v_a_6348_, 1);
v_fst_6353_ = lean_ctor_get(v_val_6352_, 0);
v_snd_6354_ = lean_ctor_get(v_val_6352_, 1);
v_isSharedCheck_6364_ = !lean_is_exclusive(v_val_6352_);
if (v_isSharedCheck_6364_ == 0)
{
v___x_6356_ = v_val_6352_;
v_isShared_6357_ = v_isSharedCheck_6364_;
goto v_resetjp_6355_;
}
else
{
lean_inc(v_snd_6354_);
lean_inc(v_fst_6353_);
lean_dec(v_val_6352_);
v___x_6356_ = lean_box(0);
v_isShared_6357_ = v_isSharedCheck_6364_;
goto v_resetjp_6355_;
}
v_resetjp_6355_:
{
lean_object* v___x_6359_; 
if (v_isShared_6357_ == 0)
{
v___x_6359_ = v___x_6356_;
goto v_reusejp_6358_;
}
else
{
lean_object* v_reuseFailAlloc_6363_; 
v_reuseFailAlloc_6363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6363_, 0, v_fst_6353_);
lean_ctor_set(v_reuseFailAlloc_6363_, 1, v_snd_6354_);
v___x_6359_ = v_reuseFailAlloc_6363_;
goto v_reusejp_6358_;
}
v_reusejp_6358_:
{
lean_object* v___x_6361_; 
if (v_isShared_6351_ == 0)
{
lean_ctor_set(v___x_6350_, 0, v___x_6359_);
v___x_6361_ = v___x_6350_;
goto v_reusejp_6360_;
}
else
{
lean_object* v_reuseFailAlloc_6362_; 
v_reuseFailAlloc_6362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6362_, 0, v___x_6359_);
v___x_6361_ = v_reuseFailAlloc_6362_;
goto v_reusejp_6360_;
}
v_reusejp_6360_:
{
return v___x_6361_;
}
}
}
}
else
{
lean_object* v___x_6365_; 
lean_del_object(v___x_6350_);
lean_dec(v_a_6348_);
lean_inc(v_goal_6046_);
v___x_6365_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(v_scope_6047_, v_goal_6046_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6365_) == 0)
{
lean_object* v_a_6366_; lean_object* v___x_6367_; 
v_a_6366_ = lean_ctor_get(v___x_6365_, 0);
lean_inc(v_a_6366_);
lean_dec_ref_known(v___x_6365_, 1);
lean_inc_ref(v_arg_6331_);
lean_inc_ref(v_arg_6334_);
lean_inc_ref(v_arg_6340_);
lean_inc(v_goal_6046_);
v___x_6367_ = l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f(v_goal_6046_, v_a_6282_, v_arg_6340_, v_arg_6337_, v_arg_6334_, v_arg_6331_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6367_) == 0)
{
lean_object* v_a_6368_; 
v_a_6368_ = lean_ctor_get(v___x_6367_, 0);
lean_inc(v_a_6368_);
lean_dec_ref_known(v___x_6367_, 1);
if (lean_obj_tag(v_a_6368_) == 1)
{
lean_object* v_val_6369_; 
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_goal_6046_);
v_val_6369_ = lean_ctor_get(v_a_6368_, 0);
lean_inc(v_val_6369_);
lean_dec_ref_known(v_a_6368_, 1);
v___y_6077_ = v_a_6366_;
v_g_6078_ = v_val_6369_;
goto v___jp_6076_;
}
else
{
lean_object* v___x_6370_; 
lean_dec(v_a_6368_);
lean_inc_ref(v_arg_6331_);
lean_inc(v_goal_6046_);
v___x_6370_ = l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(v_goal_6046_, v_arg_6331_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6370_) == 0)
{
lean_object* v_a_6371_; 
v_a_6371_ = lean_ctor_get(v___x_6370_, 0);
lean_inc(v_a_6371_);
lean_dec_ref_known(v___x_6370_, 1);
if (lean_obj_tag(v_a_6371_) == 1)
{
lean_object* v_val_6372_; 
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_goal_6046_);
v_val_6372_ = lean_ctor_get(v_a_6371_, 0);
lean_inc(v_val_6372_);
lean_dec_ref_known(v_a_6371_, 1);
v___y_6084_ = v_a_6366_;
v_gs_6085_ = v_val_6372_;
goto v___jp_6083_;
}
else
{
lean_object* v___x_6373_; 
lean_dec(v_a_6371_);
lean_inc(v_goal_6046_);
v___x_6373_ = l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(v_goal_6046_, v_arg_6331_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6373_) == 0)
{
lean_object* v_a_6374_; 
v_a_6374_ = lean_ctor_get(v___x_6373_, 0);
lean_inc(v_a_6374_);
lean_dec_ref_known(v___x_6373_, 1);
if (lean_obj_tag(v_a_6374_) == 1)
{
lean_object* v_val_6375_; 
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_goal_6046_);
v_val_6375_ = lean_ctor_get(v_a_6374_, 0);
lean_inc(v_val_6375_);
lean_dec_ref_known(v_a_6374_, 1);
v___y_6084_ = v_a_6366_;
v_gs_6085_ = v_val_6375_;
goto v___jp_6083_;
}
else
{
lean_object* v___x_6376_; 
lean_dec(v_a_6374_);
lean_inc_ref(v_arg_6331_);
lean_inc_ref(v_arg_6334_);
lean_inc(v_goal_6046_);
lean_inc(v_a_6366_);
v___x_6376_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f(v_a_6366_, v_goal_6046_, v_arg_6340_, v_arg_6334_, v_arg_6331_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
lean_dec_ref(v_arg_6340_);
if (lean_obj_tag(v___x_6376_) == 0)
{
lean_object* v_a_6377_; 
v_a_6377_ = lean_ctor_get(v___x_6376_, 0);
lean_inc(v_a_6377_);
lean_dec_ref_known(v___x_6376_, 1);
if (lean_obj_tag(v_a_6377_) == 1)
{
lean_object* v_val_6378_; 
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_goal_6046_);
v_val_6378_ = lean_ctor_get(v_a_6377_, 0);
lean_inc(v_val_6378_);
lean_dec_ref_known(v_a_6377_, 1);
v___y_6084_ = v_a_6366_;
v_gs_6085_ = v_val_6378_;
goto v___jp_6083_;
}
else
{
lean_object* v___x_6379_; 
lean_dec(v_a_6377_);
lean_inc_ref(v_arg_6331_);
v___x_6379_ = l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(v_arg_6331_);
if (lean_obj_tag(v___x_6379_) == 1)
{
lean_object* v_options_6380_; uint8_t v_hasTrace_6381_; 
v_options_6380_ = lean_ctor_get(v___y_6306_, 2);
v_hasTrace_6381_ = lean_ctor_get_uint8(v_options_6380_, sizeof(void*)*1);
if (v_hasTrace_6381_ == 0)
{
lean_object* v_val_6382_; 
v_val_6382_ = lean_ctor_get(v___x_6379_, 0);
lean_inc(v_val_6382_);
lean_dec_ref_known(v___x_6379_, 1);
v___y_6137_ = v_arg_6334_;
v___y_6138_ = v_val_6382_;
v___y_6139_ = v_a_6366_;
v___y_6140_ = v_arg_6331_;
v___y_6141_ = v___y_6297_;
v___y_6142_ = v___y_6298_;
v___y_6143_ = v___y_6299_;
v___y_6144_ = v___y_6300_;
v___y_6145_ = v___y_6301_;
v___y_6146_ = v___y_6302_;
v___y_6147_ = v___y_6303_;
v___y_6148_ = v___y_6304_;
v___y_6149_ = v___y_6305_;
v___y_6150_ = v___y_6306_;
v___y_6151_ = v___y_6307_;
goto v___jp_6136_;
}
else
{
lean_object* v_val_6383_; lean_object* v_inheritedTraceOptions_6384_; lean_object* v___x_6385_; uint8_t v___x_6386_; 
v_val_6383_ = lean_ctor_get(v___x_6379_, 0);
lean_inc(v_val_6383_);
lean_dec_ref_known(v___x_6379_, 1);
v_inheritedTraceOptions_6384_ = lean_ctor_get(v___y_6306_, 13);
v___x_6385_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_6386_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6384_, v_options_6380_, v___x_6385_);
if (v___x_6386_ == 0)
{
v___y_6137_ = v_arg_6334_;
v___y_6138_ = v_val_6383_;
v___y_6139_ = v_a_6366_;
v___y_6140_ = v_arg_6331_;
v___y_6141_ = v___y_6297_;
v___y_6142_ = v___y_6298_;
v___y_6143_ = v___y_6299_;
v___y_6144_ = v___y_6300_;
v___y_6145_ = v___y_6301_;
v___y_6146_ = v___y_6302_;
v___y_6147_ = v___y_6303_;
v___y_6148_ = v___y_6304_;
v___y_6149_ = v___y_6305_;
v___y_6150_ = v___y_6306_;
v___y_6151_ = v___y_6307_;
goto v___jp_6136_;
}
else
{
lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; 
v___x_6387_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5);
v___x_6388_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_val_6383_);
v___x_6389_ = l_Lean_MessageData_ofExpr(v___x_6388_);
v___x_6390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6390_, 0, v___x_6387_);
lean_ctor_set(v___x_6390_, 1, v___x_6389_);
v___x_6391_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_6295_, v___x_6390_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
if (lean_obj_tag(v___x_6391_) == 0)
{
lean_dec_ref_known(v___x_6391_, 1);
v___y_6137_ = v_arg_6334_;
v___y_6138_ = v_val_6383_;
v___y_6139_ = v_a_6366_;
v___y_6140_ = v_arg_6331_;
v___y_6141_ = v___y_6297_;
v___y_6142_ = v___y_6298_;
v___y_6143_ = v___y_6299_;
v___y_6144_ = v___y_6300_;
v___y_6145_ = v___y_6301_;
v___y_6146_ = v___y_6302_;
v___y_6147_ = v___y_6303_;
v___y_6148_ = v___y_6304_;
v___y_6149_ = v___y_6305_;
v___y_6150_ = v___y_6306_;
v___y_6151_ = v___y_6307_;
goto v___jp_6136_;
}
else
{
lean_object* v_a_6392_; lean_object* v___x_6394_; uint8_t v_isShared_6395_; uint8_t v_isSharedCheck_6399_; 
lean_dec(v_val_6383_);
lean_dec(v_a_6366_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_goal_6046_);
v_a_6392_ = lean_ctor_get(v___x_6391_, 0);
v_isSharedCheck_6399_ = !lean_is_exclusive(v___x_6391_);
if (v_isSharedCheck_6399_ == 0)
{
v___x_6394_ = v___x_6391_;
v_isShared_6395_ = v_isSharedCheck_6399_;
goto v_resetjp_6393_;
}
else
{
lean_inc(v_a_6392_);
lean_dec(v___x_6391_);
v___x_6394_ = lean_box(0);
v_isShared_6395_ = v_isSharedCheck_6399_;
goto v_resetjp_6393_;
}
v_resetjp_6393_:
{
lean_object* v___x_6397_; 
if (v_isShared_6395_ == 0)
{
v___x_6397_ = v___x_6394_;
goto v_reusejp_6396_;
}
else
{
lean_object* v_reuseFailAlloc_6398_; 
v_reuseFailAlloc_6398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6398_, 0, v_a_6392_);
v___x_6397_ = v_reuseFailAlloc_6398_;
goto v_reusejp_6396_;
}
v_reusejp_6396_:
{
return v___x_6397_;
}
}
}
}
}
}
else
{
lean_dec(v___x_6379_);
lean_dec(v_a_6366_);
lean_dec(v_goal_6046_);
v___y_6071_ = v_arg_6334_;
v___y_6072_ = v_arg_6331_;
goto v___jp_6070_;
}
}
}
else
{
lean_object* v_a_6400_; lean_object* v___x_6402_; uint8_t v_isShared_6403_; uint8_t v_isSharedCheck_6407_; 
lean_dec(v_a_6366_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_goal_6046_);
v_a_6400_ = lean_ctor_get(v___x_6376_, 0);
v_isSharedCheck_6407_ = !lean_is_exclusive(v___x_6376_);
if (v_isSharedCheck_6407_ == 0)
{
v___x_6402_ = v___x_6376_;
v_isShared_6403_ = v_isSharedCheck_6407_;
goto v_resetjp_6401_;
}
else
{
lean_inc(v_a_6400_);
lean_dec(v___x_6376_);
v___x_6402_ = lean_box(0);
v_isShared_6403_ = v_isSharedCheck_6407_;
goto v_resetjp_6401_;
}
v_resetjp_6401_:
{
lean_object* v___x_6405_; 
if (v_isShared_6403_ == 0)
{
v___x_6405_ = v___x_6402_;
goto v_reusejp_6404_;
}
else
{
lean_object* v_reuseFailAlloc_6406_; 
v_reuseFailAlloc_6406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6406_, 0, v_a_6400_);
v___x_6405_ = v_reuseFailAlloc_6406_;
goto v_reusejp_6404_;
}
v_reusejp_6404_:
{
return v___x_6405_;
}
}
}
}
}
else
{
lean_object* v_a_6408_; lean_object* v___x_6410_; uint8_t v_isShared_6411_; uint8_t v_isSharedCheck_6415_; 
lean_dec(v_a_6366_);
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_goal_6046_);
v_a_6408_ = lean_ctor_get(v___x_6373_, 0);
v_isSharedCheck_6415_ = !lean_is_exclusive(v___x_6373_);
if (v_isSharedCheck_6415_ == 0)
{
v___x_6410_ = v___x_6373_;
v_isShared_6411_ = v_isSharedCheck_6415_;
goto v_resetjp_6409_;
}
else
{
lean_inc(v_a_6408_);
lean_dec(v___x_6373_);
v___x_6410_ = lean_box(0);
v_isShared_6411_ = v_isSharedCheck_6415_;
goto v_resetjp_6409_;
}
v_resetjp_6409_:
{
lean_object* v___x_6413_; 
if (v_isShared_6411_ == 0)
{
v___x_6413_ = v___x_6410_;
goto v_reusejp_6412_;
}
else
{
lean_object* v_reuseFailAlloc_6414_; 
v_reuseFailAlloc_6414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6414_, 0, v_a_6408_);
v___x_6413_ = v_reuseFailAlloc_6414_;
goto v_reusejp_6412_;
}
v_reusejp_6412_:
{
return v___x_6413_;
}
}
}
}
}
else
{
lean_object* v_a_6416_; lean_object* v___x_6418_; uint8_t v_isShared_6419_; uint8_t v_isSharedCheck_6423_; 
lean_dec(v_a_6366_);
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_goal_6046_);
v_a_6416_ = lean_ctor_get(v___x_6370_, 0);
v_isSharedCheck_6423_ = !lean_is_exclusive(v___x_6370_);
if (v_isSharedCheck_6423_ == 0)
{
v___x_6418_ = v___x_6370_;
v_isShared_6419_ = v_isSharedCheck_6423_;
goto v_resetjp_6417_;
}
else
{
lean_inc(v_a_6416_);
lean_dec(v___x_6370_);
v___x_6418_ = lean_box(0);
v_isShared_6419_ = v_isSharedCheck_6423_;
goto v_resetjp_6417_;
}
v_resetjp_6417_:
{
lean_object* v___x_6421_; 
if (v_isShared_6419_ == 0)
{
v___x_6421_ = v___x_6418_;
goto v_reusejp_6420_;
}
else
{
lean_object* v_reuseFailAlloc_6422_; 
v_reuseFailAlloc_6422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6422_, 0, v_a_6416_);
v___x_6421_ = v_reuseFailAlloc_6422_;
goto v_reusejp_6420_;
}
v_reusejp_6420_:
{
return v___x_6421_;
}
}
}
}
}
else
{
lean_object* v_a_6424_; lean_object* v___x_6426_; uint8_t v_isShared_6427_; uint8_t v_isSharedCheck_6431_; 
lean_dec(v_a_6366_);
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_goal_6046_);
v_a_6424_ = lean_ctor_get(v___x_6367_, 0);
v_isSharedCheck_6431_ = !lean_is_exclusive(v___x_6367_);
if (v_isSharedCheck_6431_ == 0)
{
v___x_6426_ = v___x_6367_;
v_isShared_6427_ = v_isSharedCheck_6431_;
goto v_resetjp_6425_;
}
else
{
lean_inc(v_a_6424_);
lean_dec(v___x_6367_);
v___x_6426_ = lean_box(0);
v_isShared_6427_ = v_isSharedCheck_6431_;
goto v_resetjp_6425_;
}
v_resetjp_6425_:
{
lean_object* v___x_6429_; 
if (v_isShared_6427_ == 0)
{
v___x_6429_ = v___x_6426_;
goto v_reusejp_6428_;
}
else
{
lean_object* v_reuseFailAlloc_6430_; 
v_reuseFailAlloc_6430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6430_, 0, v_a_6424_);
v___x_6429_ = v_reuseFailAlloc_6430_;
goto v_reusejp_6428_;
}
v_reusejp_6428_:
{
return v___x_6429_;
}
}
}
}
else
{
lean_object* v_a_6432_; lean_object* v___x_6434_; uint8_t v_isShared_6435_; uint8_t v_isSharedCheck_6439_; 
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_a_6282_);
lean_dec(v_goal_6046_);
v_a_6432_ = lean_ctor_get(v___x_6365_, 0);
v_isSharedCheck_6439_ = !lean_is_exclusive(v___x_6365_);
if (v_isSharedCheck_6439_ == 0)
{
v___x_6434_ = v___x_6365_;
v_isShared_6435_ = v_isSharedCheck_6439_;
goto v_resetjp_6433_;
}
else
{
lean_inc(v_a_6432_);
lean_dec(v___x_6365_);
v___x_6434_ = lean_box(0);
v_isShared_6435_ = v_isSharedCheck_6439_;
goto v_resetjp_6433_;
}
v_resetjp_6433_:
{
lean_object* v___x_6437_; 
if (v_isShared_6435_ == 0)
{
v___x_6437_ = v___x_6434_;
goto v_reusejp_6436_;
}
else
{
lean_object* v_reuseFailAlloc_6438_; 
v_reuseFailAlloc_6438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6438_, 0, v_a_6432_);
v___x_6437_ = v_reuseFailAlloc_6438_;
goto v_reusejp_6436_;
}
v_reusejp_6436_:
{
return v___x_6437_;
}
}
}
}
}
}
else
{
lean_object* v_a_6441_; lean_object* v___x_6443_; uint8_t v_isShared_6444_; uint8_t v_isSharedCheck_6448_; 
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_a_6282_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6441_ = lean_ctor_get(v___x_6347_, 0);
v_isSharedCheck_6448_ = !lean_is_exclusive(v___x_6347_);
if (v_isSharedCheck_6448_ == 0)
{
v___x_6443_ = v___x_6347_;
v_isShared_6444_ = v_isSharedCheck_6448_;
goto v_resetjp_6442_;
}
else
{
lean_inc(v_a_6441_);
lean_dec(v___x_6347_);
v___x_6443_ = lean_box(0);
v_isShared_6444_ = v_isSharedCheck_6448_;
goto v_resetjp_6442_;
}
v_resetjp_6442_:
{
lean_object* v___x_6446_; 
if (v_isShared_6444_ == 0)
{
v___x_6446_ = v___x_6443_;
goto v_reusejp_6445_;
}
else
{
lean_object* v_reuseFailAlloc_6447_; 
v_reuseFailAlloc_6447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6447_, 0, v_a_6441_);
v___x_6446_ = v_reuseFailAlloc_6447_;
goto v_reusejp_6445_;
}
v_reusejp_6445_:
{
return v___x_6446_;
}
}
}
}
}
else
{
lean_object* v_a_6449_; lean_object* v___x_6451_; uint8_t v_isShared_6452_; uint8_t v_isSharedCheck_6456_; 
lean_dec_ref(v_arg_6340_);
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec(v_a_6282_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6449_ = lean_ctor_get(v___x_6344_, 0);
v_isSharedCheck_6456_ = !lean_is_exclusive(v___x_6344_);
if (v_isSharedCheck_6456_ == 0)
{
v___x_6451_ = v___x_6344_;
v_isShared_6452_ = v_isSharedCheck_6456_;
goto v_resetjp_6450_;
}
else
{
lean_inc(v_a_6449_);
lean_dec(v___x_6344_);
v___x_6451_ = lean_box(0);
v_isShared_6452_ = v_isSharedCheck_6456_;
goto v_resetjp_6450_;
}
v_resetjp_6450_:
{
lean_object* v___x_6454_; 
if (v_isShared_6452_ == 0)
{
v___x_6454_ = v___x_6451_;
goto v_reusejp_6453_;
}
else
{
lean_object* v_reuseFailAlloc_6455_; 
v_reuseFailAlloc_6455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6455_, 0, v_a_6449_);
v___x_6454_ = v_reuseFailAlloc_6455_;
goto v_reusejp_6453_;
}
v_reusejp_6453_:
{
return v___x_6454_;
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
else
{
lean_object* v_a_6457_; lean_object* v___x_6459_; uint8_t v_isShared_6460_; uint8_t v_isSharedCheck_6464_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6457_ = lean_ctor_get(v___x_6326_, 0);
v_isSharedCheck_6464_ = !lean_is_exclusive(v___x_6326_);
if (v_isSharedCheck_6464_ == 0)
{
v___x_6459_ = v___x_6326_;
v_isShared_6460_ = v_isSharedCheck_6464_;
goto v_resetjp_6458_;
}
else
{
lean_inc(v_a_6457_);
lean_dec(v___x_6326_);
v___x_6459_ = lean_box(0);
v_isShared_6460_ = v_isSharedCheck_6464_;
goto v_resetjp_6458_;
}
v_resetjp_6458_:
{
lean_object* v___x_6462_; 
if (v_isShared_6460_ == 0)
{
v___x_6462_ = v___x_6459_;
goto v_reusejp_6461_;
}
else
{
lean_object* v_reuseFailAlloc_6463_; 
v_reuseFailAlloc_6463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6463_, 0, v_a_6457_);
v___x_6462_ = v_reuseFailAlloc_6463_;
goto v_reusejp_6461_;
}
v_reusejp_6461_:
{
return v___x_6462_;
}
}
}
}
}
else
{
lean_object* v_a_6465_; lean_object* v___x_6467_; uint8_t v_isShared_6468_; uint8_t v_isSharedCheck_6472_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6465_ = lean_ctor_get(v___x_6323_, 0);
v_isSharedCheck_6472_ = !lean_is_exclusive(v___x_6323_);
if (v_isSharedCheck_6472_ == 0)
{
v___x_6467_ = v___x_6323_;
v_isShared_6468_ = v_isSharedCheck_6472_;
goto v_resetjp_6466_;
}
else
{
lean_inc(v_a_6465_);
lean_dec(v___x_6323_);
v___x_6467_ = lean_box(0);
v_isShared_6468_ = v_isSharedCheck_6472_;
goto v_resetjp_6466_;
}
v_resetjp_6466_:
{
lean_object* v___x_6470_; 
if (v_isShared_6468_ == 0)
{
v___x_6470_ = v___x_6467_;
goto v_reusejp_6469_;
}
else
{
lean_object* v_reuseFailAlloc_6471_; 
v_reuseFailAlloc_6471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6471_, 0, v_a_6465_);
v___x_6470_ = v_reuseFailAlloc_6471_;
goto v_reusejp_6469_;
}
v_reusejp_6469_:
{
return v___x_6470_;
}
}
}
}
}
else
{
lean_object* v_a_6473_; lean_object* v___x_6475_; uint8_t v_isShared_6476_; uint8_t v_isSharedCheck_6480_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6473_ = lean_ctor_get(v___x_6320_, 0);
v_isSharedCheck_6480_ = !lean_is_exclusive(v___x_6320_);
if (v_isSharedCheck_6480_ == 0)
{
v___x_6475_ = v___x_6320_;
v_isShared_6476_ = v_isSharedCheck_6480_;
goto v_resetjp_6474_;
}
else
{
lean_inc(v_a_6473_);
lean_dec(v___x_6320_);
v___x_6475_ = lean_box(0);
v_isShared_6476_ = v_isSharedCheck_6480_;
goto v_resetjp_6474_;
}
v_resetjp_6474_:
{
lean_object* v___x_6478_; 
if (v_isShared_6476_ == 0)
{
v___x_6478_ = v___x_6475_;
goto v_reusejp_6477_;
}
else
{
lean_object* v_reuseFailAlloc_6479_; 
v_reuseFailAlloc_6479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6479_, 0, v_a_6473_);
v___x_6478_ = v_reuseFailAlloc_6479_;
goto v_reusejp_6477_;
}
v_reusejp_6477_:
{
return v___x_6478_;
}
}
}
}
}
else
{
lean_object* v_a_6481_; lean_object* v___x_6483_; uint8_t v_isShared_6484_; uint8_t v_isSharedCheck_6488_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6481_ = lean_ctor_get(v___x_6317_, 0);
v_isSharedCheck_6488_ = !lean_is_exclusive(v___x_6317_);
if (v_isSharedCheck_6488_ == 0)
{
v___x_6483_ = v___x_6317_;
v_isShared_6484_ = v_isSharedCheck_6488_;
goto v_resetjp_6482_;
}
else
{
lean_inc(v_a_6481_);
lean_dec(v___x_6317_);
v___x_6483_ = lean_box(0);
v_isShared_6484_ = v_isSharedCheck_6488_;
goto v_resetjp_6482_;
}
v_resetjp_6482_:
{
lean_object* v___x_6486_; 
if (v_isShared_6484_ == 0)
{
v___x_6486_ = v___x_6483_;
goto v_reusejp_6485_;
}
else
{
lean_object* v_reuseFailAlloc_6487_; 
v_reuseFailAlloc_6487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6487_, 0, v_a_6481_);
v___x_6486_ = v_reuseFailAlloc_6487_;
goto v_reusejp_6485_;
}
v_reusejp_6485_:
{
return v___x_6486_;
}
}
}
}
}
else
{
lean_object* v_a_6489_; lean_object* v___x_6491_; uint8_t v_isShared_6492_; uint8_t v_isSharedCheck_6496_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6489_ = lean_ctor_get(v___x_6314_, 0);
v_isSharedCheck_6496_ = !lean_is_exclusive(v___x_6314_);
if (v_isSharedCheck_6496_ == 0)
{
v___x_6491_ = v___x_6314_;
v_isShared_6492_ = v_isSharedCheck_6496_;
goto v_resetjp_6490_;
}
else
{
lean_inc(v_a_6489_);
lean_dec(v___x_6314_);
v___x_6491_ = lean_box(0);
v_isShared_6492_ = v_isSharedCheck_6496_;
goto v_resetjp_6490_;
}
v_resetjp_6490_:
{
lean_object* v___x_6494_; 
if (v_isShared_6492_ == 0)
{
v___x_6494_ = v___x_6491_;
goto v_reusejp_6493_;
}
else
{
lean_object* v_reuseFailAlloc_6495_; 
v_reuseFailAlloc_6495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6495_, 0, v_a_6489_);
v___x_6494_ = v_reuseFailAlloc_6495_;
goto v_reusejp_6493_;
}
v_reusejp_6493_:
{
return v___x_6494_;
}
}
}
}
}
else
{
lean_object* v_a_6497_; lean_object* v___x_6499_; uint8_t v_isShared_6500_; uint8_t v_isSharedCheck_6504_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6497_ = lean_ctor_get(v___x_6311_, 0);
v_isSharedCheck_6504_ = !lean_is_exclusive(v___x_6311_);
if (v_isSharedCheck_6504_ == 0)
{
v___x_6499_ = v___x_6311_;
v_isShared_6500_ = v_isSharedCheck_6504_;
goto v_resetjp_6498_;
}
else
{
lean_inc(v_a_6497_);
lean_dec(v___x_6311_);
v___x_6499_ = lean_box(0);
v_isShared_6500_ = v_isSharedCheck_6504_;
goto v_resetjp_6498_;
}
v_resetjp_6498_:
{
lean_object* v___x_6502_; 
if (v_isShared_6500_ == 0)
{
v___x_6502_ = v___x_6499_;
goto v_reusejp_6501_;
}
else
{
lean_object* v_reuseFailAlloc_6503_; 
v_reuseFailAlloc_6503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6503_, 0, v_a_6497_);
v___x_6502_ = v_reuseFailAlloc_6503_;
goto v_reusejp_6501_;
}
v_reusejp_6501_:
{
return v___x_6502_;
}
}
}
}
}
else
{
lean_object* v_a_6505_; lean_object* v___x_6507_; uint8_t v_isShared_6508_; uint8_t v_isSharedCheck_6512_; 
lean_del_object(v___x_6284_);
lean_dec(v_a_6282_);
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6505_ = lean_ctor_get(v___x_6308_, 0);
v_isSharedCheck_6512_ = !lean_is_exclusive(v___x_6308_);
if (v_isSharedCheck_6512_ == 0)
{
v___x_6507_ = v___x_6308_;
v_isShared_6508_ = v_isSharedCheck_6512_;
goto v_resetjp_6506_;
}
else
{
lean_inc(v_a_6505_);
lean_dec(v___x_6308_);
v___x_6507_ = lean_box(0);
v_isShared_6508_ = v_isSharedCheck_6512_;
goto v_resetjp_6506_;
}
v_resetjp_6506_:
{
lean_object* v___x_6510_; 
if (v_isShared_6508_ == 0)
{
v___x_6510_ = v___x_6507_;
goto v_reusejp_6509_;
}
else
{
lean_object* v_reuseFailAlloc_6511_; 
v_reuseFailAlloc_6511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6511_, 0, v_a_6505_);
v___x_6510_ = v_reuseFailAlloc_6511_;
goto v_reusejp_6509_;
}
v_reusejp_6509_:
{
return v___x_6510_;
}
}
}
}
}
}
else
{
lean_object* v_a_6528_; lean_object* v___x_6530_; uint8_t v_isShared_6531_; uint8_t v_isSharedCheck_6535_; 
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6528_ = lean_ctor_get(v___x_6281_, 0);
v_isSharedCheck_6535_ = !lean_is_exclusive(v___x_6281_);
if (v_isSharedCheck_6535_ == 0)
{
v___x_6530_ = v___x_6281_;
v_isShared_6531_ = v_isSharedCheck_6535_;
goto v_resetjp_6529_;
}
else
{
lean_inc(v_a_6528_);
lean_dec(v___x_6281_);
v___x_6530_ = lean_box(0);
v_isShared_6531_ = v_isSharedCheck_6535_;
goto v_resetjp_6529_;
}
v_resetjp_6529_:
{
lean_object* v___x_6533_; 
if (v_isShared_6531_ == 0)
{
v___x_6533_ = v___x_6530_;
goto v_reusejp_6532_;
}
else
{
lean_object* v_reuseFailAlloc_6534_; 
v_reuseFailAlloc_6534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6534_, 0, v_a_6528_);
v___x_6533_ = v_reuseFailAlloc_6534_;
goto v_reusejp_6532_;
}
v_reusejp_6532_:
{
return v___x_6533_;
}
}
}
}
else
{
lean_object* v___x_6536_; lean_object* v___x_6538_; 
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v___x_6536_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__8));
if (v_isShared_6279_ == 0)
{
lean_ctor_set(v___x_6278_, 0, v___x_6536_);
v___x_6538_ = v___x_6278_;
goto v_reusejp_6537_;
}
else
{
lean_object* v_reuseFailAlloc_6539_; 
v_reuseFailAlloc_6539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6539_, 0, v___x_6536_);
v___x_6538_ = v_reuseFailAlloc_6539_;
goto v_reusejp_6537_;
}
v_reusejp_6537_:
{
return v___x_6538_;
}
}
}
}
else
{
lean_object* v_a_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6548_; 
lean_dec_ref(v_scope_6047_);
lean_dec(v_goal_6046_);
v_a_6541_ = lean_ctor_get(v___x_6275_, 0);
v_isSharedCheck_6548_ = !lean_is_exclusive(v___x_6275_);
if (v_isSharedCheck_6548_ == 0)
{
v___x_6543_ = v___x_6275_;
v_isShared_6544_ = v_isSharedCheck_6548_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_a_6541_);
lean_dec(v___x_6275_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6548_;
goto v_resetjp_6542_;
}
v_resetjp_6542_:
{
lean_object* v___x_6546_; 
if (v_isShared_6544_ == 0)
{
v___x_6546_ = v___x_6543_;
goto v_reusejp_6545_;
}
else
{
lean_object* v_reuseFailAlloc_6547_; 
v_reuseFailAlloc_6547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6547_, 0, v_a_6541_);
v___x_6546_ = v_reuseFailAlloc_6547_;
goto v_reusejp_6545_;
}
v_reusejp_6545_:
{
return v___x_6546_;
}
}
}
v___jp_6060_:
{
lean_object* v___x_6062_; lean_object* v___x_6063_; 
v___x_6062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6062_, 0, v_scope_6047_);
lean_ctor_set(v___x_6062_, 1, v_gs_6061_);
v___x_6063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
return v___x_6063_;
}
v___jp_6064_:
{
lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; 
v___x_6066_ = lean_box(0);
v___x_6067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6067_, 0, v_g_6065_);
lean_ctor_set(v___x_6067_, 1, v___x_6066_);
v___x_6068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6068_, 0, v_scope_6047_);
lean_ctor_set(v___x_6068_, 1, v___x_6067_);
v___x_6069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
return v___x_6069_;
}
v___jp_6070_:
{
lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; 
v___x_6073_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___y_6071_);
lean_ctor_set(v___x_6073_, 1, v___y_6072_);
v___x_6074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6073_);
v___x_6075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6074_);
return v___x_6075_;
}
v___jp_6076_:
{
lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; 
v___x_6079_ = lean_box(0);
v___x_6080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6080_, 0, v_g_6078_);
lean_ctor_set(v___x_6080_, 1, v___x_6079_);
v___x_6081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6081_, 0, v___y_6077_);
lean_ctor_set(v___x_6081_, 1, v___x_6080_);
v___x_6082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6081_);
return v___x_6082_;
}
v___jp_6083_:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; 
v___x_6086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___y_6084_);
lean_ctor_set(v___x_6086_, 1, v_gs_6085_);
v___x_6087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6086_);
return v___x_6087_;
}
v___jp_6088_:
{
lean_object* v___x_6092_; 
v___x_6092_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_6091_);
if (lean_obj_tag(v___x_6092_) == 0)
{
lean_object* v___x_6094_; uint8_t v_isShared_6095_; uint8_t v_isSharedCheck_6102_; 
v_isSharedCheck_6102_ = !lean_is_exclusive(v___x_6092_);
if (v_isSharedCheck_6102_ == 0)
{
lean_object* v_unused_6103_; 
v_unused_6103_ = lean_ctor_get(v___x_6092_, 0);
lean_dec(v_unused_6103_);
v___x_6094_ = v___x_6092_;
v_isShared_6095_ = v_isSharedCheck_6102_;
goto v_resetjp_6093_;
}
else
{
lean_dec(v___x_6092_);
v___x_6094_ = lean_box(0);
v_isShared_6095_ = v_isSharedCheck_6102_;
goto v_resetjp_6093_;
}
v_resetjp_6093_:
{
lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6100_; 
v___x_6096_ = lean_box(0);
v___x_6097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6097_, 0, v_g_6090_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v___x_6098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___y_6089_);
lean_ctor_set(v___x_6098_, 1, v___x_6097_);
if (v_isShared_6095_ == 0)
{
lean_ctor_set(v___x_6094_, 0, v___x_6098_);
v___x_6100_ = v___x_6094_;
goto v_reusejp_6099_;
}
else
{
lean_object* v_reuseFailAlloc_6101_; 
v_reuseFailAlloc_6101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6101_, 0, v___x_6098_);
v___x_6100_ = v_reuseFailAlloc_6101_;
goto v_reusejp_6099_;
}
v_reusejp_6099_:
{
return v___x_6100_;
}
}
}
else
{
lean_object* v_a_6104_; lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6111_; 
lean_dec(v_g_6090_);
lean_dec_ref(v___y_6089_);
v_a_6104_ = lean_ctor_get(v___x_6092_, 0);
v_isSharedCheck_6111_ = !lean_is_exclusive(v___x_6092_);
if (v_isSharedCheck_6111_ == 0)
{
v___x_6106_ = v___x_6092_;
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
else
{
lean_inc(v_a_6104_);
lean_dec(v___x_6092_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v___x_6109_; 
if (v_isShared_6107_ == 0)
{
v___x_6109_ = v___x_6106_;
goto v_reusejp_6108_;
}
else
{
lean_object* v_reuseFailAlloc_6110_; 
v_reuseFailAlloc_6110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_a_6104_);
v___x_6109_ = v_reuseFailAlloc_6110_;
goto v_reusejp_6108_;
}
v_reusejp_6108_:
{
return v___x_6109_;
}
}
}
}
v___jp_6112_:
{
lean_object* v___x_6126_; 
v___x_6126_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_6118_);
if (lean_obj_tag(v___x_6126_) == 0)
{
lean_object* v___x_6127_; 
lean_dec_ref_known(v___x_6126_, 1);
v___x_6127_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(v___y_6117_, v_goal_6046_, v___y_6115_, v___y_6114_, v___y_6118_, v___y_6123_, v___y_6121_, v___y_6116_, v___y_6125_, v___y_6124_, v___y_6120_, v___y_6119_, v___y_6113_, v___y_6122_);
return v___x_6127_;
}
else
{
lean_object* v_a_6128_; lean_object* v___x_6130_; uint8_t v_isShared_6131_; uint8_t v_isSharedCheck_6135_; 
lean_dec_ref(v___y_6117_);
lean_dec_ref(v___y_6115_);
lean_dec(v_goal_6046_);
v_a_6128_ = lean_ctor_get(v___x_6126_, 0);
v_isSharedCheck_6135_ = !lean_is_exclusive(v___x_6126_);
if (v_isSharedCheck_6135_ == 0)
{
v___x_6130_ = v___x_6126_;
v_isShared_6131_ = v_isSharedCheck_6135_;
goto v_resetjp_6129_;
}
else
{
lean_inc(v_a_6128_);
lean_dec(v___x_6126_);
v___x_6130_ = lean_box(0);
v_isShared_6131_ = v_isSharedCheck_6135_;
goto v_resetjp_6129_;
}
v_resetjp_6129_:
{
lean_object* v___x_6133_; 
if (v_isShared_6131_ == 0)
{
v___x_6133_ = v___x_6130_;
goto v_reusejp_6132_;
}
else
{
lean_object* v_reuseFailAlloc_6134_; 
v_reuseFailAlloc_6134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6134_, 0, v_a_6128_);
v___x_6133_ = v_reuseFailAlloc_6134_;
goto v_reusejp_6132_;
}
v_reusejp_6132_:
{
return v___x_6133_;
}
}
}
}
v___jp_6136_:
{
lean_object* v___x_6152_; lean_object* v___x_6153_; 
lean_dec_ref(v___y_6140_);
lean_dec_ref(v___y_6137_);
v___x_6152_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v___y_6138_);
lean_inc_ref(v___x_6152_);
v___x_6153_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v___x_6152_, v___y_6141_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
if (lean_obj_tag(v___x_6153_) == 0)
{
lean_object* v_a_6154_; lean_object* v___x_6156_; uint8_t v_isShared_6157_; uint8_t v_isSharedCheck_6266_; 
v_a_6154_ = lean_ctor_get(v___x_6153_, 0);
v_isSharedCheck_6266_ = !lean_is_exclusive(v___x_6153_);
if (v_isSharedCheck_6266_ == 0)
{
v___x_6156_ = v___x_6153_;
v_isShared_6157_ = v_isSharedCheck_6266_;
goto v_resetjp_6155_;
}
else
{
lean_inc(v_a_6154_);
lean_dec(v___x_6153_);
v___x_6156_ = lean_box(0);
v_isShared_6157_ = v_isSharedCheck_6266_;
goto v_resetjp_6155_;
}
v_resetjp_6155_:
{
uint8_t v___x_6158_; 
v___x_6158_ = lean_unbox(v_a_6154_);
lean_dec(v_a_6154_);
if (v___x_6158_ == 0)
{
lean_object* v___x_6159_; 
lean_del_object(v___x_6156_);
lean_inc_ref(v___y_6138_);
lean_inc(v_goal_6046_);
v___x_6159_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(v_goal_6046_, v___y_6138_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
if (lean_obj_tag(v___x_6159_) == 0)
{
lean_object* v_a_6160_; 
v_a_6160_ = lean_ctor_get(v___x_6159_, 0);
lean_inc(v_a_6160_);
lean_dec_ref_known(v___x_6159_, 1);
if (lean_obj_tag(v_a_6160_) == 1)
{
lean_object* v_val_6161_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_val_6161_ = lean_ctor_get(v_a_6160_, 0);
lean_inc(v_val_6161_);
lean_dec_ref_known(v_a_6160_, 1);
v___y_6077_ = v___y_6139_;
v_g_6078_ = v_val_6161_;
goto v___jp_6076_;
}
else
{
lean_object* v___x_6162_; 
lean_dec(v_a_6160_);
lean_inc_ref(v___y_6138_);
lean_inc(v_goal_6046_);
v___x_6162_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(v_goal_6046_, v___y_6138_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
if (lean_obj_tag(v___x_6162_) == 0)
{
lean_object* v_a_6163_; 
v_a_6163_ = lean_ctor_get(v___x_6162_, 0);
lean_inc(v_a_6163_);
lean_dec_ref_known(v___x_6162_, 1);
if (lean_obj_tag(v_a_6163_) == 1)
{
lean_object* v_val_6164_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_val_6164_ = lean_ctor_get(v_a_6163_, 0);
lean_inc(v_val_6164_);
lean_dec_ref_known(v_a_6163_, 1);
v___y_6089_ = v___y_6139_;
v_g_6090_ = v_val_6164_;
v___y_6091_ = v___y_6142_;
goto v___jp_6088_;
}
else
{
lean_object* v___x_6165_; 
lean_dec(v_a_6163_);
lean_inc_ref(v___y_6138_);
lean_inc(v_goal_6046_);
v___x_6165_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(v_goal_6046_, v___y_6138_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
if (lean_obj_tag(v___x_6165_) == 0)
{
lean_object* v_a_6166_; 
v_a_6166_ = lean_ctor_get(v___x_6165_, 0);
lean_inc(v_a_6166_);
lean_dec_ref_known(v___x_6165_, 1);
if (lean_obj_tag(v_a_6166_) == 1)
{
lean_object* v_val_6167_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_val_6167_ = lean_ctor_get(v_a_6166_, 0);
lean_inc(v_val_6167_);
lean_dec_ref_known(v_a_6166_, 1);
v___y_6084_ = v___y_6139_;
v_gs_6085_ = v_val_6167_;
goto v___jp_6083_;
}
else
{
lean_object* v___x_6168_; 
lean_dec(v_a_6166_);
lean_inc_ref(v___y_6138_);
lean_inc(v_goal_6046_);
v___x_6168_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(v_goal_6046_, v___y_6138_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
if (lean_obj_tag(v___x_6168_) == 0)
{
lean_object* v_a_6169_; 
v_a_6169_ = lean_ctor_get(v___x_6168_, 0);
lean_inc(v_a_6169_);
lean_dec_ref_known(v___x_6168_, 1);
if (lean_obj_tag(v_a_6169_) == 1)
{
lean_object* v_val_6170_; lean_object* v___x_6171_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_val_6170_ = lean_ctor_get(v_a_6169_, 0);
lean_inc(v_val_6170_);
lean_dec_ref_known(v_a_6169_, 1);
v___x_6171_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_6142_);
if (lean_obj_tag(v___x_6171_) == 0)
{
lean_object* v___x_6173_; uint8_t v_isShared_6174_; uint8_t v_isSharedCheck_6179_; 
v_isSharedCheck_6179_ = !lean_is_exclusive(v___x_6171_);
if (v_isSharedCheck_6179_ == 0)
{
lean_object* v_unused_6180_; 
v_unused_6180_ = lean_ctor_get(v___x_6171_, 0);
lean_dec(v_unused_6180_);
v___x_6173_ = v___x_6171_;
v_isShared_6174_ = v_isSharedCheck_6179_;
goto v_resetjp_6172_;
}
else
{
lean_dec(v___x_6171_);
v___x_6173_ = lean_box(0);
v_isShared_6174_ = v_isSharedCheck_6179_;
goto v_resetjp_6172_;
}
v_resetjp_6172_:
{
lean_object* v___x_6175_; lean_object* v___x_6177_; 
v___x_6175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6175_, 0, v___y_6139_);
lean_ctor_set(v___x_6175_, 1, v_val_6170_);
if (v_isShared_6174_ == 0)
{
lean_ctor_set(v___x_6173_, 0, v___x_6175_);
v___x_6177_ = v___x_6173_;
goto v_reusejp_6176_;
}
else
{
lean_object* v_reuseFailAlloc_6178_; 
v_reuseFailAlloc_6178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6178_, 0, v___x_6175_);
v___x_6177_ = v_reuseFailAlloc_6178_;
goto v_reusejp_6176_;
}
v_reusejp_6176_:
{
return v___x_6177_;
}
}
}
else
{
lean_object* v_a_6181_; lean_object* v___x_6183_; uint8_t v_isShared_6184_; uint8_t v_isSharedCheck_6188_; 
lean_dec(v_val_6170_);
lean_dec_ref(v___y_6139_);
v_a_6181_ = lean_ctor_get(v___x_6171_, 0);
v_isSharedCheck_6188_ = !lean_is_exclusive(v___x_6171_);
if (v_isSharedCheck_6188_ == 0)
{
v___x_6183_ = v___x_6171_;
v_isShared_6184_ = v_isSharedCheck_6188_;
goto v_resetjp_6182_;
}
else
{
lean_inc(v_a_6181_);
lean_dec(v___x_6171_);
v___x_6183_ = lean_box(0);
v_isShared_6184_ = v_isSharedCheck_6188_;
goto v_resetjp_6182_;
}
v_resetjp_6182_:
{
lean_object* v___x_6186_; 
if (v_isShared_6184_ == 0)
{
v___x_6186_ = v___x_6183_;
goto v_reusejp_6185_;
}
else
{
lean_object* v_reuseFailAlloc_6187_; 
v_reuseFailAlloc_6187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6187_, 0, v_a_6181_);
v___x_6186_ = v_reuseFailAlloc_6187_;
goto v_reusejp_6185_;
}
v_reusejp_6185_:
{
return v___x_6186_;
}
}
}
}
else
{
lean_object* v___x_6189_; 
lean_dec(v_a_6169_);
lean_inc_ref(v___y_6138_);
lean_inc(v_goal_6046_);
v___x_6189_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(v_goal_6046_, v___y_6138_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
if (lean_obj_tag(v___x_6189_) == 0)
{
lean_object* v_a_6190_; 
v_a_6190_ = lean_ctor_get(v___x_6189_, 0);
lean_inc(v_a_6190_);
lean_dec_ref_known(v___x_6189_, 1);
if (lean_obj_tag(v_a_6190_) == 1)
{
lean_object* v_val_6191_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_val_6191_ = lean_ctor_get(v_a_6190_, 0);
lean_inc(v_val_6191_);
lean_dec_ref_known(v_a_6190_, 1);
v___y_6089_ = v___y_6139_;
v_g_6090_ = v_val_6191_;
v___y_6091_ = v___y_6142_;
goto v___jp_6088_;
}
else
{
lean_object* v___x_6192_; 
lean_dec(v_a_6190_);
lean_inc_ref(v___y_6138_);
lean_inc(v_goal_6046_);
v___x_6192_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f(v_goal_6046_, v___y_6138_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
if (lean_obj_tag(v___x_6192_) == 0)
{
lean_object* v_a_6193_; 
v_a_6193_ = lean_ctor_get(v___x_6192_, 0);
lean_inc(v_a_6193_);
lean_dec_ref_known(v___x_6192_, 1);
if (lean_obj_tag(v_a_6193_) == 1)
{
lean_object* v_val_6194_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_val_6194_ = lean_ctor_get(v_a_6193_, 0);
lean_inc(v_val_6194_);
lean_dec_ref_known(v_a_6193_, 1);
v___y_6089_ = v___y_6139_;
v_g_6090_ = v_val_6194_;
v___y_6091_ = v___y_6142_;
goto v___jp_6088_;
}
else
{
lean_object* v___x_6195_; uint8_t v___x_6196_; 
lean_dec(v_a_6193_);
v___x_6195_ = l_Lean_Expr_getAppFn(v___x_6152_);
v___x_6196_ = l_Lean_Expr_isConst(v___x_6195_);
if (v___x_6196_ == 0)
{
uint8_t v___x_6197_; 
v___x_6197_ = l_Lean_Expr_isFVar(v___x_6195_);
lean_dec_ref(v___x_6195_);
if (v___x_6197_ == 0)
{
lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v_a_6204_; lean_object* v___x_6206_; uint8_t v_isShared_6207_; uint8_t v_isSharedCheck_6211_; 
lean_dec_ref(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v___x_6198_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1);
v___x_6199_ = l_Lean_MessageData_ofExpr(v___x_6152_);
v___x_6200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6200_, 0, v___x_6198_);
lean_ctor_set(v___x_6200_, 1, v___x_6199_);
v___x_6201_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3);
v___x_6202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6202_, 0, v___x_6200_);
lean_ctor_set(v___x_6202_, 1, v___x_6201_);
v___x_6203_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_6202_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
v_a_6204_ = lean_ctor_get(v___x_6203_, 0);
v_isSharedCheck_6211_ = !lean_is_exclusive(v___x_6203_);
if (v_isSharedCheck_6211_ == 0)
{
v___x_6206_ = v___x_6203_;
v_isShared_6207_ = v_isSharedCheck_6211_;
goto v_resetjp_6205_;
}
else
{
lean_inc(v_a_6204_);
lean_dec(v___x_6203_);
v___x_6206_ = lean_box(0);
v_isShared_6207_ = v_isSharedCheck_6211_;
goto v_resetjp_6205_;
}
v_resetjp_6205_:
{
lean_object* v___x_6209_; 
if (v_isShared_6207_ == 0)
{
v___x_6209_ = v___x_6206_;
goto v_reusejp_6208_;
}
else
{
lean_object* v_reuseFailAlloc_6210_; 
v_reuseFailAlloc_6210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6210_, 0, v_a_6204_);
v___x_6209_ = v_reuseFailAlloc_6210_;
goto v_reusejp_6208_;
}
v_reusejp_6208_:
{
return v___x_6209_;
}
}
}
else
{
lean_dec_ref(v___x_6152_);
v___y_6113_ = v___y_6150_;
v___y_6114_ = v___y_6141_;
v___y_6115_ = v___y_6138_;
v___y_6116_ = v___y_6145_;
v___y_6117_ = v___y_6139_;
v___y_6118_ = v___y_6142_;
v___y_6119_ = v___y_6149_;
v___y_6120_ = v___y_6148_;
v___y_6121_ = v___y_6144_;
v___y_6122_ = v___y_6151_;
v___y_6123_ = v___y_6143_;
v___y_6124_ = v___y_6147_;
v___y_6125_ = v___y_6146_;
goto v___jp_6112_;
}
}
else
{
lean_dec_ref(v___x_6195_);
lean_dec_ref(v___x_6152_);
v___y_6113_ = v___y_6150_;
v___y_6114_ = v___y_6141_;
v___y_6115_ = v___y_6138_;
v___y_6116_ = v___y_6145_;
v___y_6117_ = v___y_6139_;
v___y_6118_ = v___y_6142_;
v___y_6119_ = v___y_6149_;
v___y_6120_ = v___y_6148_;
v___y_6121_ = v___y_6144_;
v___y_6122_ = v___y_6151_;
v___y_6123_ = v___y_6143_;
v___y_6124_ = v___y_6147_;
v___y_6125_ = v___y_6146_;
goto v___jp_6112_;
}
}
}
else
{
lean_object* v_a_6212_; lean_object* v___x_6214_; uint8_t v_isShared_6215_; uint8_t v_isSharedCheck_6219_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_a_6212_ = lean_ctor_get(v___x_6192_, 0);
v_isSharedCheck_6219_ = !lean_is_exclusive(v___x_6192_);
if (v_isSharedCheck_6219_ == 0)
{
v___x_6214_ = v___x_6192_;
v_isShared_6215_ = v_isSharedCheck_6219_;
goto v_resetjp_6213_;
}
else
{
lean_inc(v_a_6212_);
lean_dec(v___x_6192_);
v___x_6214_ = lean_box(0);
v_isShared_6215_ = v_isSharedCheck_6219_;
goto v_resetjp_6213_;
}
v_resetjp_6213_:
{
lean_object* v___x_6217_; 
if (v_isShared_6215_ == 0)
{
v___x_6217_ = v___x_6214_;
goto v_reusejp_6216_;
}
else
{
lean_object* v_reuseFailAlloc_6218_; 
v_reuseFailAlloc_6218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6218_, 0, v_a_6212_);
v___x_6217_ = v_reuseFailAlloc_6218_;
goto v_reusejp_6216_;
}
v_reusejp_6216_:
{
return v___x_6217_;
}
}
}
}
}
else
{
lean_object* v_a_6220_; lean_object* v___x_6222_; uint8_t v_isShared_6223_; uint8_t v_isSharedCheck_6227_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_a_6220_ = lean_ctor_get(v___x_6189_, 0);
v_isSharedCheck_6227_ = !lean_is_exclusive(v___x_6189_);
if (v_isSharedCheck_6227_ == 0)
{
v___x_6222_ = v___x_6189_;
v_isShared_6223_ = v_isSharedCheck_6227_;
goto v_resetjp_6221_;
}
else
{
lean_inc(v_a_6220_);
lean_dec(v___x_6189_);
v___x_6222_ = lean_box(0);
v_isShared_6223_ = v_isSharedCheck_6227_;
goto v_resetjp_6221_;
}
v_resetjp_6221_:
{
lean_object* v___x_6225_; 
if (v_isShared_6223_ == 0)
{
v___x_6225_ = v___x_6222_;
goto v_reusejp_6224_;
}
else
{
lean_object* v_reuseFailAlloc_6226_; 
v_reuseFailAlloc_6226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6226_, 0, v_a_6220_);
v___x_6225_ = v_reuseFailAlloc_6226_;
goto v_reusejp_6224_;
}
v_reusejp_6224_:
{
return v___x_6225_;
}
}
}
}
}
else
{
lean_object* v_a_6228_; lean_object* v___x_6230_; uint8_t v_isShared_6231_; uint8_t v_isSharedCheck_6235_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_a_6228_ = lean_ctor_get(v___x_6168_, 0);
v_isSharedCheck_6235_ = !lean_is_exclusive(v___x_6168_);
if (v_isSharedCheck_6235_ == 0)
{
v___x_6230_ = v___x_6168_;
v_isShared_6231_ = v_isSharedCheck_6235_;
goto v_resetjp_6229_;
}
else
{
lean_inc(v_a_6228_);
lean_dec(v___x_6168_);
v___x_6230_ = lean_box(0);
v_isShared_6231_ = v_isSharedCheck_6235_;
goto v_resetjp_6229_;
}
v_resetjp_6229_:
{
lean_object* v___x_6233_; 
if (v_isShared_6231_ == 0)
{
v___x_6233_ = v___x_6230_;
goto v_reusejp_6232_;
}
else
{
lean_object* v_reuseFailAlloc_6234_; 
v_reuseFailAlloc_6234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6234_, 0, v_a_6228_);
v___x_6233_ = v_reuseFailAlloc_6234_;
goto v_reusejp_6232_;
}
v_reusejp_6232_:
{
return v___x_6233_;
}
}
}
}
}
else
{
lean_object* v_a_6236_; lean_object* v___x_6238_; uint8_t v_isShared_6239_; uint8_t v_isSharedCheck_6243_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_a_6236_ = lean_ctor_get(v___x_6165_, 0);
v_isSharedCheck_6243_ = !lean_is_exclusive(v___x_6165_);
if (v_isSharedCheck_6243_ == 0)
{
v___x_6238_ = v___x_6165_;
v_isShared_6239_ = v_isSharedCheck_6243_;
goto v_resetjp_6237_;
}
else
{
lean_inc(v_a_6236_);
lean_dec(v___x_6165_);
v___x_6238_ = lean_box(0);
v_isShared_6239_ = v_isSharedCheck_6243_;
goto v_resetjp_6237_;
}
v_resetjp_6237_:
{
lean_object* v___x_6241_; 
if (v_isShared_6239_ == 0)
{
v___x_6241_ = v___x_6238_;
goto v_reusejp_6240_;
}
else
{
lean_object* v_reuseFailAlloc_6242_; 
v_reuseFailAlloc_6242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6242_, 0, v_a_6236_);
v___x_6241_ = v_reuseFailAlloc_6242_;
goto v_reusejp_6240_;
}
v_reusejp_6240_:
{
return v___x_6241_;
}
}
}
}
}
else
{
lean_object* v_a_6244_; lean_object* v___x_6246_; uint8_t v_isShared_6247_; uint8_t v_isSharedCheck_6251_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_a_6244_ = lean_ctor_get(v___x_6162_, 0);
v_isSharedCheck_6251_ = !lean_is_exclusive(v___x_6162_);
if (v_isSharedCheck_6251_ == 0)
{
v___x_6246_ = v___x_6162_;
v_isShared_6247_ = v_isSharedCheck_6251_;
goto v_resetjp_6245_;
}
else
{
lean_inc(v_a_6244_);
lean_dec(v___x_6162_);
v___x_6246_ = lean_box(0);
v_isShared_6247_ = v_isSharedCheck_6251_;
goto v_resetjp_6245_;
}
v_resetjp_6245_:
{
lean_object* v___x_6249_; 
if (v_isShared_6247_ == 0)
{
v___x_6249_ = v___x_6246_;
goto v_reusejp_6248_;
}
else
{
lean_object* v_reuseFailAlloc_6250_; 
v_reuseFailAlloc_6250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6250_, 0, v_a_6244_);
v___x_6249_ = v_reuseFailAlloc_6250_;
goto v_reusejp_6248_;
}
v_reusejp_6248_:
{
return v___x_6249_;
}
}
}
}
}
else
{
lean_object* v_a_6252_; lean_object* v___x_6254_; uint8_t v_isShared_6255_; uint8_t v_isSharedCheck_6259_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_a_6252_ = lean_ctor_get(v___x_6159_, 0);
v_isSharedCheck_6259_ = !lean_is_exclusive(v___x_6159_);
if (v_isSharedCheck_6259_ == 0)
{
v___x_6254_ = v___x_6159_;
v_isShared_6255_ = v_isSharedCheck_6259_;
goto v_resetjp_6253_;
}
else
{
lean_inc(v_a_6252_);
lean_dec(v___x_6159_);
v___x_6254_ = lean_box(0);
v_isShared_6255_ = v_isSharedCheck_6259_;
goto v_resetjp_6253_;
}
v_resetjp_6253_:
{
lean_object* v___x_6257_; 
if (v_isShared_6255_ == 0)
{
v___x_6257_ = v___x_6254_;
goto v_reusejp_6256_;
}
else
{
lean_object* v_reuseFailAlloc_6258_; 
v_reuseFailAlloc_6258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6258_, 0, v_a_6252_);
v___x_6257_ = v_reuseFailAlloc_6258_;
goto v_reusejp_6256_;
}
v_reusejp_6256_:
{
return v___x_6257_;
}
}
}
}
else
{
lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6264_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6139_);
lean_dec(v_goal_6046_);
v___x_6260_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v___y_6138_);
lean_dec_ref(v___y_6138_);
v___x_6261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6261_, 0, v___x_6260_);
v___x_6262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6262_, 0, v___x_6261_);
if (v_isShared_6157_ == 0)
{
lean_ctor_set(v___x_6156_, 0, v___x_6262_);
v___x_6264_ = v___x_6156_;
goto v_reusejp_6263_;
}
else
{
lean_object* v_reuseFailAlloc_6265_; 
v_reuseFailAlloc_6265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6265_, 0, v___x_6262_);
v___x_6264_ = v_reuseFailAlloc_6265_;
goto v_reusejp_6263_;
}
v_reusejp_6263_:
{
return v___x_6264_;
}
}
}
}
else
{
lean_object* v_a_6267_; lean_object* v___x_6269_; uint8_t v_isShared_6270_; uint8_t v_isSharedCheck_6274_; 
lean_dec_ref(v___x_6152_);
lean_dec_ref(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec(v_goal_6046_);
v_a_6267_ = lean_ctor_get(v___x_6153_, 0);
v_isSharedCheck_6274_ = !lean_is_exclusive(v___x_6153_);
if (v_isSharedCheck_6274_ == 0)
{
v___x_6269_ = v___x_6153_;
v_isShared_6270_ = v_isSharedCheck_6274_;
goto v_resetjp_6268_;
}
else
{
lean_inc(v_a_6267_);
lean_dec(v___x_6153_);
v___x_6269_ = lean_box(0);
v_isShared_6270_ = v_isSharedCheck_6274_;
goto v_resetjp_6268_;
}
v_resetjp_6268_:
{
lean_object* v___x_6272_; 
if (v_isShared_6270_ == 0)
{
v___x_6272_ = v___x_6269_;
goto v_reusejp_6271_;
}
else
{
lean_object* v_reuseFailAlloc_6273_; 
v_reuseFailAlloc_6273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6273_, 0, v_a_6267_);
v___x_6272_ = v_reuseFailAlloc_6273_;
goto v_reusejp_6271_;
}
v_reusejp_6271_:
{
return v___x_6272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___boxed(lean_object* v_goal_6549_, lean_object* v_scope_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_, lean_object* v___y_6559_, lean_object* v___y_6560_, lean_object* v___y_6561_, lean_object* v___y_6562_){
_start:
{
lean_object* v_res_6563_; 
v_res_6563_ = l_Lean_Elab_Tactic_VCGen_solve___lam__0(v_goal_6549_, v_scope_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_, v___y_6561_);
lean_dec(v___y_6561_);
lean_dec_ref(v___y_6560_);
lean_dec(v___y_6559_);
lean_dec_ref(v___y_6558_);
lean_dec(v___y_6557_);
lean_dec_ref(v___y_6556_);
lean_dec(v___y_6555_);
lean_dec_ref(v___y_6554_);
lean_dec(v___y_6553_);
lean_dec(v___y_6552_);
lean_dec_ref(v___y_6551_);
return v_res_6563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve(lean_object* v_scope_6564_, lean_object* v_goal_6565_, lean_object* v_a_6566_, lean_object* v_a_6567_, lean_object* v_a_6568_, lean_object* v_a_6569_, lean_object* v_a_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_, lean_object* v_a_6573_, lean_object* v_a_6574_, lean_object* v_a_6575_, lean_object* v_a_6576_){
_start:
{
lean_object* v___f_6578_; lean_object* v___x_6579_; 
lean_inc(v_goal_6565_);
v___f_6578_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___boxed), 14, 2);
lean_closure_set(v___f_6578_, 0, v_goal_6565_);
lean_closure_set(v___f_6578_, 1, v_scope_6564_);
v___x_6579_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_6565_, v___f_6578_, v_a_6566_, v_a_6567_, v_a_6568_, v_a_6569_, v_a_6570_, v_a_6571_, v_a_6572_, v_a_6573_, v_a_6574_, v_a_6575_, v_a_6576_);
return v___x_6579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___boxed(lean_object* v_scope_6580_, lean_object* v_goal_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_, lean_object* v_a_6584_, lean_object* v_a_6585_, lean_object* v_a_6586_, lean_object* v_a_6587_, lean_object* v_a_6588_, lean_object* v_a_6589_, lean_object* v_a_6590_, lean_object* v_a_6591_, lean_object* v_a_6592_, lean_object* v_a_6593_){
_start:
{
lean_object* v_res_6594_; 
v_res_6594_ = l_Lean_Elab_Tactic_VCGen_solve(v_scope_6580_, v_goal_6581_, v_a_6582_, v_a_6583_, v_a_6584_, v_a_6585_, v_a_6586_, v_a_6587_, v_a_6588_, v_a_6589_, v_a_6590_, v_a_6591_, v_a_6592_);
lean_dec(v_a_6592_);
lean_dec_ref(v_a_6591_);
lean_dec(v_a_6590_);
lean_dec_ref(v_a_6589_);
lean_dec(v_a_6588_);
lean_dec_ref(v_a_6587_);
lean_dec(v_a_6586_);
lean_dec_ref(v_a_6585_);
lean_dec(v_a_6584_);
lean_dec(v_a_6583_);
lean_dec_ref(v_a_6582_);
return v_res_6594_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_RuleCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Entails(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Solve(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_Solve(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_RuleCache(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Entails(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_Solve(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_Solve(builtin);
}
#ifdef __cplusplus
}
#endif
