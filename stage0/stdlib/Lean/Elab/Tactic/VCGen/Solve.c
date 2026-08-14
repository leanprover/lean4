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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 119, 227, 254, 29, 206, 25, 24)}};
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
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(124, 118, 39, 144, 78, 10, 170, 168)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 255, 127, 189, 81, 246, 28, 251)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f(lean_object* v_goal_718_, lean_object* v_target_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3));
v___x_733_ = l_Lean_Expr_isAppOf(v_target_719_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec(v_goal_718_);
v___x_734_ = lean_box(0);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Elab_Tactic_VCGen_unfoldTriple(v_goal_718_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_745_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_745_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_a_737_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
v_a_746_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_736_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_736_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___boxed(lean_object* v_goal_754_, lean_object* v_target_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f(v_goal_754_, v_target_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_target_755_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
lean_object* v_ks_773_; lean_object* v_vs_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_798_; 
v_ks_773_ = lean_ctor_get(v_x_769_, 0);
v_vs_774_ = lean_ctor_get(v_x_769_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_769_);
if (v_isSharedCheck_798_ == 0)
{
v___x_776_ = v_x_769_;
v_isShared_777_ = v_isSharedCheck_798_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_vs_774_);
lean_inc(v_ks_773_);
lean_dec(v_x_769_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_798_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = lean_array_get_size(v_ks_773_);
v___x_779_ = lean_nat_dec_lt(v_x_770_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
lean_dec(v_x_770_);
v___x_780_ = lean_array_push(v_ks_773_, v_x_771_);
v___x_781_ = lean_array_push(v_vs_774_, v_x_772_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___x_781_);
lean_ctor_set(v___x_776_, 0, v___x_780_);
v___x_783_ = v___x_776_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
else
{
lean_object* v_k_x27_785_; uint8_t v___x_786_; 
v_k_x27_785_ = lean_array_fget_borrowed(v_ks_773_, v_x_770_);
v___x_786_ = l_Lean_instBEqMVarId_beq(v_x_771_, v_k_x27_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_788_; 
if (v_isShared_777_ == 0)
{
v___x_788_ = v___x_776_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_ks_773_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_vs_774_);
v___x_788_ = v_reuseFailAlloc_792_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_x_770_, v___x_789_);
lean_dec(v_x_770_);
v_x_769_ = v___x_788_;
v_x_770_ = v___x_790_;
goto _start;
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_793_ = lean_array_fset(v_ks_773_, v_x_770_, v_x_771_);
v___x_794_ = lean_array_fset(v_vs_774_, v_x_770_, v_x_772_);
lean_dec(v_x_770_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___x_794_);
lean_ctor_set(v___x_776_, 0, v___x_793_);
v___x_796_ = v___x_776_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_799_, lean_object* v_k_800_, lean_object* v_v_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_799_, v___x_802_, v_k_800_, v_v_801_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_x_805_, size_t v_x_806_, size_t v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
if (lean_obj_tag(v_x_805_) == 0)
{
lean_object* v_es_810_; size_t v___x_811_; size_t v___x_812_; lean_object* v_j_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_es_810_ = lean_ctor_get(v_x_805_, 0);
v___x_811_ = ((size_t)31ULL);
v___x_812_ = lean_usize_land(v_x_806_, v___x_811_);
v_j_813_ = lean_usize_to_nat(v___x_812_);
v___x_814_ = lean_array_get_size(v_es_810_);
v___x_815_ = lean_nat_dec_lt(v_j_813_, v___x_814_);
if (v___x_815_ == 0)
{
lean_dec(v_j_813_);
lean_dec(v_x_809_);
lean_dec(v_x_808_);
return v_x_805_;
}
else
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_854_; 
lean_inc_ref(v_es_810_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_x_805_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v_x_805_, 0);
lean_dec(v_unused_855_);
v___x_817_ = v_x_805_;
v_isShared_818_ = v_isSharedCheck_854_;
goto v_resetjp_816_;
}
else
{
lean_dec(v_x_805_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_854_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_v_819_; lean_object* v___x_820_; lean_object* v_xs_x27_821_; lean_object* v___y_823_; 
v_v_819_ = lean_array_fget(v_es_810_, v_j_813_);
v___x_820_ = lean_box(0);
v_xs_x27_821_ = lean_array_fset(v_es_810_, v_j_813_, v___x_820_);
switch(lean_obj_tag(v_v_819_))
{
case 0:
{
lean_object* v_key_828_; lean_object* v_val_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_839_; 
v_key_828_ = lean_ctor_get(v_v_819_, 0);
v_val_829_ = lean_ctor_get(v_v_819_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_v_819_);
if (v_isSharedCheck_839_ == 0)
{
v___x_831_ = v_v_819_;
v_isShared_832_ = v_isSharedCheck_839_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_val_829_);
lean_inc(v_key_828_);
lean_dec(v_v_819_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_839_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v___x_833_; 
v___x_833_ = l_Lean_instBEqMVarId_beq(v_x_808_, v_key_828_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_del_object(v___x_831_);
v___x_834_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_828_, v_val_829_, v_x_808_, v_x_809_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
v___y_823_ = v___x_835_;
goto v___jp_822_;
}
else
{
lean_object* v___x_837_; 
lean_dec(v_val_829_);
lean_dec(v_key_828_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v_x_809_);
lean_ctor_set(v___x_831_, 0, v_x_808_);
v___x_837_ = v___x_831_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_x_808_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_x_809_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
v___y_823_ = v___x_837_;
goto v___jp_822_;
}
}
}
}
case 1:
{
lean_object* v_node_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_852_; 
v_node_840_ = lean_ctor_get(v_v_819_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v_v_819_);
if (v_isSharedCheck_852_ == 0)
{
v___x_842_ = v_v_819_;
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_node_840_);
lean_dec(v_v_819_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
size_t v___x_844_; size_t v___x_845_; size_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_844_ = ((size_t)5ULL);
v___x_845_ = lean_usize_shift_right(v_x_806_, v___x_844_);
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_add(v_x_807_, v___x_846_);
v___x_848_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_node_840_, v___x_845_, v___x_847_, v_x_808_, v_x_809_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_848_);
v___x_850_ = v___x_842_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
v___y_823_ = v___x_850_;
goto v___jp_822_;
}
}
}
default: 
{
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v_x_808_);
lean_ctor_set(v___x_853_, 1, v_x_809_);
v___y_823_ = v___x_853_;
goto v___jp_822_;
}
}
v___jp_822_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = lean_array_fset(v_xs_x27_821_, v_j_813_, v___y_823_);
lean_dec(v_j_813_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_824_);
v___x_826_ = v___x_817_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
else
{
lean_object* v_ks_856_; lean_object* v_vs_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_877_; 
v_ks_856_ = lean_ctor_get(v_x_805_, 0);
v_vs_857_ = lean_ctor_get(v_x_805_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_x_805_);
if (v_isSharedCheck_877_ == 0)
{
v___x_859_ = v_x_805_;
v_isShared_860_ = v_isSharedCheck_877_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_vs_857_);
lean_inc(v_ks_856_);
lean_dec(v_x_805_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_877_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_ks_856_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_vs_857_);
v___x_862_ = v_reuseFailAlloc_876_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v_newNode_863_; uint8_t v___y_865_; size_t v___x_871_; uint8_t v___x_872_; 
v_newNode_863_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v___x_862_, v_x_808_, v_x_809_);
v___x_871_ = ((size_t)7ULL);
v___x_872_ = lean_usize_dec_le(v___x_871_, v_x_807_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_873_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_863_);
v___x_874_ = lean_unsigned_to_nat(4u);
v___x_875_ = lean_nat_dec_lt(v___x_873_, v___x_874_);
lean_dec(v___x_873_);
v___y_865_ = v___x_875_;
goto v___jp_864_;
}
else
{
v___y_865_ = v___x_872_;
goto v___jp_864_;
}
v___jp_864_:
{
if (v___y_865_ == 0)
{
lean_object* v_ks_866_; lean_object* v_vs_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_ks_866_ = lean_ctor_get(v_newNode_863_, 0);
lean_inc_ref(v_ks_866_);
v_vs_867_ = lean_ctor_get(v_newNode_863_, 1);
lean_inc_ref(v_vs_867_);
lean_dec_ref(v_newNode_863_);
v___x_868_ = lean_unsigned_to_nat(0u);
v___x_869_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_x_807_, v_ks_866_, v_vs_867_, v___x_868_, v___x_869_);
lean_dec_ref(v_vs_867_);
lean_dec_ref(v_ks_866_);
return v___x_870_;
}
else
{
return v_newNode_863_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_878_, lean_object* v_keys_879_, lean_object* v_vals_880_, lean_object* v_i_881_, lean_object* v_entries_882_){
_start:
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = lean_array_get_size(v_keys_879_);
v___x_884_ = lean_nat_dec_lt(v_i_881_, v___x_883_);
if (v___x_884_ == 0)
{
lean_dec(v_i_881_);
return v_entries_882_;
}
else
{
lean_object* v_k_885_; lean_object* v_v_886_; uint64_t v___x_887_; size_t v_h_888_; size_t v___x_889_; lean_object* v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v_h_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_k_885_ = lean_array_fget_borrowed(v_keys_879_, v_i_881_);
v_v_886_ = lean_array_fget_borrowed(v_vals_880_, v_i_881_);
v___x_887_ = l_Lean_instHashableMVarId_hash(v_k_885_);
v_h_888_ = lean_uint64_to_usize(v___x_887_);
v___x_889_ = ((size_t)5ULL);
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_sub(v_depth_878_, v___x_891_);
v___x_893_ = lean_usize_mul(v___x_889_, v___x_892_);
v_h_894_ = lean_usize_shift_right(v_h_888_, v___x_893_);
v___x_895_ = lean_nat_add(v_i_881_, v___x_890_);
lean_dec(v_i_881_);
lean_inc(v_v_886_);
lean_inc(v_k_885_);
v___x_896_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_entries_882_, v_h_894_, v_depth_878_, v_k_885_, v_v_886_);
v_i_881_ = v___x_895_;
v_entries_882_ = v___x_896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_898_, lean_object* v_keys_899_, lean_object* v_vals_900_, lean_object* v_i_901_, lean_object* v_entries_902_){
_start:
{
size_t v_depth_boxed_903_; lean_object* v_res_904_; 
v_depth_boxed_903_ = lean_unbox_usize(v_depth_898_);
lean_dec(v_depth_898_);
v_res_904_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_903_, v_keys_899_, v_vals_900_, v_i_901_, v_entries_902_);
lean_dec_ref(v_vals_900_);
lean_dec_ref(v_keys_899_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
size_t v_x_8514__boxed_910_; size_t v_x_8515__boxed_911_; lean_object* v_res_912_; 
v_x_8514__boxed_910_ = lean_unbox_usize(v_x_906_);
lean_dec(v_x_906_);
v_x_8515__boxed_911_ = lean_unbox_usize(v_x_907_);
lean_dec(v_x_907_);
v_res_912_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_905_, v_x_8514__boxed_910_, v_x_8515__boxed_911_, v_x_908_, v_x_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
uint64_t v___x_916_; size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; 
v___x_916_ = l_Lean_instHashableMVarId_hash(v_x_914_);
v___x_917_ = lean_uint64_to_usize(v___x_916_);
v___x_918_ = ((size_t)1ULL);
v___x_919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_913_, v___x_917_, v___x_918_, v_x_914_, v_x_915_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(lean_object* v_mvarId_920_, lean_object* v_val_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; lean_object* v_mctx_925_; lean_object* v_cache_926_; lean_object* v_zetaDeltaFVarIds_927_; lean_object* v_postponed_928_; lean_object* v_diag_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_957_; 
v___x_924_ = lean_st_ref_take(v___y_922_);
v_mctx_925_ = lean_ctor_get(v___x_924_, 0);
v_cache_926_ = lean_ctor_get(v___x_924_, 1);
v_zetaDeltaFVarIds_927_ = lean_ctor_get(v___x_924_, 2);
v_postponed_928_ = lean_ctor_get(v___x_924_, 3);
v_diag_929_ = lean_ctor_get(v___x_924_, 4);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_957_ == 0)
{
v___x_931_ = v___x_924_;
v_isShared_932_ = v_isSharedCheck_957_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_diag_929_);
lean_inc(v_postponed_928_);
lean_inc(v_zetaDeltaFVarIds_927_);
lean_inc(v_cache_926_);
lean_inc(v_mctx_925_);
lean_dec(v___x_924_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_957_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_depth_933_; lean_object* v_levelAssignDepth_934_; lean_object* v_lmvarCounter_935_; lean_object* v_mvarCounter_936_; lean_object* v_lDecls_937_; lean_object* v_decls_938_; lean_object* v_userNames_939_; lean_object* v_lAssignment_940_; lean_object* v_eAssignment_941_; lean_object* v_dAssignment_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_956_; 
v_depth_933_ = lean_ctor_get(v_mctx_925_, 0);
v_levelAssignDepth_934_ = lean_ctor_get(v_mctx_925_, 1);
v_lmvarCounter_935_ = lean_ctor_get(v_mctx_925_, 2);
v_mvarCounter_936_ = lean_ctor_get(v_mctx_925_, 3);
v_lDecls_937_ = lean_ctor_get(v_mctx_925_, 4);
v_decls_938_ = lean_ctor_get(v_mctx_925_, 5);
v_userNames_939_ = lean_ctor_get(v_mctx_925_, 6);
v_lAssignment_940_ = lean_ctor_get(v_mctx_925_, 7);
v_eAssignment_941_ = lean_ctor_get(v_mctx_925_, 8);
v_dAssignment_942_ = lean_ctor_get(v_mctx_925_, 9);
v_isSharedCheck_956_ = !lean_is_exclusive(v_mctx_925_);
if (v_isSharedCheck_956_ == 0)
{
v___x_944_ = v_mctx_925_;
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_dAssignment_942_);
lean_inc(v_eAssignment_941_);
lean_inc(v_lAssignment_940_);
lean_inc(v_userNames_939_);
lean_inc(v_decls_938_);
lean_inc(v_lDecls_937_);
lean_inc(v_mvarCounter_936_);
lean_inc(v_lmvarCounter_935_);
lean_inc(v_levelAssignDepth_934_);
lean_inc(v_depth_933_);
lean_dec(v_mctx_925_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_946_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_eAssignment_941_, v_mvarId_920_, v_val_921_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 8, v___x_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_depth_933_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_levelAssignDepth_934_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_lmvarCounter_935_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_mvarCounter_936_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v_lDecls_937_);
lean_ctor_set(v_reuseFailAlloc_955_, 5, v_decls_938_);
lean_ctor_set(v_reuseFailAlloc_955_, 6, v_userNames_939_);
lean_ctor_set(v_reuseFailAlloc_955_, 7, v_lAssignment_940_);
lean_ctor_set(v_reuseFailAlloc_955_, 8, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_955_, 9, v_dAssignment_942_);
v___x_948_ = v_reuseFailAlloc_955_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_948_);
v___x_950_ = v___x_931_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_cache_926_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_zetaDeltaFVarIds_927_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_postponed_928_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_diag_929_);
v___x_950_ = v_reuseFailAlloc_954_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_st_ref_put(v___y_922_, v___x_950_);
v___x_952_ = lean_box(0);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_958_, lean_object* v_val_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_958_, v_val_959_, v___y_960_);
lean_dec(v___y_960_);
return v_res_962_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__4(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = l_Lean_Level_ofNat(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__4, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__4);
v___x_973_ = l_Lean_mkSort(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__6(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__5);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__7(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_976_ = lean_box(0);
v___x_977_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__6, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__6_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__6);
v___x_978_ = lean_unsigned_to_nat(2u);
v___x_979_ = lean_mk_empty_array_with_capacity(v___x_978_);
v___x_980_ = lean_array_push(v___x_979_, v___x_977_);
v___x_981_ = lean_array_push(v___x_980_, v___x_976_);
return v___x_981_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__13(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_box(0);
v___x_995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__12));
v___x_996_ = l_Lean_mkConst(v___x_995_, v___x_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f(lean_object* v_goal_997_, lean_object* v_target_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; 
lean_inc_ref(v_target_998_);
v___x_1011_ = l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(v_target_998_);
if (lean_obj_tag(v___x_1011_) == 1)
{
lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1078_; 
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v___x_1011_, 0);
lean_dec(v_unused_1079_);
v___x_1013_ = v___x_1011_;
v_isShared_1014_ = v_isSharedCheck_1078_;
goto v_resetjp_1012_;
}
else
{
lean_dec(v___x_1011_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1078_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3));
v___x_1016_ = lean_unsigned_to_nat(2u);
v___x_1017_ = lean_mk_empty_array_with_capacity(v___x_1016_);
v___x_1018_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__7);
v___x_1019_ = l_Lean_Meta_mkAppOptM(v___x_1015_, v___x_1018_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10));
v___x_1022_ = lean_array_push(v___x_1017_, v_a_1020_);
lean_inc_ref(v_target_998_);
v___x_1023_ = lean_array_push(v___x_1022_, v_target_998_);
v___x_1024_ = l_Lean_Meta_mkAppM(v___x_1021_, v___x_1023_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = l_Lean_Meta_Sym_shareCommon(v_a_1025_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = lean_box(0);
v___x_1029_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1027_, v___x_1028_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1044_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_n(v_a_1030_, 2);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__13, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__13_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__13);
v___x_1032_ = l_Lean_mkAppB(v___x_1031_, v_target_998_, v_a_1030_);
v___x_1033_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_997_, v___x_1032_, v_a_1007_);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v___x_1033_, 0);
lean_dec(v_unused_1045_);
v___x_1035_ = v___x_1033_;
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
else
{
lean_dec(v___x_1033_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = l_Lean_Expr_mvarId_x21(v_a_1030_);
lean_dec(v_a_1030_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1037_);
v___x_1039_ = v___x_1013_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1039_);
v___x_1041_ = v___x_1035_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_del_object(v___x_1013_);
lean_dec_ref(v_target_998_);
lean_dec(v_goal_997_);
v_a_1046_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1029_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1029_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_del_object(v___x_1013_);
lean_dec_ref(v_target_998_);
lean_dec(v_goal_997_);
v_a_1054_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1026_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1026_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_del_object(v___x_1013_);
lean_dec_ref(v_target_998_);
lean_dec(v_goal_997_);
v_a_1062_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1024_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1024_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref(v___x_1017_);
lean_del_object(v___x_1013_);
lean_dec_ref(v_target_998_);
lean_dec(v_goal_997_);
v_a_1070_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1019_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1019_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec(v___x_1011_);
lean_dec_ref(v_target_998_);
lean_dec(v_goal_997_);
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___boxed(lean_object* v_goal_1082_, lean_object* v_target_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f(v_goal_1082_, v_target_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0(lean_object* v_mvarId_1097_, lean_object* v_val_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_1097_, v_val_1098_, v___y_1107_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___boxed(lean_object* v_mvarId_1112_, lean_object* v_val_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0(v_mvarId_1112_, v_val_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_x_1128_, v_x_1129_, v_x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1132_, lean_object* v_x_1133_, size_t v_x_1134_, size_t v_x_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_1133_, v_x_1134_, v_x_1135_, v_x_1136_, v_x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
size_t v_x_9024__boxed_1145_; size_t v_x_9025__boxed_1146_; lean_object* v_res_1147_; 
v_x_9024__boxed_1145_ = lean_unbox_usize(v_x_1141_);
lean_dec(v_x_1141_);
v_x_9025__boxed_1146_ = lean_unbox_usize(v_x_1142_);
lean_dec(v_x_1142_);
v_res_1147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1139_, v_x_1140_, v_x_9024__boxed_1145_, v_x_9025__boxed_1146_, v_x_1143_, v_x_1144_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1148_, lean_object* v_n_1149_, lean_object* v_k_1150_, lean_object* v_v_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1149_, v_k_1150_, v_v_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1153_, size_t v_depth_1154_, lean_object* v_keys_1155_, lean_object* v_vals_1156_, lean_object* v_heq_1157_, lean_object* v_i_1158_, lean_object* v_entries_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1154_, v_keys_1155_, v_vals_1156_, v_i_1158_, v_entries_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1161_, lean_object* v_depth_1162_, lean_object* v_keys_1163_, lean_object* v_vals_1164_, lean_object* v_heq_1165_, lean_object* v_i_1166_, lean_object* v_entries_1167_){
_start:
{
size_t v_depth_boxed_1168_; lean_object* v_res_1169_; 
v_depth_boxed_1168_ = lean_unbox_usize(v_depth_1162_);
lean_dec(v_depth_1162_);
v_res_1169_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1161_, v_depth_boxed_1168_, v_keys_1163_, v_vals_1164_, v_heq_1165_, v_i_1166_, v_entries_1167_);
lean_dec_ref(v_vals_1164_);
lean_dec_ref(v_keys_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1171_, v_x_1172_, v_x_1173_, v_x_1174_);
return v___x_1175_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__0));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(lean_object* v_goal_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_backwardRules_1188_; lean_object* v_refl_1189_; lean_object* v___x_1190_; 
v_backwardRules_1188_ = lean_ctor_get(v_a_1180_, 0);
v_refl_1189_ = lean_ctor_get(v_backwardRules_1188_, 9);
lean_inc_ref(v_refl_1189_);
lean_inc(v_goal_1179_);
v___x_1190_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1179_, v_refl_1189_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1229_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1229_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1229_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
if (lean_obj_tag(v_a_1191_) == 1)
{
lean_object* v_mvarIds_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1224_; 
v_mvarIds_1195_ = lean_ctor_get(v_a_1191_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_a_1191_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1197_ = v_a_1191_;
v_isShared_1198_ = v_isSharedCheck_1224_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_mvarIds_1195_);
lean_dec(v_a_1191_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1224_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v_options_1206_; uint8_t v_hasTrace_1207_; 
v_options_1206_ = lean_ctor_get(v_a_1185_, 2);
v_hasTrace_1207_ = lean_ctor_get_uint8(v_options_1206_, sizeof(void*)*1);
if (v_hasTrace_1207_ == 0)
{
lean_dec(v_goal_1179_);
goto v___jp_1199_;
}
else
{
lean_object* v_inheritedTraceOptions_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_inheritedTraceOptions_1208_ = lean_ctor_get(v_a_1185_, 13);
v___x_1209_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_1210_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_1211_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1208_, v_options_1206_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_dec(v_goal_1179_);
goto v___jp_1199_;
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_goal_1179_);
v___x_1214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1209_, v___x_1214_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_dec_ref_known(v___x_1215_, 1);
goto v___jp_1199_;
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_del_object(v___x_1197_);
lean_dec(v_mvarIds_1195_);
lean_del_object(v___x_1193_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
v___jp_1199_:
{
lean_object* v___x_1201_; 
if (v_isShared_1198_ == 0)
{
v___x_1201_ = v___x_1197_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_mvarIds_1195_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1201_);
v___x_1203_ = v___x_1193_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
lean_dec(v_a_1191_);
lean_dec(v_goal_1179_);
v___x_1225_ = lean_box(0);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1225_);
v___x_1227_ = v___x_1193_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v_goal_1179_);
v_a_1230_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1190_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1190_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___boxed(lean_object* v_goal_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(v_goal_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v_a_1239_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f(lean_object* v_goal_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(v_goal_1248_, v_a_1249_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___boxed(lean_object* v_goal_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f(v_goal_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
return v_res_1275_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__0));
v___x_1278_ = l_Lean_stringToMessageData(v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(lean_object* v_scope_1279_, lean_object* v_e_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_lastLiftedPre_x3f_1286_; 
v_lastLiftedPre_x3f_1286_ = lean_ctor_get(v_scope_1279_, 2);
lean_inc(v_lastLiftedPre_x3f_1286_);
lean_dec_ref(v_scope_1279_);
if (lean_obj_tag(v_lastLiftedPre_x3f_1286_) == 1)
{
lean_object* v_val_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1344_; 
v_val_1287_ = lean_ctor_get(v_lastLiftedPre_x3f_1286_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_lastLiftedPre_x3f_1286_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1289_ = v_lastLiftedPre_x3f_1286_;
v_isShared_1290_ = v_isSharedCheck_1344_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_val_1287_);
lean_dec(v_lastLiftedPre_x3f_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1344_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v_lctx_1291_; lean_object* v___x_1292_; 
v_lctx_1291_ = lean_ctor_get(v_a_1281_, 2);
lean_inc_ref(v_lctx_1291_);
v___x_1292_ = lean_local_ctx_find(v_lctx_1291_, v_val_1287_);
if (lean_obj_tag(v___x_1292_) == 1)
{
lean_object* v_val_1293_; lean_object* v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; uint8_t v___x_1297_; 
v_val_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_val_1293_);
v___x_1294_ = l_Lean_LocalDecl_type(v_val_1293_);
v___x_1295_ = lean_ptr_addr(v_e_1280_);
v___x_1296_ = lean_ptr_addr(v___x_1294_);
lean_dec_ref(v___x_1294_);
v___x_1297_ = lean_usize_dec_eq(v___x_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_val_1293_);
lean_del_object(v___x_1289_);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v___x_1292_, 0);
lean_dec(v_unused_1306_);
v___x_1299_ = v___x_1292_;
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v___x_1292_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_box(0);
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1301_);
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
else
{
lean_object* v_options_1307_; uint8_t v_hasTrace_1308_; 
v_options_1307_ = lean_ctor_get(v_a_1283_, 2);
v_hasTrace_1308_ = lean_ctor_get_uint8(v_options_1307_, sizeof(void*)*1);
if (v_hasTrace_1308_ == 0)
{
lean_object* v___x_1310_; 
lean_dec(v_val_1293_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set_tag(v___x_1289_, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1292_);
v___x_1310_ = v___x_1289_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1292_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
else
{
lean_object* v_inheritedTraceOptions_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_inheritedTraceOptions_1312_ = lean_ctor_get(v_a_1283_, 13);
v___x_1313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_1314_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_1315_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1312_, v_options_1307_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1317_; 
lean_dec(v_val_1293_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set_tag(v___x_1289_, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1292_);
v___x_1317_ = v___x_1289_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1292_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_del_object(v___x_1289_);
v___x_1319_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1);
v___x_1320_ = l_Lean_LocalDecl_userName(v_val_1293_);
lean_dec(v_val_1293_);
v___x_1321_ = l_Lean_MessageData_ofName(v___x_1320_);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1319_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1313_, v___x_1322_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1330_ == 0)
{
lean_object* v_unused_1331_; 
v_unused_1331_ = lean_ctor_get(v___x_1323_, 0);
lean_dec(v_unused_1331_);
v___x_1325_ = v___x_1323_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_dec(v___x_1323_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1292_);
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1292_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref_known(v___x_1292_, 1);
v_a_1332_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1323_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1323_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
lean_dec(v___x_1292_);
v___x_1340_ = lean_box(0);
if (v_isShared_1290_ == 0)
{
lean_ctor_set_tag(v___x_1289_, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1340_);
v___x_1342_ = v___x_1289_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec(v_lastLiftedPre_x3f_1286_);
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___boxed(lean_object* v_scope_1347_, lean_object* v_e_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_1347_, v_e_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_e_1348_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f(lean_object* v_scope_1355_, lean_object* v_e_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_1355_, v_e_1356_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___boxed(lean_object* v_scope_1370_, lean_object* v_e_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f(v_scope_1370_, v_e_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec_ref(v_e_1371_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
lean_inc(v___y_1388_);
lean_inc(v___y_1387_);
lean_inc_ref(v___y_1386_);
v___x_1398_ = lean_apply_12(v_x_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, lean_box(0));
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(v_x_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(lean_object* v_mvarId_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___f_1427_; lean_object* v___x_1428_; 
lean_inc(v___y_1421_);
lean_inc_ref(v___y_1420_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc(v___y_1416_);
lean_inc_ref(v___y_1415_);
v___f_1427_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1427_, 0, v_x_1414_);
lean_closure_set(v___f_1427_, 1, v___y_1415_);
lean_closure_set(v___f_1427_, 2, v___y_1416_);
lean_closure_set(v___f_1427_, 3, v___y_1417_);
lean_closure_set(v___f_1427_, 4, v___y_1418_);
lean_closure_set(v___f_1427_, 5, v___y_1419_);
lean_closure_set(v___f_1427_, 6, v___y_1420_);
lean_closure_set(v___f_1427_, 7, v___y_1421_);
v___x_1428_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1413_, v___f_1427_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1428_) == 0)
{
return v___x_1428_;
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_1437_, lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1437_, v_x_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0(lean_object* v_00_u03b1_1452_, lean_object* v_mvarId_1453_, lean_object* v_x_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1453_, v_x_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___boxed(lean_object* v_00_u03b1_1468_, lean_object* v_mvarId_1469_, lean_object* v_x_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0(v_00_u03b1_1468_, v_mvarId_1469_, v_x_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0(uint8_t v___x_1489_, lean_object* v_scope_1490_, lean_object* v_rhs_1491_, lean_object* v_pre_1492_, lean_object* v_goal_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
if (v___x_1489_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v_goal_1493_);
lean_dec_ref(v_pre_1492_);
lean_dec_ref(v_rhs_1491_);
lean_dec_ref(v_scope_1490_);
v___x_1506_ = lean_box(0);
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
else
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_1490_, v_rhs_1491_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1545_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1545_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1545_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
if (lean_obj_tag(v_a_1509_) == 1)
{
lean_object* v_val_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_del_object(v___x_1511_);
v_val_1513_ = lean_ctor_get(v_a_1509_, 0);
lean_inc(v_val_1513_);
lean_dec_ref_known(v_a_1509_, 1);
v___x_1514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1));
v___x_1515_ = l_Lean_LocalDecl_toExpr(v_val_1513_);
v___x_1516_ = lean_unsigned_to_nat(3u);
v___x_1517_ = lean_mk_empty_array_with_capacity(v___x_1516_);
v___x_1518_ = lean_array_push(v___x_1517_, v_pre_1492_);
v___x_1519_ = lean_array_push(v___x_1518_, v_rhs_1491_);
v___x_1520_ = lean_array_push(v___x_1519_, v___x_1515_);
v___x_1521_ = l_Lean_Meta_mkAppM(v___x_1514_, v___x_1520_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1531_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1493_, v_a_1522_, v___y_1502_);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v___x_1523_, 0);
lean_dec(v_unused_1532_);
v___x_1525_ = v___x_1523_;
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
else
{
lean_dec(v___x_1523_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1527_);
v___x_1529_ = v___x_1525_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_goal_1493_);
v_a_1533_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1521_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1521_);
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
else
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
lean_dec(v_a_1509_);
lean_dec(v_goal_1493_);
lean_dec_ref(v_pre_1492_);
lean_dec_ref(v_rhs_1491_);
v___x_1541_ = lean_box(0);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1541_);
v___x_1543_ = v___x_1511_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
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
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_goal_1493_);
lean_dec_ref(v_pre_1492_);
lean_dec_ref(v_rhs_1491_);
v_a_1546_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1508_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1508_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___boxed(lean_object** _args){
lean_object* v___x_1554_ = _args[0];
lean_object* v_scope_1555_ = _args[1];
lean_object* v_rhs_1556_ = _args[2];
lean_object* v_pre_1557_ = _args[3];
lean_object* v_goal_1558_ = _args[4];
lean_object* v___y_1559_ = _args[5];
lean_object* v___y_1560_ = _args[6];
lean_object* v___y_1561_ = _args[7];
lean_object* v___y_1562_ = _args[8];
lean_object* v___y_1563_ = _args[9];
lean_object* v___y_1564_ = _args[10];
lean_object* v___y_1565_ = _args[11];
lean_object* v___y_1566_ = _args[12];
lean_object* v___y_1567_ = _args[13];
lean_object* v___y_1568_ = _args[14];
lean_object* v___y_1569_ = _args[15];
lean_object* v___y_1570_ = _args[16];
_start:
{
uint8_t v___x_7757__boxed_1571_; lean_object* v_res_1572_; 
v___x_7757__boxed_1571_ = lean_unbox(v___x_1554_);
v_res_1572_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0(v___x_7757__boxed_1571_, v_scope_1555_, v_rhs_1556_, v_pre_1557_, v_goal_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f(lean_object* v_scope_1573_, lean_object* v_goal_1574_, lean_object* v_00_u03b1_1575_, lean_object* v_pre_1576_, lean_object* v_rhs_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___y_1592_; lean_object* v___x_1593_; 
v___x_1590_ = l_Lean_Expr_isProp(v_00_u03b1_1575_);
v___x_1591_ = lean_box(v___x_1590_);
lean_inc(v_goal_1574_);
v___y_1592_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___boxed), 17, 5);
lean_closure_set(v___y_1592_, 0, v___x_1591_);
lean_closure_set(v___y_1592_, 1, v_scope_1573_);
lean_closure_set(v___y_1592_, 2, v_rhs_1577_);
lean_closure_set(v___y_1592_, 3, v_pre_1576_);
lean_closure_set(v___y_1592_, 4, v_goal_1574_);
v___x_1593_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1574_, v___y_1592_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___boxed(lean_object** _args){
lean_object* v_scope_1594_ = _args[0];
lean_object* v_goal_1595_ = _args[1];
lean_object* v_00_u03b1_1596_ = _args[2];
lean_object* v_pre_1597_ = _args[3];
lean_object* v_rhs_1598_ = _args[4];
lean_object* v_a_1599_ = _args[5];
lean_object* v_a_1600_ = _args[6];
lean_object* v_a_1601_ = _args[7];
lean_object* v_a_1602_ = _args[8];
lean_object* v_a_1603_ = _args[9];
lean_object* v_a_1604_ = _args[10];
lean_object* v_a_1605_ = _args[11];
lean_object* v_a_1606_ = _args[12];
lean_object* v_a_1607_ = _args[13];
lean_object* v_a_1608_ = _args[14];
lean_object* v_a_1609_ = _args[15];
lean_object* v_a_1610_ = _args[16];
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f(v_scope_1594_, v_goal_1595_, v_00_u03b1_1596_, v_pre_1597_, v_rhs_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec_ref(v_00_u03b1_1596_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0(lean_object* v_scope_1612_, lean_object* v_target_1613_, lean_object* v_goal_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_1612_, v_target_1613_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1648_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1648_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1648_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
if (lean_obj_tag(v_a_1628_) == 1)
{
lean_object* v_val_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1642_; 
lean_del_object(v___x_1630_);
v_val_1632_ = lean_ctor_get(v_a_1628_, 0);
lean_inc(v_val_1632_);
lean_dec_ref_known(v_a_1628_, 1);
v___x_1633_ = l_Lean_LocalDecl_toExpr(v_val_1632_);
v___x_1634_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1614_, v___x_1633_, v___y_1623_);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; 
v_unused_1643_ = lean_ctor_get(v___x_1634_, 0);
lean_dec(v_unused_1643_);
v___x_1636_ = v___x_1634_;
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
else
{
lean_dec(v___x_1634_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1638_);
v___x_1640_ = v___x_1636_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
lean_dec(v_a_1628_);
lean_dec(v_goal_1614_);
v___x_1644_ = lean_box(0);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1644_);
v___x_1646_ = v___x_1630_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
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
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_goal_1614_);
v_a_1649_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1627_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1627_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0___boxed(lean_object* v_scope_1657_, lean_object* v_target_1658_, lean_object* v_goal_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0(v_scope_1657_, v_target_1658_, v_goal_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v_target_1658_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f(lean_object* v_scope_1673_, lean_object* v_goal_1674_, lean_object* v_target_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___f_1688_; lean_object* v___x_1689_; 
lean_inc(v_goal_1674_);
v___f_1688_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0___boxed), 15, 3);
lean_closure_set(v___f_1688_, 0, v_scope_1673_);
lean_closure_set(v___f_1688_, 1, v_target_1675_);
lean_closure_set(v___f_1688_, 2, v_goal_1674_);
v___x_1689_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1674_, v___f_1688_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___boxed(lean_object* v_scope_1690_, lean_object* v_goal_1691_, lean_object* v_target_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f(v_scope_1690_, v_goal_1691_, v_target_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
lean_dec(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(lean_object* v_e_1706_, lean_object* v_i_1707_, lean_object* v_n_1708_, lean_object* v_v_1709_){
_start:
{
if (lean_obj_tag(v_e_1706_) == 5)
{
lean_object* v_fn_1710_; lean_object* v_arg_1711_; uint8_t v___y_1713_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_fn_1710_ = lean_ctor_get(v_e_1706_, 0);
v_arg_1711_ = lean_ctor_get(v_e_1706_, 1);
v___x_1715_ = lean_unsigned_to_nat(1u);
v___x_1716_ = lean_nat_add(v_i_1707_, v___x_1715_);
v___x_1717_ = lean_nat_dec_eq(v_n_1708_, v___x_1716_);
lean_dec(v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___y_1721_; size_t v___x_1723_; size_t v___x_1724_; uint8_t v___x_1725_; 
v___x_1718_ = lean_nat_sub(v_n_1708_, v___x_1715_);
lean_inc_ref(v_fn_1710_);
v___x_1719_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(v_fn_1710_, v_i_1707_, v___x_1718_, v_v_1709_);
lean_dec(v___x_1718_);
v___x_1723_ = lean_ptr_addr(v_fn_1710_);
v___x_1724_ = lean_ptr_addr(v___x_1719_);
v___x_1725_ = lean_usize_dec_eq(v___x_1723_, v___x_1724_);
if (v___x_1725_ == 0)
{
v___y_1721_ = v___x_1725_;
goto v___jp_1720_;
}
else
{
size_t v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = lean_ptr_addr(v_arg_1711_);
v___x_1727_ = lean_usize_dec_eq(v___x_1726_, v___x_1726_);
v___y_1721_ = v___x_1727_;
goto v___jp_1720_;
}
v___jp_1720_:
{
if (v___y_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_inc_ref(v_arg_1711_);
lean_dec_ref_known(v_e_1706_, 2);
v___x_1722_ = l_Lean_Expr_app___override(v___x_1719_, v_arg_1711_);
return v___x_1722_;
}
else
{
lean_dec_ref(v___x_1719_);
return v_e_1706_;
}
}
}
else
{
size_t v___x_1728_; uint8_t v___x_1729_; 
v___x_1728_ = lean_ptr_addr(v_fn_1710_);
v___x_1729_ = lean_usize_dec_eq(v___x_1728_, v___x_1728_);
if (v___x_1729_ == 0)
{
v___y_1713_ = v___x_1729_;
goto v___jp_1712_;
}
else
{
size_t v___x_1730_; size_t v___x_1731_; uint8_t v___x_1732_; 
v___x_1730_ = lean_ptr_addr(v_arg_1711_);
v___x_1731_ = lean_ptr_addr(v_v_1709_);
v___x_1732_ = lean_usize_dec_eq(v___x_1730_, v___x_1731_);
v___y_1713_ = v___x_1732_;
goto v___jp_1712_;
}
}
v___jp_1712_:
{
if (v___y_1713_ == 0)
{
lean_object* v___x_1714_; 
lean_inc_ref(v_fn_1710_);
lean_dec_ref_known(v_e_1706_, 2);
v___x_1714_ = l_Lean_Expr_app___override(v_fn_1710_, v_v_1709_);
return v___x_1714_;
}
else
{
lean_dec_ref(v_v_1709_);
return v_e_1706_;
}
}
}
else
{
lean_dec_ref(v_v_1709_);
return v_e_1706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg___boxed(lean_object* v_e_1733_, lean_object* v_i_1734_, lean_object* v_n_1735_, lean_object* v_v_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(v_e_1733_, v_i_1734_, v_n_1735_, v_v_1736_);
lean_dec(v_n_1735_);
lean_dec(v_i_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(lean_object* v_rhs_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
uint8_t v___x_1751_; 
v___x_1751_ = l_Lean_Expr_hasMVar(v_rhs_1743_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec_ref(v_rhs_1743_);
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
else
{
lean_object* v_n_1754_; lean_object* v___x_1755_; uint8_t v___y_1757_; uint8_t v___x_1804_; 
v_n_1754_ = l_Lean_Expr_getAppNumArgs(v_rhs_1743_);
v___x_1755_ = lean_unsigned_to_nat(7u);
v___x_1804_ = lean_nat_dec_lt(v___x_1755_, v_n_1754_);
if (v___x_1804_ == 0)
{
v___y_1757_ = v___x_1804_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1805_ = l_Lean_Expr_getAppFn(v_rhs_1743_);
v___x_1806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1));
v___x_1807_ = l_Lean_Expr_isConstOf(v___x_1805_, v___x_1806_);
lean_dec_ref(v___x_1805_);
v___y_1757_ = v___x_1807_;
goto v___jp_1756_;
}
v___jp_1756_:
{
if (v___y_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_dec(v_n_1754_);
lean_dec_ref(v_rhs_1743_);
v___x_1758_ = lean_box(0);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v_prog_1763_; lean_object* v___x_1764_; 
v___x_1760_ = lean_nat_sub(v_n_1754_, v___x_1755_);
v___x_1761_ = lean_unsigned_to_nat(1u);
v___x_1762_ = lean_nat_sub(v___x_1760_, v___x_1761_);
lean_dec(v___x_1760_);
v_prog_1763_ = l_Lean_Expr_getRevArg_x21(v_rhs_1743_, v___x_1762_);
lean_inc_ref(v_prog_1763_);
v___x_1764_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_prog_1763_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1795_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1795_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1795_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
size_t v___x_1769_; size_t v___x_1770_; uint8_t v___x_1771_; 
v___x_1769_ = lean_ptr_addr(v_prog_1763_);
lean_dec_ref(v_prog_1763_);
v___x_1770_ = lean_ptr_addr(v_a_1765_);
v___x_1771_ = lean_usize_dec_eq(v___x_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_del_object(v___x_1767_);
v___x_1772_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(v_rhs_1743_, v___x_1755_, v_n_1754_, v_a_1765_);
lean_dec(v_n_1754_);
v___x_1773_ = l_Lean_Meta_Sym_shareCommon(v___x_1772_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1782_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_a_1774_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1778_);
v___x_1780_ = v___x_1776_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_a_1783_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1773_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1773_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
lean_dec(v_a_1765_);
lean_dec(v_n_1754_);
lean_dec_ref(v_rhs_1743_);
v___x_1791_ = lean_box(0);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1791_);
v___x_1793_ = v___x_1767_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
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
lean_dec_ref(v_prog_1763_);
lean_dec(v_n_1754_);
lean_dec_ref(v_rhs_1743_);
v_a_1796_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1764_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1764_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___boxed(lean_object* v_rhs_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_rhs_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f(lean_object* v_rhs_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_rhs_1817_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___boxed(lean_object* v_rhs_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f(v_rhs_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1845_, lean_object* v_a_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___y_1855_; lean_object* v___x_1858_; uint8_t v_debug_1859_; 
v___x_1858_ = lean_st_ref_get(v___y_1848_);
v_debug_1859_ = lean_ctor_get_uint8(v___x_1858_, sizeof(void*)*11);
lean_dec(v___x_1858_);
if (v_debug_1859_ == 0)
{
v___y_1855_ = v___y_1848_;
goto v___jp_1854_;
}
else
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1845_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref_known(v___x_1860_, 1);
v___x_1861_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_dec_ref_known(v___x_1861_, 1);
v___y_1855_ = v___y_1848_;
goto v___jp_1854_;
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v_a_1846_);
lean_dec_ref(v_f_1845_);
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
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
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v_a_1846_);
lean_dec_ref(v_f_1845_);
v_a_1870_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1860_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1860_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
v___jp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = l_Lean_Expr_app___override(v_f_1845_, v_a_1846_);
v___x_1857_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1856_, v___y_1855_);
return v___x_1857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1878_, lean_object* v_a_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_f_1878_, v_a_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0(lean_object* v_args_1888_, lean_object* v_endIdx_1889_, lean_object* v_b_1890_, lean_object* v_i_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
uint8_t v___x_1904_; 
v___x_1904_ = lean_nat_dec_le(v_endIdx_1889_, v_i_1891_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = l_Lean_instInhabitedExpr;
v___x_1906_ = lean_array_get_borrowed(v___x_1905_, v_args_1888_, v_i_1891_);
lean_inc(v___x_1906_);
v___x_1907_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_b_1890_, v___x_1906_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v___x_1909_ = lean_unsigned_to_nat(1u);
v___x_1910_ = lean_nat_add(v_i_1891_, v___x_1909_);
lean_dec(v_i_1891_);
v_b_1890_ = v_a_1908_;
v_i_1891_ = v___x_1910_;
goto _start;
}
else
{
lean_dec(v_i_1891_);
return v___x_1907_;
}
}
else
{
lean_object* v___x_1912_; 
lean_dec(v_i_1891_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_b_1890_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0___boxed(lean_object* v_args_1913_, lean_object* v_endIdx_1914_, lean_object* v_b_1915_, lean_object* v_i_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0(v_args_1913_, v_endIdx_1914_, v_b_1915_, v_i_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v_endIdx_1914_);
lean_dec_ref(v_args_1913_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(lean_object* v_f_1930_, lean_object* v_args_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_array_get_size(v_args_1931_);
v___x_1946_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0(v_args_1931_, v___x_1945_, v_f_1930_, v___x_1944_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0___boxed(lean_object* v_f_1947_, lean_object* v_args_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_f_1947_, v_args_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec_ref(v_args_1948_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(lean_object* v_goal_1962_, lean_object* v_target_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = l_Lean_Expr_cleanupAnnotations(v_target_1963_);
v___x_1980_ = l_Lean_Expr_isApp(v___x_1979_);
if (v___x_1980_ == 0)
{
lean_dec_ref(v___x_1979_);
lean_dec(v_goal_1962_);
goto v___jp_1976_;
}
else
{
lean_object* v_arg_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v_arg_1981_ = lean_ctor_get(v___x_1979_, 1);
lean_inc_ref(v_arg_1981_);
v___x_1982_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1979_);
v___x_1983_ = l_Lean_Expr_isApp(v___x_1982_);
if (v___x_1983_ == 0)
{
lean_dec_ref(v___x_1982_);
lean_dec_ref(v_arg_1981_);
lean_dec(v_goal_1962_);
goto v___jp_1976_;
}
else
{
lean_object* v_arg_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v_arg_1984_ = lean_ctor_get(v___x_1982_, 1);
lean_inc_ref(v_arg_1984_);
v___x_1985_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1982_);
v___x_1986_ = l_Lean_Expr_isApp(v___x_1985_);
if (v___x_1986_ == 0)
{
lean_dec_ref(v___x_1985_);
lean_dec_ref(v_arg_1984_);
lean_dec_ref(v_arg_1981_);
lean_dec(v_goal_1962_);
goto v___jp_1976_;
}
else
{
lean_object* v_arg_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v_arg_1987_ = lean_ctor_get(v___x_1985_, 1);
lean_inc_ref(v_arg_1987_);
v___x_1988_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1985_);
v___x_1989_ = l_Lean_Expr_isApp(v___x_1988_);
if (v___x_1989_ == 0)
{
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_arg_1987_);
lean_dec_ref(v_arg_1984_);
lean_dec_ref(v_arg_1981_);
lean_dec(v_goal_1962_);
goto v___jp_1976_;
}
else
{
lean_object* v_arg_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v_arg_1990_ = lean_ctor_get(v___x_1988_, 1);
lean_inc_ref(v_arg_1990_);
v___x_1991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1988_);
v___x_1992_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10));
v___x_1993_ = l_Lean_Expr_isConstOf(v___x_1991_, v___x_1992_);
if (v___x_1993_ == 0)
{
lean_dec_ref(v___x_1991_);
lean_dec_ref(v_arg_1990_);
lean_dec_ref(v_arg_1987_);
lean_dec_ref(v_arg_1984_);
lean_dec_ref(v_arg_1981_);
lean_dec(v_goal_1962_);
goto v___jp_1976_;
}
else
{
lean_object* v___x_1994_; 
lean_inc_ref(v_arg_1990_);
v___x_1994_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1990_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1996_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1994_, 1);
lean_inc_ref(v_arg_1984_);
v___x_1996_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1984_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
lean_inc_ref(v_arg_1981_);
v___x_1998_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1981_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc_n(v_a_1999_, 2);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2000_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_a_1999_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2060_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2060_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2060_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___y_2006_; lean_object* v___y_2042_; uint8_t v___y_2043_; lean_object* v___y_2052_; 
if (lean_obj_tag(v_a_2001_) == 0)
{
v___y_2052_ = v_a_1999_;
goto v___jp_2051_;
}
else
{
lean_object* v_val_2059_; 
lean_dec(v_a_1999_);
v_val_2059_ = lean_ctor_get(v_a_2001_, 0);
lean_inc(v_val_2059_);
lean_dec_ref_known(v_a_2001_, 1);
v___y_2052_ = v_val_2059_;
goto v___jp_2051_;
}
v___jp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2007_ = lean_unsigned_to_nat(4u);
v___x_2008_ = lean_mk_empty_array_with_capacity(v___x_2007_);
v___x_2009_ = lean_array_push(v___x_2008_, v_a_1995_);
v___x_2010_ = lean_array_push(v___x_2009_, v_arg_1987_);
v___x_2011_ = lean_array_push(v___x_2010_, v_a_1997_);
v___x_2012_ = lean_array_push(v___x_2011_, v___y_2006_);
v___x_2013_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v___x_1991_, v___x_2012_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec_ref(v___x_2012_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v___x_2015_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_1962_, v_a_2014_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2024_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_a_2016_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2020_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
v_a_2025_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2015_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2015_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_goal_1962_);
v_a_2033_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2013_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2013_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
v___jp_2041_:
{
if (v___y_2043_ == 0)
{
lean_del_object(v___x_2003_);
lean_dec_ref(v_arg_1981_);
v___y_2006_ = v___y_2042_;
goto v___jp_2005_;
}
else
{
size_t v___x_2044_; size_t v___x_2045_; uint8_t v___x_2046_; 
v___x_2044_ = lean_ptr_addr(v_arg_1981_);
lean_dec_ref(v_arg_1981_);
v___x_2045_ = lean_ptr_addr(v___y_2042_);
v___x_2046_ = lean_usize_dec_eq(v___x_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_del_object(v___x_2003_);
v___y_2006_ = v___y_2042_;
goto v___jp_2005_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
lean_dec_ref(v___y_2042_);
lean_dec(v_a_1997_);
lean_dec(v_a_1995_);
lean_dec_ref(v___x_1991_);
lean_dec_ref(v_arg_1987_);
lean_dec(v_goal_1962_);
v___x_2047_ = lean_box(0);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2047_);
v___x_2049_ = v___x_2003_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
v___jp_2051_:
{
size_t v___x_2053_; size_t v___x_2054_; uint8_t v___x_2055_; 
v___x_2053_ = lean_ptr_addr(v_arg_1990_);
lean_dec_ref(v_arg_1990_);
v___x_2054_ = lean_ptr_addr(v_a_1995_);
v___x_2055_ = lean_usize_dec_eq(v___x_2053_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_dec_ref(v_arg_1984_);
v___y_2042_ = v___y_2052_;
v___y_2043_ = v___x_2055_;
goto v___jp_2041_;
}
else
{
size_t v___x_2056_; size_t v___x_2057_; uint8_t v___x_2058_; 
v___x_2056_ = lean_ptr_addr(v_arg_1984_);
lean_dec_ref(v_arg_1984_);
v___x_2057_ = lean_ptr_addr(v_a_1997_);
v___x_2058_ = lean_usize_dec_eq(v___x_2056_, v___x_2057_);
v___y_2042_ = v___y_2052_;
v___y_2043_ = v___x_2058_;
goto v___jp_2041_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec(v_a_1995_);
lean_dec_ref(v___x_1991_);
lean_dec_ref(v_arg_1990_);
lean_dec_ref(v_arg_1987_);
lean_dec_ref(v_arg_1984_);
lean_dec_ref(v_arg_1981_);
lean_dec(v_goal_1962_);
v_a_2061_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2000_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2000_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_a_1997_);
lean_dec(v_a_1995_);
lean_dec_ref(v___x_1991_);
lean_dec_ref(v_arg_1990_);
lean_dec_ref(v_arg_1987_);
lean_dec_ref(v_arg_1984_);
lean_dec_ref(v_arg_1981_);
lean_dec(v_goal_1962_);
v_a_2069_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_1998_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_1998_);
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
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v_a_1995_);
lean_dec_ref(v___x_1991_);
lean_dec_ref(v_arg_1990_);
lean_dec_ref(v_arg_1987_);
lean_dec_ref(v_arg_1984_);
lean_dec_ref(v_arg_1981_);
lean_dec(v_goal_1962_);
v_a_2077_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_1996_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_1996_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v___x_1991_);
lean_dec_ref(v_arg_1990_);
lean_dec_ref(v_arg_1987_);
lean_dec_ref(v_arg_1984_);
lean_dec_ref(v_arg_1981_);
lean_dec(v_goal_1962_);
v_a_2085_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_1994_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_1994_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
}
}
}
v___jp_1976_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_box(0);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f___boxed(lean_object* v_goal_2093_, lean_object* v_target_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(v_goal_2093_, v_target_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1(lean_object* v_f_2108_, lean_object* v_a_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_f_2108_, v_a_2109_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2123_, lean_object* v_a_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1(v_f_2123_, v_a_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2137_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__2));
v___x_2145_ = l_Lean_stringToMessageData(v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(lean_object* v_goal_2146_, lean_object* v_pre_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = l_Lean_Expr_cleanupAnnotations(v_pre_2147_);
v___x_2164_ = l_Lean_Expr_isApp(v___x_2163_);
if (v___x_2164_ == 0)
{
lean_dec_ref(v___x_2163_);
lean_dec(v_goal_2146_);
goto v___jp_2160_;
}
else
{
lean_object* v_arg_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v_arg_2165_ = lean_ctor_get(v___x_2163_, 1);
lean_inc_ref(v_arg_2165_);
v___x_2166_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2163_);
v___x_2167_ = l_Lean_Expr_isApp(v___x_2166_);
if (v___x_2167_ == 0)
{
lean_dec_ref(v___x_2166_);
lean_dec_ref(v_arg_2165_);
lean_dec(v_goal_2146_);
goto v___jp_2160_;
}
else
{
lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2166_);
v___x_2169_ = l_Lean_Expr_isApp(v___x_2168_);
if (v___x_2169_ == 0)
{
lean_dec_ref(v___x_2168_);
lean_dec_ref(v_arg_2165_);
lean_dec(v_goal_2146_);
goto v___jp_2160_;
}
else
{
lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2170_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2168_);
v___x_2171_ = l_Lean_Expr_isApp(v___x_2170_);
if (v___x_2171_ == 0)
{
lean_dec_ref(v___x_2170_);
lean_dec_ref(v_arg_2165_);
lean_dec(v_goal_2146_);
goto v___jp_2160_;
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2170_);
v___x_2173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_2174_ = l_Lean_Expr_isConstOf(v___x_2172_, v___x_2173_);
lean_dec_ref(v___x_2172_);
if (v___x_2174_ == 0)
{
lean_dec_ref(v_arg_2165_);
lean_dec(v_goal_2146_);
goto v___jp_2160_;
}
else
{
lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2175_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3));
v___x_2176_ = l_Lean_Expr_isAppOf(v_arg_2165_, v___x_2175_);
lean_dec_ref(v_arg_2165_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec(v_goal_2146_);
v___x_2177_ = lean_box(0);
v___x_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
return v___x_2178_;
}
else
{
lean_object* v_backwardRules_2179_; lean_object* v_meetTop_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_backwardRules_2179_ = lean_ctor_get(v_a_2148_, 0);
v_meetTop_2180_ = lean_ctor_get(v_backwardRules_2179_, 10);
v___x_2181_ = lean_box(0);
lean_inc(v_goal_2146_);
lean_inc_ref(v_meetTop_2180_);
v___x_2182_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_meetTop_2180_, v_goal_2146_, v___x_2181_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2209_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2185_ = v___x_2182_;
v_isShared_2186_ = v_isSharedCheck_2209_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2182_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2209_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; 
if (lean_obj_tag(v_a_2183_) == 1)
{
lean_object* v_mvarIds_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2208_; 
v_mvarIds_2196_ = lean_ctor_get(v_a_2183_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_a_2183_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2198_ = v_a_2183_;
v_isShared_2199_ = v_isSharedCheck_2208_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_mvarIds_2196_);
lean_dec(v_a_2183_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2208_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
if (lean_obj_tag(v_mvarIds_2196_) == 1)
{
lean_object* v_tail_2200_; 
v_tail_2200_ = lean_ctor_get(v_mvarIds_2196_, 1);
if (lean_obj_tag(v_tail_2200_) == 0)
{
lean_object* v_head_2201_; lean_object* v___x_2203_; 
lean_dec(v_goal_2146_);
v_head_2201_ = lean_ctor_get(v_mvarIds_2196_, 0);
lean_inc(v_head_2201_);
lean_dec_ref_known(v_mvarIds_2196_, 2);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v_head_2201_);
v___x_2203_ = v___x_2198_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_head_2201_);
v___x_2203_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2205_; 
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2203_);
v___x_2205_ = v___x_2185_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2196_, 2);
lean_del_object(v___x_2198_);
lean_del_object(v___x_2185_);
v___y_2188_ = v_a_2155_;
v___y_2189_ = v_a_2156_;
v___y_2190_ = v_a_2157_;
v___y_2191_ = v_a_2158_;
goto v___jp_2187_;
}
}
else
{
lean_del_object(v___x_2198_);
lean_dec(v_mvarIds_2196_);
lean_del_object(v___x_2185_);
v___y_2188_ = v_a_2155_;
v___y_2189_ = v_a_2156_;
v___y_2190_ = v_a_2157_;
v___y_2191_ = v_a_2158_;
goto v___jp_2187_;
}
}
}
else
{
lean_del_object(v___x_2185_);
lean_dec(v_a_2183_);
v___y_2188_ = v_a_2155_;
v___y_2189_ = v_a_2156_;
v___y_2190_ = v_a_2157_;
v___y_2191_ = v_a_2158_;
goto v___jp_2187_;
}
v___jp_2187_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2192_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3);
v___x_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2193_, 0, v_goal_2146_);
v___x_2194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2194_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
return v___x_2195_;
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_goal_2146_);
v_a_2210_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2182_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2182_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
}
}
}
}
v___jp_2160_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___boxed(lean_object* v_goal_2218_, lean_object* v_pre_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(v_goal_2218_, v_pre_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(lean_object* v_goal_2240_, lean_object* v_pre_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v___x_2257_; uint8_t v___x_2258_; 
v___x_2257_ = l_Lean_Expr_cleanupAnnotations(v_pre_2241_);
v___x_2258_ = l_Lean_Expr_isApp(v___x_2257_);
if (v___x_2258_ == 0)
{
lean_dec_ref(v___x_2257_);
lean_dec(v_goal_2240_);
goto v___jp_2254_;
}
else
{
lean_object* v_arg_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v_arg_2259_ = lean_ctor_get(v___x_2257_, 1);
lean_inc_ref(v_arg_2259_);
v___x_2260_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2257_);
v___x_2261_ = l_Lean_Expr_isApp(v___x_2260_);
if (v___x_2261_ == 0)
{
lean_dec_ref(v___x_2260_);
lean_dec_ref(v_arg_2259_);
lean_dec(v_goal_2240_);
goto v___jp_2254_;
}
else
{
lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2260_);
v___x_2263_ = l_Lean_Expr_isApp(v___x_2262_);
if (v___x_2263_ == 0)
{
lean_dec_ref(v___x_2262_);
lean_dec_ref(v_arg_2259_);
lean_dec(v_goal_2240_);
goto v___jp_2254_;
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2264_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2262_);
v___x_2265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_2266_ = l_Lean_Expr_isConstOf(v___x_2264_, v___x_2265_);
lean_dec_ref(v___x_2264_);
if (v___x_2266_ == 0)
{
lean_dec_ref(v_arg_2259_);
lean_dec(v_goal_2240_);
goto v___jp_2254_;
}
else
{
uint8_t v___x_2267_; 
v___x_2267_ = l_Lean_Expr_isTrue(v_arg_2259_);
if (v___x_2267_ == 0)
{
lean_object* v_backwardRules_2268_; lean_object* v_ofPropPreIntro_2269_; lean_object* v___x_2270_; 
v_backwardRules_2268_ = lean_ctor_get(v_a_2242_, 0);
v_ofPropPreIntro_2269_ = lean_ctor_get(v_backwardRules_2268_, 3);
lean_inc_ref(v_ofPropPreIntro_2269_);
v___x_2270_ = l_Lean_Elab_Tactic_VCGen_introPre(v_ofPropPreIntro_2269_, v_goal_2240_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2279_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2279_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2279_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2275_, 0, v_a_2271_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2275_);
v___x_2277_ = v___x_2273_;
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
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
v_a_2280_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2270_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2270_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec(v_goal_2240_);
v___x_2288_ = lean_box(0);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
}
}
}
v___jp_2254_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___boxed(lean_object* v_goal_2290_, lean_object* v_pre_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(v_goal_2290_, v_pre_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(lean_object* v_goal_2305_, lean_object* v_pre_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = l_Lean_Expr_cleanupAnnotations(v_pre_2306_);
v___x_2326_ = l_Lean_Expr_isApp(v___x_2325_);
if (v___x_2326_ == 0)
{
lean_dec_ref(v___x_2325_);
lean_dec(v_goal_2305_);
goto v___jp_2319_;
}
else
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2325_);
v___x_2328_ = l_Lean_Expr_isApp(v___x_2327_);
if (v___x_2328_ == 0)
{
lean_dec_ref(v___x_2327_);
lean_dec(v_goal_2305_);
goto v___jp_2319_;
}
else
{
lean_object* v_arg_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_arg_2329_ = lean_ctor_get(v___x_2327_, 1);
lean_inc_ref(v_arg_2329_);
v___x_2330_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2327_);
v___x_2331_ = l_Lean_Expr_isApp(v___x_2330_);
if (v___x_2331_ == 0)
{
lean_dec_ref(v___x_2330_);
lean_dec_ref(v_arg_2329_);
lean_dec(v_goal_2305_);
goto v___jp_2319_;
}
else
{
lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2330_);
v___x_2333_ = l_Lean_Expr_isApp(v___x_2332_);
if (v___x_2333_ == 0)
{
lean_dec_ref(v___x_2332_);
lean_dec_ref(v_arg_2329_);
lean_dec(v_goal_2305_);
goto v___jp_2319_;
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2332_);
v___x_2335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_2336_ = l_Lean_Expr_isConstOf(v___x_2334_, v___x_2335_);
lean_dec_ref(v___x_2334_);
if (v___x_2336_ == 0)
{
lean_dec_ref(v_arg_2329_);
lean_dec(v_goal_2305_);
goto v___jp_2319_;
}
else
{
lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = l_Lean_Expr_cleanupAnnotations(v_arg_2329_);
v___x_2338_ = l_Lean_Expr_isApp(v___x_2337_);
if (v___x_2338_ == 0)
{
lean_dec_ref(v___x_2337_);
lean_dec(v_goal_2305_);
goto v___jp_2322_;
}
else
{
lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2337_);
v___x_2340_ = l_Lean_Expr_isApp(v___x_2339_);
if (v___x_2340_ == 0)
{
lean_dec_ref(v___x_2339_);
lean_dec(v_goal_2305_);
goto v___jp_2322_;
}
else
{
lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2339_);
v___x_2342_ = l_Lean_Expr_isApp(v___x_2341_);
if (v___x_2342_ == 0)
{
lean_dec_ref(v___x_2341_);
lean_dec(v_goal_2305_);
goto v___jp_2322_;
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2341_);
v___x_2344_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_2345_ = l_Lean_Expr_isConstOf(v___x_2343_, v___x_2344_);
lean_dec_ref(v___x_2343_);
if (v___x_2345_ == 0)
{
lean_dec(v_goal_2305_);
goto v___jp_2322_;
}
else
{
lean_object* v_backwardRules_2346_; lean_object* v_ofPropMeetPreIntro_2347_; lean_object* v___x_2348_; 
v_backwardRules_2346_ = lean_ctor_get(v_a_2307_, 0);
v_ofPropMeetPreIntro_2347_ = lean_ctor_get(v_backwardRules_2346_, 4);
lean_inc_ref(v_ofPropMeetPreIntro_2347_);
v___x_2348_ = l_Lean_Elab_Tactic_VCGen_introPre(v_ofPropMeetPreIntro_2347_, v_goal_2305_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2357_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_a_2349_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2353_);
v___x_2355_ = v___x_2351_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2348_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2348_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
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
}
}
}
}
v___jp_2319_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
v___jp_2322_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_box(0);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
return v___x_2324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f___boxed(lean_object* v_goal_2366_, lean_object* v_pre_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(v_goal_2366_, v_pre_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
return v_res_2380_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__2));
v___x_2388_ = l_Lean_stringToMessageData(v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(lean_object* v_goal_2389_, lean_object* v_pre_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1));
v___x_2404_ = lean_unsigned_to_nat(4u);
v___x_2405_ = l_Lean_Expr_isAppOfArity(v_pre_2390_, v___x_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec(v_goal_2389_);
v___x_2406_ = lean_box(0);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
return v___x_2407_;
}
else
{
lean_object* v_backwardRules_2408_; lean_object* v_iSupPreIntro_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_backwardRules_2408_ = lean_ctor_get(v_a_2391_, 0);
v_iSupPreIntro_2409_ = lean_ctor_get(v_backwardRules_2408_, 5);
v___x_2410_ = lean_box(0);
lean_inc(v_goal_2389_);
lean_inc_ref(v_iSupPreIntro_2409_);
v___x_2411_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_iSupPreIntro_2409_, v_goal_2389_, v___x_2410_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2438_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2438_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2438_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; 
if (lean_obj_tag(v_a_2412_) == 1)
{
lean_object* v_mvarIds_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2437_; 
v_mvarIds_2425_ = lean_ctor_get(v_a_2412_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_a_2412_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2427_ = v_a_2412_;
v_isShared_2428_ = v_isSharedCheck_2437_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_mvarIds_2425_);
lean_dec(v_a_2412_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2437_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
if (lean_obj_tag(v_mvarIds_2425_) == 1)
{
lean_object* v_tail_2429_; 
v_tail_2429_ = lean_ctor_get(v_mvarIds_2425_, 1);
if (lean_obj_tag(v_tail_2429_) == 0)
{
lean_object* v_head_2430_; lean_object* v___x_2432_; 
lean_dec(v_goal_2389_);
v_head_2430_ = lean_ctor_get(v_mvarIds_2425_, 0);
lean_inc(v_head_2430_);
lean_dec_ref_known(v_mvarIds_2425_, 2);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_head_2430_);
v___x_2432_ = v___x_2427_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_head_2430_);
v___x_2432_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2434_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2432_);
v___x_2434_ = v___x_2414_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2425_, 2);
lean_del_object(v___x_2427_);
lean_del_object(v___x_2414_);
v___y_2417_ = v_a_2398_;
v___y_2418_ = v_a_2399_;
v___y_2419_ = v_a_2400_;
v___y_2420_ = v_a_2401_;
goto v___jp_2416_;
}
}
else
{
lean_del_object(v___x_2427_);
lean_dec(v_mvarIds_2425_);
lean_del_object(v___x_2414_);
v___y_2417_ = v_a_2398_;
v___y_2418_ = v_a_2399_;
v___y_2419_ = v_a_2400_;
v___y_2420_ = v_a_2401_;
goto v___jp_2416_;
}
}
}
else
{
lean_del_object(v___x_2414_);
lean_dec(v_a_2412_);
v___y_2417_ = v_a_2398_;
v___y_2418_ = v_a_2399_;
v___y_2419_ = v_a_2400_;
v___y_2420_ = v_a_2401_;
goto v___jp_2416_;
}
v___jp_2416_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2421_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3);
v___x_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2422_, 0, v_goal_2389_);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2423_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v___x_2424_;
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec(v_goal_2389_);
v_a_2439_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2411_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2411_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___boxed(lean_object* v_goal_2447_, lean_object* v_pre_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(v_goal_2447_, v_pre_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec_ref(v_pre_2448_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(lean_object* v_goal_2462_, lean_object* v_00_u03b1_2463_, lean_object* v_pre_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
uint8_t v___x_2477_; 
v___x_2477_ = l_Lean_Expr_isProp(v_00_u03b1_2463_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_dec(v_goal_2462_);
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
return v___x_2479_;
}
else
{
lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3));
v___x_2481_ = l_Lean_Expr_isAppOf(v_pre_2464_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v_backwardRules_2482_; lean_object* v_propPreIntro_2483_; lean_object* v___x_2484_; 
v_backwardRules_2482_ = lean_ctor_get(v_a_2465_, 0);
v_propPreIntro_2483_ = lean_ctor_get(v_backwardRules_2482_, 2);
lean_inc_ref(v_propPreIntro_2483_);
v___x_2484_ = l_Lean_Elab_Tactic_VCGen_introPre(v_propPreIntro_2483_, v_goal_2462_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2493_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2493_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2493_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_a_2485_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2489_);
v___x_2491_ = v___x_2487_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
v_a_2494_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2484_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2484_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
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
else
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_dec(v_goal_2462_);
v___x_2502_ = lean_box(0);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f___boxed(lean_object* v_goal_2504_, lean_object* v_00_u03b1_2505_, lean_object* v_pre_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(v_goal_2504_, v_00_u03b1_2505_, v_pre_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec_ref(v_pre_2506_);
lean_dec_ref(v_00_u03b1_2505_);
return v_res_2519_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__0));
v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
return v___x_2522_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4(void){
_start:
{
uint8_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = 0;
v___x_2529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3));
v___x_2530_ = l_Lean_MessageData_ofConstName(v___x_2529_, v___x_2528_);
return v___x_2530_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4);
v___x_2532_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1);
v___x_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v___x_2531_);
return v___x_2533_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__6));
v___x_2536_ = l_Lean_stringToMessageData(v___x_2535_);
return v___x_2536_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7);
v___x_2538_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5);
v___x_2539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
lean_ctor_set(v___x_2539_, 1, v___x_2537_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(lean_object* v_goal_2540_, lean_object* v_pre_2541_, lean_object* v_target_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; uint8_t v___x_2593_; 
lean_inc_ref(v_pre_2541_);
v___x_2593_ = l_Lean_Expr_isTrue(v_pre_2541_);
if (v___x_2593_ == 0)
{
v___y_2556_ = v_a_2548_;
v___y_2557_ = v_a_2549_;
v___y_2558_ = v_a_2550_;
v___y_2559_ = v_a_2551_;
v___y_2560_ = v_a_2552_;
v___y_2561_ = v_a_2553_;
goto v___jp_2555_;
}
else
{
lean_object* v_backwardRules_2594_; lean_object* v_truePreIntro_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_dec_ref(v_pre_2541_);
v_backwardRules_2594_ = lean_ctor_get(v_a_2543_, 0);
v_truePreIntro_2595_ = lean_ctor_get(v_backwardRules_2594_, 6);
v___x_2596_ = lean_box(0);
lean_inc_ref(v_truePreIntro_2595_);
v___x_2597_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_truePreIntro_2595_, v_goal_2540_, v___x_2596_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2633_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2633_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2633_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; 
if (lean_obj_tag(v_a_2598_) == 1)
{
lean_object* v_mvarIds_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2632_; 
v_mvarIds_2621_ = lean_ctor_get(v_a_2598_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_a_2598_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2623_ = v_a_2598_;
v_isShared_2624_ = v_isSharedCheck_2632_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_mvarIds_2621_);
lean_dec(v_a_2598_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2632_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
if (lean_obj_tag(v_mvarIds_2621_) == 1)
{
lean_object* v_tail_2625_; 
v_tail_2625_ = lean_ctor_get(v_mvarIds_2621_, 1);
if (lean_obj_tag(v_tail_2625_) == 0)
{
lean_object* v___x_2627_; 
lean_dec_ref(v_target_2542_);
if (v_isShared_2624_ == 0)
{
v___x_2627_ = v___x_2623_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_mvarIds_2621_);
v___x_2627_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2629_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2627_);
v___x_2629_ = v___x_2600_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2621_, 2);
lean_del_object(v___x_2623_);
lean_del_object(v___x_2600_);
v___y_2603_ = v_a_2548_;
v___y_2604_ = v_a_2549_;
v___y_2605_ = v_a_2550_;
v___y_2606_ = v_a_2551_;
v___y_2607_ = v_a_2552_;
v___y_2608_ = v_a_2553_;
goto v___jp_2602_;
}
}
else
{
lean_del_object(v___x_2623_);
lean_dec(v_mvarIds_2621_);
lean_del_object(v___x_2600_);
v___y_2603_ = v_a_2548_;
v___y_2604_ = v_a_2549_;
v___y_2605_ = v_a_2550_;
v___y_2606_ = v_a_2551_;
v___y_2607_ = v_a_2552_;
v___y_2608_ = v_a_2553_;
goto v___jp_2602_;
}
}
}
else
{
lean_del_object(v___x_2600_);
lean_dec(v_a_2598_);
v___y_2603_ = v_a_2548_;
v___y_2604_ = v_a_2549_;
v___y_2605_ = v_a_2550_;
v___y_2606_ = v_a_2551_;
v___y_2607_ = v_a_2552_;
v___y_2608_ = v_a_2553_;
goto v___jp_2602_;
}
v___jp_2602_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
v___x_2609_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8);
v___x_2610_ = l_Lean_indentExpr(v_target_2542_);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2611_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec_ref(v_target_2542_);
v_a_2634_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2597_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2597_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
v___jp_2555_:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(v_goal_2540_, v_target_2542_, v_pre_2541_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2584_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2584_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2584_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
if (lean_obj_tag(v_a_2563_) == 1)
{
lean_object* v_val_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2579_; 
v_val_2567_ = lean_ctor_get(v_a_2563_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_a_2563_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2569_ = v_a_2563_;
v_isShared_2570_ = v_isSharedCheck_2579_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_val_2567_);
lean_dec(v_a_2563_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2579_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2571_ = lean_box(0);
v___x_2572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2572_, 0, v_val_2567_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2572_);
v___x_2574_ = v___x_2569_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2576_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2574_);
v___x_2576_ = v___x_2565_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
lean_dec(v_a_2563_);
v___x_2580_ = lean_box(0);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2580_);
v___x_2582_ = v___x_2565_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
v_a_2585_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2562_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2562_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___boxed(lean_object* v_goal_2642_, lean_object* v_pre_2643_, lean_object* v_target_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(v_goal_2642_, v_pre_2643_, v_target_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(lean_object* v_scope_2658_, lean_object* v_goal_2659_, lean_object* v_00_u03b1_2660_, lean_object* v_pre_2661_, lean_object* v_target_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v_g_2676_; lean_object* v_g_2683_; lean_object* v_h_2684_; lean_object* v___x_2702_; 
lean_inc_ref(v_pre_2661_);
lean_inc(v_goal_2659_);
v___x_2702_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(v_goal_2659_, v_pre_2661_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
if (lean_obj_tag(v_a_2703_) == 1)
{
lean_object* v_val_2704_; 
lean_dec_ref(v_target_2662_);
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
v_val_2704_ = lean_ctor_get(v_a_2703_, 0);
lean_inc(v_val_2704_);
lean_dec_ref_known(v_a_2703_, 1);
v_g_2676_ = v_val_2704_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2705_; 
lean_dec(v_a_2703_);
lean_inc_ref(v_pre_2661_);
lean_inc(v_goal_2659_);
v___x_2705_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(v_goal_2659_, v_pre_2661_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
if (lean_obj_tag(v_a_2706_) == 1)
{
lean_object* v_val_2707_; lean_object* v_fst_2708_; lean_object* v_snd_2709_; 
lean_dec_ref(v_target_2662_);
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
v_val_2707_ = lean_ctor_get(v_a_2706_, 0);
lean_inc(v_val_2707_);
lean_dec_ref_known(v_a_2706_, 1);
v_fst_2708_ = lean_ctor_get(v_val_2707_, 0);
lean_inc(v_fst_2708_);
v_snd_2709_ = lean_ctor_get(v_val_2707_, 1);
lean_inc(v_snd_2709_);
lean_dec(v_val_2707_);
v_g_2683_ = v_fst_2708_;
v_h_2684_ = v_snd_2709_;
goto v___jp_2682_;
}
else
{
lean_object* v___x_2710_; 
lean_dec(v_a_2706_);
lean_inc_ref(v_pre_2661_);
lean_inc(v_goal_2659_);
v___x_2710_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(v_goal_2659_, v_pre_2661_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
if (lean_obj_tag(v_a_2711_) == 1)
{
lean_object* v_val_2712_; lean_object* v_fst_2713_; lean_object* v_snd_2714_; 
lean_dec_ref(v_target_2662_);
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
v_val_2712_ = lean_ctor_get(v_a_2711_, 0);
lean_inc(v_val_2712_);
lean_dec_ref_known(v_a_2711_, 1);
v_fst_2713_ = lean_ctor_get(v_val_2712_, 0);
lean_inc(v_fst_2713_);
v_snd_2714_ = lean_ctor_get(v_val_2712_, 1);
lean_inc(v_snd_2714_);
lean_dec(v_val_2712_);
v_g_2683_ = v_fst_2713_;
v_h_2684_ = v_snd_2714_;
goto v___jp_2682_;
}
else
{
lean_object* v___x_2715_; 
lean_dec(v_a_2711_);
lean_inc(v_goal_2659_);
v___x_2715_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(v_goal_2659_, v_pre_2661_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
if (lean_obj_tag(v_a_2716_) == 1)
{
lean_object* v_val_2717_; 
lean_dec_ref(v_target_2662_);
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
v_val_2717_ = lean_ctor_get(v_a_2716_, 0);
lean_inc(v_val_2717_);
lean_dec_ref_known(v_a_2716_, 1);
v_g_2676_ = v_val_2717_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2718_; 
lean_dec(v_a_2716_);
lean_inc(v_goal_2659_);
v___x_2718_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_goal_2659_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2718_, 1);
if (lean_obj_tag(v_a_2719_) == 1)
{
lean_object* v_val_2720_; 
lean_dec_ref(v_target_2662_);
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
v_val_2720_ = lean_ctor_get(v_a_2719_, 0);
lean_inc(v_val_2720_);
lean_dec_ref_known(v_a_2719_, 1);
v_g_2676_ = v_val_2720_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2721_; 
lean_dec(v_a_2719_);
lean_inc_ref(v_pre_2661_);
lean_inc(v_goal_2659_);
v___x_2721_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(v_goal_2659_, v_pre_2661_, v_target_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2759_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2759_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2759_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
if (lean_obj_tag(v_a_2722_) == 1)
{
lean_object* v_val_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2737_; 
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
v_val_2726_ = lean_ctor_get(v_a_2722_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_a_2722_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2728_ = v_a_2722_;
v_isShared_2729_ = v_isSharedCheck_2737_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_val_2726_);
lean_dec(v_a_2722_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2737_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v_scope_2658_);
lean_ctor_set(v___x_2730_, 1, v_val_2726_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2730_);
v___x_2732_ = v___x_2728_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2734_; 
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2732_);
v___x_2734_ = v___x_2724_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
else
{
lean_object* v___x_2738_; 
lean_del_object(v___x_2724_);
lean_dec(v_a_2722_);
v___x_2738_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(v_goal_2659_, v_00_u03b1_2660_, v_pre_2661_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_);
lean_dec_ref(v_pre_2661_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2750_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2750_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2750_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
if (lean_obj_tag(v_a_2739_) == 1)
{
lean_object* v_val_2743_; lean_object* v_fst_2744_; lean_object* v_snd_2745_; 
lean_del_object(v___x_2741_);
v_val_2743_ = lean_ctor_get(v_a_2739_, 0);
lean_inc(v_val_2743_);
lean_dec_ref_known(v_a_2739_, 1);
v_fst_2744_ = lean_ctor_get(v_val_2743_, 0);
lean_inc(v_fst_2744_);
v_snd_2745_ = lean_ctor_get(v_val_2743_, 1);
lean_inc(v_snd_2745_);
lean_dec(v_val_2743_);
v_g_2683_ = v_fst_2744_;
v_h_2684_ = v_snd_2745_;
goto v___jp_2682_;
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
lean_dec(v_a_2739_);
lean_dec_ref(v_scope_2658_);
v___x_2746_ = lean_box(0);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2746_);
v___x_2748_ = v___x_2741_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec_ref(v_scope_2658_);
v_a_2751_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2738_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2738_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
lean_dec_ref(v_scope_2658_);
v_a_2760_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2721_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2721_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref(v_target_2662_);
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
lean_dec_ref(v_scope_2658_);
v_a_2768_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2718_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2718_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref(v_target_2662_);
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
lean_dec_ref(v_scope_2658_);
v_a_2776_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2715_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2715_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec_ref(v_target_2662_);
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
lean_dec_ref(v_scope_2658_);
v_a_2784_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2710_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2710_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec_ref(v_target_2662_);
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
lean_dec_ref(v_scope_2658_);
v_a_2792_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2705_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2705_);
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
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec_ref(v_target_2662_);
lean_dec_ref(v_pre_2661_);
lean_dec(v_goal_2659_);
lean_dec_ref(v_scope_2658_);
v_a_2800_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2702_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2702_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
v___jp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2677_ = lean_box(0);
v___x_2678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2678_, 0, v_g_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2679_, 0, v_scope_2658_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
v___jp_2682_:
{
lean_object* v_specs_2685_; lean_object* v_jps_2686_; lean_object* v_nextDeclIdx_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2700_; 
v_specs_2685_ = lean_ctor_get(v_scope_2658_, 0);
v_jps_2686_ = lean_ctor_get(v_scope_2658_, 1);
v_nextDeclIdx_2687_ = lean_ctor_get(v_scope_2658_, 3);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_scope_2658_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; 
v_unused_2701_ = lean_ctor_get(v_scope_2658_, 2);
lean_dec(v_unused_2701_);
v___x_2689_ = v_scope_2658_;
v_isShared_2690_ = v_isSharedCheck_2700_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_nextDeclIdx_2687_);
lean_inc(v_jps_2686_);
lean_inc(v_specs_2685_);
lean_dec(v_scope_2658_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2700_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2691_, 0, v_h_2684_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 2, v___x_2691_);
v___x_2693_ = v___x_2689_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_specs_2685_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_jps_2686_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2699_, 3, v_nextDeclIdx_2687_);
v___x_2693_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2695_, 0, v_g_2683_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2693_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
return v___x_2698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f___boxed(lean_object** _args){
lean_object* v_scope_2808_ = _args[0];
lean_object* v_goal_2809_ = _args[1];
lean_object* v_00_u03b1_2810_ = _args[2];
lean_object* v_pre_2811_ = _args[3];
lean_object* v_target_2812_ = _args[4];
lean_object* v_a_2813_ = _args[5];
lean_object* v_a_2814_ = _args[6];
lean_object* v_a_2815_ = _args[7];
lean_object* v_a_2816_ = _args[8];
lean_object* v_a_2817_ = _args[9];
lean_object* v_a_2818_ = _args[10];
lean_object* v_a_2819_ = _args[11];
lean_object* v_a_2820_ = _args[12];
lean_object* v_a_2821_ = _args[13];
lean_object* v_a_2822_ = _args[14];
lean_object* v_a_2823_ = _args[15];
lean_object* v_a_2824_ = _args[16];
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(v_scope_2808_, v_goal_2809_, v_00_u03b1_2810_, v_pre_2811_, v_target_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec_ref(v_00_u03b1_2810_);
return v_res_2825_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0(void){
_start:
{
lean_object* v___x_2826_; lean_object* v_dummy_2827_; 
v___x_2826_ = lean_box(0);
v_dummy_2827_ = l_Lean_Expr_sort___override(v___x_2826_);
return v_dummy_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(lean_object* v_goal_2828_, lean_object* v_info_2829_, lean_object* v_prog_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v_head_2843_; lean_object* v_args_2844_; lean_object* v_excessArgs_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_head_2843_ = lean_ctor_get(v_info_2829_, 0);
lean_inc_ref(v_head_2843_);
v_args_2844_ = lean_ctor_get(v_info_2829_, 1);
lean_inc_ref(v_args_2844_);
v_excessArgs_2845_ = lean_ctor_get(v_info_2829_, 2);
lean_inc_ref(v_excessArgs_2845_);
lean_dec_ref(v_info_2829_);
v___x_2846_ = lean_unsigned_to_nat(7u);
v___x_2847_ = lean_array_set(v_args_2844_, v___x_2846_, v_prog_2830_);
v___x_2848_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_head_2843_, v___x_2847_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec_ref(v___x_2847_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v___x_2850_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_a_2849_, v_excessArgs_2845_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec_ref(v_excessArgs_2845_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
lean_inc(v_goal_2828_);
v___x_2852_ = l_Lean_MVarId_getType(v_goal_2828_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v_dummy_2854_; lean_object* v_nargs_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc_n(v_a_2853_, 2);
lean_dec_ref_known(v___x_2852_, 1);
v_dummy_2854_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0);
v_nargs_2855_ = l_Lean_Expr_getAppNumArgs(v_a_2853_);
lean_inc(v_nargs_2855_);
v___x_2856_ = lean_mk_array(v_nargs_2855_, v_dummy_2854_);
v___x_2857_ = lean_unsigned_to_nat(1u);
v___x_2858_ = lean_nat_sub(v_nargs_2855_, v___x_2857_);
lean_dec(v_nargs_2855_);
v___x_2859_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2853_, v___x_2856_, v___x_2858_);
v___x_2860_ = l_Lean_Expr_getAppFn(v_a_2853_);
lean_dec(v_a_2853_);
v___x_2861_ = lean_array_get_size(v___x_2859_);
v___x_2862_ = lean_nat_sub(v___x_2861_, v___x_2857_);
v___x_2863_ = lean_array_set(v___x_2859_, v___x_2862_, v_a_2851_);
lean_dec(v___x_2862_);
v___x_2864_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v___x_2860_, v___x_2863_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec_ref(v___x_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2828_, v_a_2865_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
return v___x_2866_;
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v_goal_2828_);
v_a_2867_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2864_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2864_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec(v_a_2851_);
lean_dec(v_goal_2828_);
v_a_2875_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2852_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2852_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec(v_goal_2828_);
v_a_2883_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2850_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2850_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec_ref(v_excessArgs_2845_);
lean_dec(v_goal_2828_);
v_a_2891_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2848_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2848_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___boxed(lean_object* v_goal_2899_, lean_object* v_info_2900_, lean_object* v_prog_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_2899_, v_info_2900_, v_prog_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(lean_object* v_goal_2915_, lean_object* v_info_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_2916_);
if (lean_obj_tag(v___x_2929_) == 10)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = l_Lean_Expr_consumeMData(v___x_2929_);
lean_dec_ref_known(v___x_2929_, 2);
v___x_2931_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_2915_, v_info_2916_, v___x_2930_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2940_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2934_ = v___x_2931_;
v_isShared_2935_ = v_isSharedCheck_2940_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2940_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2936_, 0, v_a_2932_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 0, v___x_2936_);
v___x_2938_ = v___x_2934_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
v_a_2941_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2931_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2931_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
else
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
lean_dec_ref(v___x_2929_);
lean_dec_ref(v_info_2916_);
lean_dec(v_goal_2915_);
v___x_2949_ = lean_box(0);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f___boxed(lean_object* v_goal_2951_, lean_object* v_info_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(v_goal_2951_, v_info_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
lean_dec(v_a_2963_);
lean_dec_ref(v_a_2962_);
lean_dec(v_a_2961_);
lean_dec_ref(v_a_2960_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
lean_dec(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object* v_revArgs_2966_, lean_object* v_start_2967_, lean_object* v_b_2968_, lean_object* v_i_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
uint8_t v___x_2977_; 
v___x_2977_ = lean_nat_dec_le(v_i_2969_, v_start_2967_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; lean_object* v_i_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2978_ = lean_unsigned_to_nat(1u);
v_i_2979_ = lean_nat_sub(v_i_2969_, v___x_2978_);
lean_dec(v_i_2969_);
v___x_2980_ = l_Lean_instInhabitedExpr;
v___x_2981_ = lean_array_get_borrowed(v___x_2980_, v_revArgs_2966_, v_i_2979_);
lean_inc(v___x_2981_);
v___x_2982_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_b_2968_, v___x_2981_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v_b_2968_ = v_a_2983_;
v_i_2969_ = v_i_2979_;
goto _start;
}
else
{
lean_dec(v_i_2979_);
return v___x_2982_;
}
}
else
{
lean_object* v___x_2985_; 
lean_dec(v_i_2969_);
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_b_2968_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_revArgs_2986_, lean_object* v_start_2987_, lean_object* v_b_2988_, lean_object* v_i_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2986_, v_start_2987_, v_b_2988_, v_i_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v_start_2987_);
lean_dec_ref(v_revArgs_2986_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(lean_object* v_f_2998_, lean_object* v_revArgs_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_unsigned_to_nat(0u);
v___x_3013_ = lean_array_get_size(v_revArgs_2999_);
v___x_3014_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2999_, v___x_3012_, v_f_2998_, v___x_3013_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0___boxed(lean_object* v_f_3015_, lean_object* v_revArgs_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_f_3015_, v_revArgs_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec_ref(v_revArgs_3016_);
return v_res_3029_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__0));
v___x_3032_ = l_Lean_stringToMessageData(v___x_3031_);
return v___x_3032_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__2));
v___x_3035_ = l_Lean_stringToMessageData(v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(lean_object* v_goal_3036_, lean_object* v_info_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3037_);
v___x_3051_ = l_Lean_Expr_getAppFn(v___x_3050_);
if (lean_obj_tag(v___x_3051_) == 8)
{
lean_object* v_declName_3052_; lean_object* v_type_3053_; lean_object* v_value_3054_; lean_object* v_body_3055_; uint8_t v_nondep_3056_; lean_object* v___x_3057_; 
v_declName_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc_n(v_declName_3052_, 2);
v_type_3053_ = lean_ctor_get(v___x_3051_, 1);
lean_inc_ref(v_type_3053_);
v_value_3054_ = lean_ctor_get(v___x_3051_, 2);
lean_inc_ref(v_value_3054_);
v_body_3055_ = lean_ctor_get(v___x_3051_, 3);
lean_inc_ref(v_body_3055_);
v_nondep_3056_ = lean_ctor_get_uint8(v___x_3051_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v___x_3051_, 4);
v___x_3057_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg(v_declName_3052_, v_value_3054_, v_a_3038_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v_appArgs_3060_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; uint8_t v___x_3114_; 
lean_dec_ref_known(v___x_3057_, 1);
v___x_3058_ = l_Lean_Expr_getAppNumArgs(v___x_3050_);
v___x_3059_ = lean_mk_empty_array_with_capacity(v___x_3058_);
lean_dec(v___x_3058_);
v_appArgs_3060_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3050_, v___x_3059_);
v___x_3114_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable(v_value_3054_);
if (v___x_3114_ == 0)
{
lean_object* v_options_3115_; lean_object* v_inheritedTraceOptions_3116_; uint8_t v_hasTrace_3117_; uint8_t v___x_3118_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; 
v_options_3115_ = lean_ctor_get(v_a_3047_, 2);
v_inheritedTraceOptions_3116_ = lean_ctor_get(v_a_3047_, 13);
v_hasTrace_3117_ = lean_ctor_get_uint8(v_options_3115_, sizeof(void*)*1);
v___x_3118_ = 1;
if (v_hasTrace_3117_ == 0)
{
v___y_3120_ = v_a_3038_;
v___y_3121_ = v_a_3039_;
v___y_3122_ = v_a_3040_;
v___y_3123_ = v_a_3041_;
v___y_3124_ = v_a_3042_;
v___y_3125_ = v_a_3043_;
v___y_3126_ = v_a_3044_;
v___y_3127_ = v_a_3045_;
v___y_3128_ = v_a_3046_;
v___y_3129_ = v_a_3047_;
v___y_3130_ = v_a_3048_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3229_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_3230_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_3231_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3116_, v_options_3115_, v___x_3230_);
if (v___x_3231_ == 0)
{
v___y_3120_ = v_a_3038_;
v___y_3121_ = v_a_3039_;
v___y_3122_ = v_a_3040_;
v___y_3123_ = v_a_3041_;
v___y_3124_ = v_a_3042_;
v___y_3125_ = v_a_3043_;
v___y_3126_ = v_a_3044_;
v___y_3127_ = v_a_3045_;
v___y_3128_ = v_a_3046_;
v___y_3129_ = v_a_3047_;
v___y_3130_ = v_a_3048_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3232_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3);
lean_inc(v_declName_3052_);
v___x_3233_ = l_Lean_MessageData_ofName(v_declName_3052_);
v___x_3234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3229_, v___x_3234_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_dec_ref_known(v___x_3235_, 1);
v___y_3120_ = v_a_3038_;
v___y_3121_ = v_a_3039_;
v___y_3122_ = v_a_3040_;
v___y_3123_ = v_a_3041_;
v___y_3124_ = v_a_3042_;
v___y_3125_ = v_a_3043_;
v___y_3126_ = v_a_3044_;
v___y_3127_ = v_a_3045_;
v___y_3128_ = v_a_3046_;
v___y_3129_ = v_a_3047_;
v___y_3130_ = v_a_3048_;
goto v___jp_3119_;
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec_ref(v_appArgs_3060_);
lean_dec_ref(v_body_3055_);
lean_dec_ref(v_value_3054_);
lean_dec_ref(v_type_3053_);
lean_dec(v_declName_3052_);
lean_dec_ref(v_info_3037_);
lean_dec(v_goal_3036_);
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
v___jp_3119_:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_body_3055_, v_appArgs_3060_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec_ref(v_appArgs_3060_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v_head_3133_; lean_object* v_args_3134_; lean_object* v_excessArgs_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3131_, 1);
v_head_3133_ = lean_ctor_get(v_info_3037_, 0);
lean_inc_ref(v_head_3133_);
v_args_3134_ = lean_ctor_get(v_info_3037_, 1);
lean_inc_ref(v_args_3134_);
v_excessArgs_3135_ = lean_ctor_get(v_info_3037_, 2);
lean_inc_ref(v_excessArgs_3135_);
lean_dec_ref(v_info_3037_);
v___x_3136_ = lean_unsigned_to_nat(7u);
v___x_3137_ = lean_array_set(v_args_3134_, v___x_3136_, v_a_3132_);
v___x_3138_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_head_3133_, v___x_3137_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec_ref(v___x_3137_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3140_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___x_3138_, 1);
v___x_3140_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_a_3139_, v_excessArgs_3135_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec_ref(v_excessArgs_3135_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3142_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
lean_inc(v_goal_3036_);
v___x_3142_ = l_Lean_MVarId_getType(v_goal_3036_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v_dummy_3144_; lean_object* v_nargs_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc_n(v_a_3143_, 2);
lean_dec_ref_known(v___x_3142_, 1);
v_dummy_3144_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0);
v_nargs_3145_ = l_Lean_Expr_getAppNumArgs(v_a_3143_);
lean_inc(v_nargs_3145_);
v___x_3146_ = lean_mk_array(v_nargs_3145_, v_dummy_3144_);
v___x_3147_ = lean_unsigned_to_nat(1u);
v___x_3148_ = lean_nat_sub(v_nargs_3145_, v___x_3147_);
lean_dec(v_nargs_3145_);
v___x_3149_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3143_, v___x_3146_, v___x_3148_);
v___x_3150_ = l_Lean_Expr_getAppFn(v_a_3143_);
lean_dec(v_a_3143_);
v___x_3151_ = lean_array_get_size(v___x_3149_);
v___x_3152_ = lean_nat_sub(v___x_3151_, v___x_3147_);
v___x_3153_ = lean_array_set(v___x_3149_, v___x_3152_, v_a_3141_);
lean_dec(v___x_3152_);
v___x_3154_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v___x_3150_, v___x_3153_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec_ref(v___x_3153_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v___x_3156_ = l_Lean_Expr_letE___override(v_declName_3052_, v_type_3053_, v_value_3054_, v_a_3155_, v_nondep_3056_);
v___x_3157_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_3036_, v___x_3156_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___x_3157_, 1);
v___x_3159_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0));
v___x_3160_ = l_Lean_Meta_Sym_intros(v_a_3158_, v___x_3159_, v___x_3118_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3172_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3172_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3172_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
if (lean_obj_tag(v_a_3161_) == 1)
{
lean_object* v_mvarId_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
v_mvarId_3165_ = lean_ctor_get(v_a_3161_, 1);
lean_inc(v_mvarId_3165_);
lean_dec_ref_known(v_a_3161_, 2);
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_mvarId_3165_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3166_);
v___x_3168_ = v___x_3163_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_del_object(v___x_3163_);
lean_dec(v_a_3161_);
v___x_3170_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1);
v___x_3171_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3170_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
return v___x_3171_;
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
v_a_3173_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3160_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3160_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
v_a_3181_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3157_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3157_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec_ref(v_value_3054_);
lean_dec_ref(v_type_3053_);
lean_dec(v_declName_3052_);
lean_dec(v_goal_3036_);
v_a_3189_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3154_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3154_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v_a_3141_);
lean_dec_ref(v_value_3054_);
lean_dec_ref(v_type_3053_);
lean_dec(v_declName_3052_);
lean_dec(v_goal_3036_);
v_a_3197_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3142_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3142_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref(v_value_3054_);
lean_dec_ref(v_type_3053_);
lean_dec(v_declName_3052_);
lean_dec(v_goal_3036_);
v_a_3205_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3140_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3140_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref(v_excessArgs_3135_);
lean_dec_ref(v_value_3054_);
lean_dec_ref(v_type_3053_);
lean_dec(v_declName_3052_);
lean_dec(v_goal_3036_);
v_a_3213_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3138_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3138_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec_ref(v_value_3054_);
lean_dec_ref(v_type_3053_);
lean_dec(v_declName_3052_);
lean_dec_ref(v_info_3037_);
lean_dec(v_goal_3036_);
v_a_3221_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3131_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3131_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
else
{
lean_object* v_options_3244_; uint8_t v_hasTrace_3245_; 
lean_dec_ref(v_type_3053_);
v_options_3244_ = lean_ctor_get(v_a_3047_, 2);
v_hasTrace_3245_ = lean_ctor_get_uint8(v_options_3244_, sizeof(void*)*1);
if (v_hasTrace_3245_ == 0)
{
lean_dec(v_declName_3052_);
v___y_3062_ = v_a_3038_;
v___y_3063_ = v_a_3039_;
v___y_3064_ = v_a_3040_;
v___y_3065_ = v_a_3041_;
v___y_3066_ = v_a_3042_;
v___y_3067_ = v_a_3043_;
v___y_3068_ = v_a_3044_;
v___y_3069_ = v_a_3045_;
v___y_3070_ = v_a_3046_;
v___y_3071_ = v_a_3047_;
v___y_3072_ = v_a_3048_;
goto v___jp_3061_;
}
else
{
lean_object* v_inheritedTraceOptions_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v_inheritedTraceOptions_3246_ = lean_ctor_get(v_a_3047_, 13);
v___x_3247_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_3248_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_3249_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3246_, v_options_3244_, v___x_3248_);
if (v___x_3249_ == 0)
{
lean_dec(v_declName_3052_);
v___y_3062_ = v_a_3038_;
v___y_3063_ = v_a_3039_;
v___y_3064_ = v_a_3040_;
v___y_3065_ = v_a_3041_;
v___y_3066_ = v_a_3042_;
v___y_3067_ = v_a_3043_;
v___y_3068_ = v_a_3044_;
v___y_3069_ = v_a_3045_;
v___y_3070_ = v_a_3046_;
v___y_3071_ = v_a_3047_;
v___y_3072_ = v_a_3048_;
goto v___jp_3061_;
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3250_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11);
v___x_3251_ = l_Lean_MessageData_ofName(v_declName_3052_);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3247_, v___x_3252_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_dec_ref_known(v___x_3253_, 1);
v___y_3062_ = v_a_3038_;
v___y_3063_ = v_a_3039_;
v___y_3064_ = v_a_3040_;
v___y_3065_ = v_a_3041_;
v___y_3066_ = v_a_3042_;
v___y_3067_ = v_a_3043_;
v___y_3068_ = v_a_3044_;
v___y_3069_ = v_a_3045_;
v___y_3070_ = v_a_3046_;
v___y_3071_ = v_a_3047_;
v___y_3072_ = v_a_3048_;
goto v___jp_3061_;
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v_appArgs_3060_);
lean_dec_ref(v_body_3055_);
lean_dec_ref(v_value_3054_);
lean_dec_ref(v_info_3037_);
lean_dec(v_goal_3036_);
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3253_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
}
v___jp_3061_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3073_ = lean_unsigned_to_nat(1u);
v___x_3074_ = lean_mk_empty_array_with_capacity(v___x_3073_);
v___x_3075_ = lean_array_push(v___x_3074_, v_value_3054_);
v___x_3076_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_3055_, v___x_3075_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v___x_3078_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_a_3077_, v_appArgs_3060_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec_ref(v_appArgs_3060_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3080_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3079_);
lean_dec_ref_known(v___x_3078_, 1);
v___x_3080_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3036_, v_info_3037_, v_a_3079_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3089_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3089_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3089_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v_a_3081_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v___x_3085_);
v___x_3087_ = v___x_3083_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
v_a_3090_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3080_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3080_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec_ref(v_info_3037_);
lean_dec(v_goal_3036_);
v_a_3098_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3078_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3078_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec_ref(v_appArgs_3060_);
lean_dec_ref(v_info_3037_);
lean_dec(v_goal_3036_);
v_a_3106_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3076_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3076_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref(v_body_3055_);
lean_dec_ref(v_value_3054_);
lean_dec_ref(v_type_3053_);
lean_dec(v_declName_3052_);
lean_dec_ref(v___x_3050_);
lean_dec_ref(v_info_3037_);
lean_dec(v_goal_3036_);
v_a_3262_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3057_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3057_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_dec_ref(v___x_3051_);
lean_dec_ref(v___x_3050_);
lean_dec_ref(v_info_3037_);
lean_dec(v_goal_3036_);
v___x_3270_ = lean_box(0);
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3270_);
return v___x_3271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___boxed(lean_object* v_goal_3272_, lean_object* v_info_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(v_goal_3272_, v_info_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0(lean_object* v_revArgs_3287_, lean_object* v_start_3288_, lean_object* v_b_3289_, lean_object* v_i_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_3287_, v_start_3288_, v_b_3289_, v_i_3290_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___boxed(lean_object* v_revArgs_3304_, lean_object* v_start_3305_, lean_object* v_b_3306_, lean_object* v_i_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0(v_revArgs_3304_, v_start_3305_, v_b_3306_, v_i_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v_start_3305_);
lean_dec_ref(v_revArgs_3304_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0(lean_object* v_arg_3321_, lean_object* v___x_3322_, lean_object* v___x_3323_, uint8_t v___x_3324_, lean_object* v_a_3325_, lean_object* v_fn_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v___x_3337_; 
lean_inc_ref(v_arg_3321_);
v___x_3337_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_arg_3321_, v___x_3322_, v___x_3323_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3337_, 1);
v___x_3339_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3339_, 0, v___x_3324_);
lean_ctor_set_uint8(v___x_3339_, 1, v___x_3324_);
v___x_3340_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_a_3325_, v_fn_3326_, v_arg_3321_, v___x_3339_, v_a_3338_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
return v___x_3340_;
}
else
{
lean_dec_ref(v_fn_3326_);
lean_dec_ref(v_a_3325_);
lean_dec_ref(v_arg_3321_);
return v___x_3337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0___boxed(lean_object* v_arg_3341_, lean_object* v___x_3342_, lean_object* v___x_3343_, lean_object* v___x_3344_, lean_object* v_a_3345_, lean_object* v_fn_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
uint8_t v___x_23412__boxed_3357_; lean_object* v_res_3358_; 
v___x_23412__boxed_3357_ = lean_unbox(v___x_3344_);
v_res_3358_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0(v_arg_3341_, v___x_3342_, v___x_3343_, v___x_23412__boxed_3357_, v_a_3345_, v_fn_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec(v___x_3343_);
lean_dec(v___x_3342_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1(uint8_t v___x_3362_, lean_object* v_goal_3363_, lean_object* v_args_3364_, lean_object* v_excessArgs_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
if (v___x_3362_ == 0)
{
lean_object* v_hypSimpMethods_3378_; 
v_hypSimpMethods_3378_ = lean_ctor_get(v___y_3366_, 2);
if (lean_obj_tag(v_hypSimpMethods_3378_) == 1)
{
lean_object* v_val_3379_; lean_object* v___x_3380_; 
v_val_3379_ = lean_ctor_get(v_hypSimpMethods_3378_, 0);
lean_inc(v_goal_3363_);
v___x_3380_ = l_Lean_MVarId_getType(v_goal_3363_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3471_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3471_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3471_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
if (lean_obj_tag(v_a_3381_) == 5)
{
lean_object* v_fn_3385_; lean_object* v_arg_3386_; lean_object* v___x_3387_; lean_object* v_simpState_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___f_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_del_object(v___x_3383_);
v_fn_3385_ = lean_ctor_get(v_a_3381_, 0);
lean_inc_ref(v_fn_3385_);
v_arg_3386_ = lean_ctor_get(v_a_3381_, 1);
lean_inc_ref(v_arg_3386_);
v___x_3387_ = lean_st_ref_get(v___y_3367_);
v_simpState_3388_ = lean_ctor_get(v___x_3387_, 7);
lean_inc_ref(v_simpState_3388_);
lean_dec(v___x_3387_);
v___x_3389_ = lean_array_get_size(v_args_3364_);
v___x_3390_ = lean_array_get_size(v_excessArgs_3365_);
v___x_3391_ = lean_nat_add(v___x_3389_, v___x_3390_);
v___x_3392_ = lean_box(v___x_3362_);
v___f_3393_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3393_, 0, v_arg_3386_);
lean_closure_set(v___f_3393_, 1, v___x_3389_);
lean_closure_set(v___f_3393_, 2, v___x_3391_);
lean_closure_set(v___f_3393_, 3, v___x_3392_);
lean_closure_set(v___f_3393_, 4, v_a_3381_);
lean_closure_set(v___f_3393_, 5, v_fn_3385_);
v___x_3394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___closed__0));
lean_inc(v_val_3379_);
v___x_3395_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___f_3393_, v_val_3379_, v___x_3394_, v_simpState_3388_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v_fst_3397_; lean_object* v_snd_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3458_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v___x_3395_, 1);
v_fst_3397_ = lean_ctor_get(v_a_3396_, 0);
v_snd_3398_ = lean_ctor_get(v_a_3396_, 1);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_a_3396_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3400_ = v_a_3396_;
v_isShared_3401_ = v_isSharedCheck_3458_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_snd_3398_);
lean_inc(v_fst_3397_);
lean_dec(v_a_3396_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3458_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; lean_object* v_specBackwardRuleCache_3403_; lean_object* v_splitBackwardRuleCache_3404_; lean_object* v_latticeBackwardRuleCache_3405_; lean_object* v_frameBackwardRuleCache_3406_; lean_object* v_frameDB_3407_; lean_object* v_invariants_3408_; lean_object* v_vcs_3409_; lean_object* v_fuel_3410_; lean_object* v_inlineHandledInvariants_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3456_; 
v___x_3402_ = lean_st_ref_take(v___y_3367_);
v_specBackwardRuleCache_3403_ = lean_ctor_get(v___x_3402_, 0);
v_splitBackwardRuleCache_3404_ = lean_ctor_get(v___x_3402_, 1);
v_latticeBackwardRuleCache_3405_ = lean_ctor_get(v___x_3402_, 2);
v_frameBackwardRuleCache_3406_ = lean_ctor_get(v___x_3402_, 3);
v_frameDB_3407_ = lean_ctor_get(v___x_3402_, 4);
v_invariants_3408_ = lean_ctor_get(v___x_3402_, 5);
v_vcs_3409_ = lean_ctor_get(v___x_3402_, 6);
v_fuel_3410_ = lean_ctor_get(v___x_3402_, 8);
v_inlineHandledInvariants_3411_ = lean_ctor_get(v___x_3402_, 9);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3456_ == 0)
{
lean_object* v_unused_3457_; 
v_unused_3457_ = lean_ctor_get(v___x_3402_, 7);
lean_dec(v_unused_3457_);
v___x_3413_ = v___x_3402_;
v_isShared_3414_ = v_isSharedCheck_3456_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_inlineHandledInvariants_3411_);
lean_inc(v_fuel_3410_);
lean_inc(v_vcs_3409_);
lean_inc(v_invariants_3408_);
lean_inc(v_frameDB_3407_);
lean_inc(v_frameBackwardRuleCache_3406_);
lean_inc(v_latticeBackwardRuleCache_3405_);
lean_inc(v_splitBackwardRuleCache_3404_);
lean_inc(v_specBackwardRuleCache_3403_);
lean_dec(v___x_3402_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3456_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 7, v_snd_3398_);
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_specBackwardRuleCache_3403_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_splitBackwardRuleCache_3404_);
lean_ctor_set(v_reuseFailAlloc_3455_, 2, v_latticeBackwardRuleCache_3405_);
lean_ctor_set(v_reuseFailAlloc_3455_, 3, v_frameBackwardRuleCache_3406_);
lean_ctor_set(v_reuseFailAlloc_3455_, 4, v_frameDB_3407_);
lean_ctor_set(v_reuseFailAlloc_3455_, 5, v_invariants_3408_);
lean_ctor_set(v_reuseFailAlloc_3455_, 6, v_vcs_3409_);
lean_ctor_set(v_reuseFailAlloc_3455_, 7, v_snd_3398_);
lean_ctor_set(v_reuseFailAlloc_3455_, 8, v_fuel_3410_);
lean_ctor_set(v_reuseFailAlloc_3455_, 9, v_inlineHandledInvariants_3411_);
v___x_3416_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = lean_st_ref_put(v___y_3367_, v___x_3416_);
v___x_3418_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_3397_, v_goal_3363_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3446_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3446_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3446_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
switch(lean_obj_tag(v_a_3419_))
{
case 0:
{
lean_object* v___x_3423_; lean_object* v___x_3425_; 
lean_del_object(v___x_3400_);
v___x_3423_ = lean_box(0);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3423_);
v___x_3425_ = v___x_3421_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
case 1:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
lean_del_object(v___x_3400_);
v___x_3427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3427_);
v___x_3429_ = v___x_3421_;
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
default: 
{
lean_object* v_mvarId_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3445_; 
v_mvarId_3431_ = lean_ctor_get(v_a_3419_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_a_3419_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3433_ = v_a_3419_;
v_isShared_3434_ = v_isSharedCheck_3445_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_mvarId_3431_);
lean_dec(v_a_3419_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3445_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3435_ = lean_box(0);
if (v_isShared_3401_ == 0)
{
lean_ctor_set_tag(v___x_3400_, 1);
lean_ctor_set(v___x_3400_, 1, v___x_3435_);
lean_ctor_set(v___x_3400_, 0, v_mvarId_3431_);
v___x_3437_ = v___x_3400_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_mvarId_3431_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set_tag(v___x_3433_, 1);
lean_ctor_set(v___x_3433_, 0, v___x_3437_);
v___x_3439_ = v___x_3433_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3439_);
v___x_3441_ = v___x_3421_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
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
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_del_object(v___x_3400_);
v_a_3447_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3418_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3418_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v_goal_3363_);
v_a_3459_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3395_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3395_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
else
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
lean_dec(v_a_3381_);
lean_dec(v_goal_3363_);
v___x_3467_ = lean_box(0);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3467_);
v___x_3469_ = v___x_3383_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec(v_goal_3363_);
v_a_3472_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3380_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3380_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
lean_dec(v_goal_3363_);
v___x_3480_ = lean_box(0);
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
return v___x_3481_;
}
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_dec(v_goal_3363_);
v___x_3482_ = lean_box(0);
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
return v___x_3483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___boxed(lean_object* v___x_3484_, lean_object* v_goal_3485_, lean_object* v_args_3486_, lean_object* v_excessArgs_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
uint8_t v___x_23474__boxed_3500_; lean_object* v_res_3501_; 
v___x_23474__boxed_3500_ = lean_unbox(v___x_3484_);
v_res_3501_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1(v___x_23474__boxed_3500_, v_goal_3485_, v_args_3486_, v_excessArgs_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec_ref(v_excessArgs_3487_);
lean_dec_ref(v_args_3486_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(lean_object* v_goal_3502_, lean_object* v_info_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v_args_3516_; lean_object* v_excessArgs_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; lean_object* v___x_3521_; lean_object* v___y_3522_; lean_object* v___x_3523_; 
v_args_3516_ = lean_ctor_get(v_info_3503_, 1);
lean_inc_ref(v_args_3516_);
v_excessArgs_3517_ = lean_ctor_get(v_info_3503_, 2);
lean_inc_ref(v_excessArgs_3517_);
lean_dec_ref(v_info_3503_);
v___x_3518_ = lean_array_get_size(v_excessArgs_3517_);
v___x_3519_ = lean_unsigned_to_nat(0u);
v___x_3520_ = lean_nat_dec_eq(v___x_3518_, v___x_3519_);
v___x_3521_ = lean_box(v___x_3520_);
lean_inc(v_goal_3502_);
v___y_3522_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___boxed), 16, 4);
lean_closure_set(v___y_3522_, 0, v___x_3521_);
lean_closure_set(v___y_3522_, 1, v_goal_3502_);
lean_closure_set(v___y_3522_, 2, v_args_3516_);
lean_closure_set(v___y_3522_, 3, v_excessArgs_3517_);
v___x_3523_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_3502_, v___y_3522_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___boxed(lean_object* v_goal_3524_, lean_object* v_info_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(v_goal_3524_, v_info_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(lean_object* v_as_x27_3539_, lean_object* v_b_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
if (lean_obj_tag(v_as_x27_3539_) == 0)
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_b_3540_);
return v___x_3550_;
}
else
{
lean_object* v_head_3551_; lean_object* v_tail_3552_; lean_object* v___x_3553_; 
v_head_3551_ = lean_ctor_get(v_as_x27_3539_, 0);
v_tail_3552_ = lean_ctor_get(v_as_x27_3539_, 1);
lean_inc(v_head_3551_);
v___x_3553_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_head_3551_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
switch(lean_obj_tag(v_a_3554_))
{
case 0:
{
lean_object* v___x_3555_; 
lean_inc(v_head_3551_);
v___x_3555_ = lean_array_push(v_b_3540_, v_head_3551_);
v_as_x27_3539_ = v_tail_3552_;
v_b_3540_ = v___x_3555_;
goto _start;
}
case 1:
{
v_as_x27_3539_ = v_tail_3552_;
goto _start;
}
default: 
{
lean_object* v_mvarId_3558_; lean_object* v___x_3559_; 
v_mvarId_3558_ = lean_ctor_get(v_a_3554_, 0);
lean_inc(v_mvarId_3558_);
lean_dec_ref_known(v_a_3554_, 1);
v___x_3559_ = lean_array_push(v_b_3540_, v_mvarId_3558_);
v_as_x27_3539_ = v_tail_3552_;
v_b_3540_ = v___x_3559_;
goto _start;
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec_ref(v_b_3540_);
v_a_3561_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3553_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3553_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg___boxed(lean_object* v_as_x27_3569_, lean_object* v_b_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3569_, v_b_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v_as_x27_3569_);
return v_res_3580_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1(void){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__0));
v___x_3583_ = l_Lean_stringToMessageData(v___x_3582_);
return v___x_3583_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3(void){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3585_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__2));
v___x_3586_ = l_Lean_stringToMessageData(v___x_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(lean_object* v_goal_3587_, lean_object* v_info_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3588_);
lean_inc_ref(v___x_3601_);
v___x_3602_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v___x_3601_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3745_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3605_ = v___x_3602_;
v_isShared_3606_ = v_isSharedCheck_3745_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3602_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3745_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
if (lean_obj_tag(v_a_3603_) == 1)
{
lean_object* v_val_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3740_; 
lean_del_object(v___x_3605_);
v_val_3607_ = lean_ctor_get(v_a_3603_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_a_3603_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3609_ = v_a_3603_;
v_isShared_3610_ = v_isSharedCheck_3740_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_val_3607_);
lean_dec(v_a_3603_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3740_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; 
if (lean_obj_tag(v_val_3607_) == 2)
{
lean_object* v_keyedConfig_3679_; uint8_t v_trackZetaDelta_3680_; lean_object* v_zetaDeltaSet_3681_; lean_object* v_lctx_3682_; lean_object* v_localInstances_3683_; lean_object* v_defEqCtx_x3f_3684_; lean_object* v_synthPendingDepth_3685_; lean_object* v_customCanUnfoldPredicate_x3f_3686_; uint8_t v_univApprox_3687_; uint8_t v_inTypeClassResolution_3688_; uint8_t v_cacheInferType_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v_keyedConfig_3679_ = lean_ctor_get(v_a_3596_, 0);
v_trackZetaDelta_3680_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*7);
v_zetaDeltaSet_3681_ = lean_ctor_get(v_a_3596_, 1);
v_lctx_3682_ = lean_ctor_get(v_a_3596_, 2);
v_localInstances_3683_ = lean_ctor_get(v_a_3596_, 3);
v_defEqCtx_x3f_3684_ = lean_ctor_get(v_a_3596_, 4);
v_synthPendingDepth_3685_ = lean_ctor_get(v_a_3596_, 5);
v_customCanUnfoldPredicate_x3f_3686_ = lean_ctor_get(v_a_3596_, 6);
v_univApprox_3687_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3688_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*7 + 2);
v_cacheInferType_3689_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*7 + 3);
v___x_3690_ = 2;
lean_inc_ref(v_keyedConfig_3679_);
v___x_3691_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3690_, v_keyedConfig_3679_);
lean_inc(v_customCanUnfoldPredicate_x3f_3686_);
lean_inc(v_synthPendingDepth_3685_);
lean_inc(v_defEqCtx_x3f_3684_);
lean_inc_ref(v_localInstances_3683_);
lean_inc_ref(v_lctx_3682_);
lean_inc(v_zetaDeltaSet_3681_);
v___x_3692_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
lean_ctor_set(v___x_3692_, 1, v_zetaDeltaSet_3681_);
lean_ctor_set(v___x_3692_, 2, v_lctx_3682_);
lean_ctor_set(v___x_3692_, 3, v_localInstances_3683_);
lean_ctor_set(v___x_3692_, 4, v_defEqCtx_x3f_3684_);
lean_ctor_set(v___x_3692_, 5, v_synthPendingDepth_3685_);
lean_ctor_set(v___x_3692_, 6, v_customCanUnfoldPredicate_x3f_3686_);
lean_ctor_set_uint8(v___x_3692_, sizeof(void*)*7, v_trackZetaDelta_3680_);
lean_ctor_set_uint8(v___x_3692_, sizeof(void*)*7 + 1, v_univApprox_3687_);
lean_ctor_set_uint8(v___x_3692_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3688_);
lean_ctor_set_uint8(v___x_3692_, sizeof(void*)*7 + 3, v_cacheInferType_3689_);
v___x_3693_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_3601_, v___x_3692_, v_a_3597_, v_a_3598_, v_a_3599_);
lean_dec_ref_known(v___x_3692_, 7);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
if (lean_obj_tag(v_a_3694_) == 1)
{
lean_object* v_val_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3731_; 
lean_dec_ref_known(v_val_3607_, 1);
lean_del_object(v___x_3609_);
lean_dec_ref(v___x_3601_);
v_val_3695_ = lean_ctor_get(v_a_3694_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_a_3694_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3697_ = v_a_3694_;
v_isShared_3698_ = v_isSharedCheck_3731_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_val_3695_);
lean_dec(v_a_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3731_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Lean_Meta_Sym_shareCommonInc(v_val_3695_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v___x_3701_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_a_3700_);
lean_dec_ref_known(v___x_3699_, 1);
v___x_3701_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3587_, v_info_3588_, v_a_3700_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3714_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3714_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3714_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3709_; 
v___x_3706_ = lean_box(0);
v___x_3707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3707_, 0, v_a_3702_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3707_);
v___x_3709_ = v___x_3697_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3707_);
v___x_3709_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3711_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3709_);
v___x_3711_ = v___x_3704_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3709_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_del_object(v___x_3697_);
v_a_3715_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3701_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3701_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_del_object(v___x_3697_);
lean_dec_ref(v_info_3588_);
lean_dec(v_goal_3587_);
v_a_3723_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3699_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3699_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
else
{
lean_dec(v_a_3694_);
v___y_3612_ = v_a_3589_;
v___y_3613_ = v_a_3590_;
v___y_3614_ = v_a_3591_;
v___y_3615_ = v_a_3592_;
v___y_3616_ = v_a_3593_;
v___y_3617_ = v_a_3594_;
v___y_3618_ = v_a_3595_;
v___y_3619_ = v_a_3596_;
v___y_3620_ = v_a_3597_;
v___y_3621_ = v_a_3598_;
v___y_3622_ = v_a_3599_;
goto v___jp_3611_;
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec_ref_known(v_val_3607_, 1);
lean_del_object(v___x_3609_);
lean_dec_ref(v___x_3601_);
lean_dec_ref(v_info_3588_);
lean_dec(v_goal_3587_);
v_a_3732_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3693_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3693_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
v___y_3612_ = v_a_3589_;
v___y_3613_ = v_a_3590_;
v___y_3614_ = v_a_3591_;
v___y_3615_ = v_a_3592_;
v___y_3616_ = v_a_3593_;
v___y_3617_ = v_a_3594_;
v___y_3618_ = v_a_3595_;
v___y_3619_ = v_a_3596_;
v___y_3620_ = v_a_3597_;
v___y_3621_ = v_a_3598_;
v___y_3622_ = v_a_3599_;
goto v___jp_3611_;
}
v___jp_3611_:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_val_3607_, v_info_3588_, v___y_3613_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3629_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3623_, 1);
v___x_3625_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1);
v___x_3626_ = l_Lean_indentExpr(v___x_3601_);
lean_inc_ref(v___x_3626_);
v___x_3627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3625_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3627_);
v___x_3629_ = v___x_3609_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3627_);
v___x_3629_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_3624_, v_goal_3587_, v___x_3629_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
if (lean_obj_tag(v_a_3631_) == 1)
{
lean_object* v_mvarIds_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3658_; 
lean_dec_ref(v___x_3626_);
v_mvarIds_3632_ = lean_ctor_get(v_a_3631_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_a_3631_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3634_ = v_a_3631_;
v_isShared_3635_ = v_isSharedCheck_3658_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_mvarIds_3632_);
lean_dec(v_a_3631_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3658_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0));
v___x_3637_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_mvarIds_3632_, v___x_3636_, v___y_3612_, v___y_3613_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
lean_dec(v_mvarIds_3632_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3649_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3640_ = v___x_3637_;
v_isShared_3641_ = v_isSharedCheck_3649_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3649_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3642_; lean_object* v___x_3644_; 
v___x_3642_ = lean_array_to_list(v_a_3638_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3642_);
v___x_3644_ = v___x_3634_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3642_);
v___x_3644_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3646_; 
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3644_);
v___x_3646_ = v___x_3640_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_del_object(v___x_3634_);
v_a_3650_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3637_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3637_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
}
else
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
lean_dec(v_a_3631_);
v___x_3659_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3);
v___x_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
lean_ctor_set(v___x_3660_, 1, v___x_3626_);
v___x_3661_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3660_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
return v___x_3661_;
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_dec_ref(v___x_3626_);
v_a_3662_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3630_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3630_);
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
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_del_object(v___x_3609_);
lean_dec_ref(v___x_3601_);
lean_dec(v_goal_3587_);
v_a_3671_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3623_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3623_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
}
}
else
{
lean_object* v___x_3741_; lean_object* v___x_3743_; 
lean_dec(v_a_3603_);
lean_dec_ref(v___x_3601_);
lean_dec_ref(v_info_3588_);
lean_dec(v_goal_3587_);
v___x_3741_ = lean_box(0);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v___x_3741_);
v___x_3743_ = v___x_3605_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3741_);
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
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec_ref(v___x_3601_);
lean_dec_ref(v_info_3588_);
lean_dec(v_goal_3587_);
v_a_3746_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3602_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3602_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___boxed(lean_object* v_goal_3754_, lean_object* v_info_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(v_goal_3754_, v_info_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0(lean_object* v_as_3769_, lean_object* v_as_x27_3770_, lean_object* v_b_3771_, lean_object* v_a_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3770_, v_b_3771_, v___y_3773_, v___y_3774_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___boxed(lean_object* v_as_3786_, lean_object* v_as_x27_3787_, lean_object* v_b_3788_, lean_object* v_a_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0(v_as_3786_, v_as_x27_3787_, v_b_3788_, v_a_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v_as_x27_3787_);
lean_dec(v_as_3786_);
return v_res_3802_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__0));
v___x_3805_ = l_Lean_stringToMessageData(v___x_3804_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(lean_object* v_goal_3806_, lean_object* v_info_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_){
_start:
{
lean_object* v___x_3820_; lean_object* v_f_3821_; lean_object* v___x_3822_; 
v___x_3820_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3807_);
v_f_3821_ = l_Lean_Expr_getAppFn(v___x_3820_);
v___x_3822_ = l_Lean_Expr_fvarId_x3f(v_f_3821_);
lean_dec_ref(v_f_3821_);
if (lean_obj_tag(v___x_3822_) == 1)
{
lean_object* v_val_3823_; uint8_t v___x_3824_; lean_object* v___x_3825_; 
v_val_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc_n(v_val_3823_, 2);
lean_dec_ref_known(v___x_3822_, 1);
v___x_3824_ = 0;
v___x_3825_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_3823_, v___x_3824_, v_a_3815_, v_a_3817_, v_a_3818_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3913_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3828_ = v___x_3825_;
v_isShared_3829_ = v_isSharedCheck_3913_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3913_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
if (lean_obj_tag(v_a_3826_) == 1)
{
lean_object* v_val_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3908_; 
lean_del_object(v___x_3828_);
v_val_3830_ = lean_ctor_get(v_a_3826_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_a_3826_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3832_ = v_a_3826_;
v_isShared_3833_ = v_isSharedCheck_3908_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_val_3830_);
lean_dec(v_a_3826_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3908_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v_options_3880_; uint8_t v_hasTrace_3881_; 
v_options_3880_ = lean_ctor_get(v_a_3817_, 2);
v_hasTrace_3881_ = lean_ctor_get_uint8(v_options_3880_, sizeof(void*)*1);
if (v_hasTrace_3881_ == 0)
{
lean_dec(v_val_3823_);
v___y_3835_ = v_a_3808_;
v___y_3836_ = v_a_3809_;
v___y_3837_ = v_a_3810_;
v___y_3838_ = v_a_3811_;
v___y_3839_ = v_a_3812_;
v___y_3840_ = v_a_3813_;
v___y_3841_ = v_a_3814_;
v___y_3842_ = v_a_3815_;
v___y_3843_ = v_a_3816_;
v___y_3844_ = v_a_3817_;
v___y_3845_ = v_a_3818_;
goto v___jp_3834_;
}
else
{
lean_object* v_inheritedTraceOptions_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; uint8_t v___x_3885_; 
v_inheritedTraceOptions_3882_ = lean_ctor_get(v_a_3817_, 13);
v___x_3883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_3884_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_3885_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3882_, v_options_3880_, v___x_3884_);
if (v___x_3885_ == 0)
{
lean_dec(v_val_3823_);
v___y_3835_ = v_a_3808_;
v___y_3836_ = v_a_3809_;
v___y_3837_ = v_a_3810_;
v___y_3838_ = v_a_3811_;
v___y_3839_ = v_a_3812_;
v___y_3840_ = v_a_3813_;
v___y_3841_ = v_a_3814_;
v___y_3842_ = v_a_3815_;
v___y_3843_ = v_a_3816_;
v___y_3844_ = v_a_3817_;
v___y_3845_ = v_a_3818_;
goto v___jp_3834_;
}
else
{
lean_object* v___x_3886_; 
v___x_3886_ = l_Lean_FVarId_getUserName___redArg(v_val_3823_, v_a_3815_, v_a_3817_, v_a_3818_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1);
v___x_3889_ = l_Lean_MessageData_ofName(v_a_3887_);
v___x_3890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3883_, v___x_3890_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_dec_ref_known(v___x_3891_, 1);
v___y_3835_ = v_a_3808_;
v___y_3836_ = v_a_3809_;
v___y_3837_ = v_a_3810_;
v___y_3838_ = v_a_3811_;
v___y_3839_ = v_a_3812_;
v___y_3840_ = v_a_3813_;
v___y_3841_ = v_a_3814_;
v___y_3842_ = v_a_3815_;
v___y_3843_ = v_a_3816_;
v___y_3844_ = v_a_3817_;
v___y_3845_ = v_a_3818_;
goto v___jp_3834_;
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_del_object(v___x_3832_);
lean_dec(v_val_3830_);
lean_dec_ref(v___x_3820_);
lean_dec_ref(v_info_3807_);
lean_dec(v_goal_3806_);
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3891_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3891_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_del_object(v___x_3832_);
lean_dec(v_val_3830_);
lean_dec_ref(v___x_3820_);
lean_dec_ref(v_info_3807_);
lean_dec(v_goal_3806_);
v_a_3900_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3886_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3886_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
}
v___jp_3834_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3846_ = l_Lean_Expr_getAppNumArgs(v___x_3820_);
v___x_3847_ = lean_mk_empty_array_with_capacity(v___x_3846_);
lean_dec(v___x_3846_);
v___x_3848_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3820_, v___x_3847_);
v___x_3849_ = l_Lean_Expr_betaRev(v_val_3830_, v___x_3848_, v___x_3824_, v___x_3824_);
lean_dec_ref(v___x_3848_);
v___x_3850_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3849_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; lean_object* v___x_3852_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3850_, 1);
v___x_3852_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3806_, v_info_3807_, v_a_3851_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3863_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3855_ = v___x_3852_;
v_isShared_3856_ = v_isSharedCheck_3863_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3863_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v_a_3853_);
v___x_3858_ = v___x_3832_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3860_; 
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3858_);
v___x_3860_ = v___x_3855_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3858_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_del_object(v___x_3832_);
v_a_3864_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3852_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3852_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_del_object(v___x_3832_);
lean_dec_ref(v_info_3807_);
lean_dec(v_goal_3806_);
v_a_3872_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3850_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3850_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
}
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
lean_dec(v_a_3826_);
lean_dec(v_val_3823_);
lean_dec_ref(v___x_3820_);
lean_dec_ref(v_info_3807_);
lean_dec(v_goal_3806_);
v___x_3909_ = lean_box(0);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v___x_3909_);
v___x_3911_ = v___x_3828_;
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
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec(v_val_3823_);
lean_dec_ref(v___x_3820_);
lean_dec_ref(v_info_3807_);
lean_dec(v_goal_3806_);
v_a_3914_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3825_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3825_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
else
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
lean_dec(v___x_3822_);
lean_dec_ref(v___x_3820_);
lean_dec_ref(v_info_3807_);
lean_dec(v_goal_3806_);
v___x_3922_ = lean_box(0);
v___x_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
return v___x_3923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___boxed(lean_object* v_goal_3924_, lean_object* v_info_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(v_goal_3924_, v_info_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec_ref(v_a_3926_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f(lean_object* v_goal_3939_, lean_object* v_info_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v___x_3953_; lean_object* v_a_3955_; lean_object* v_f_4016_; 
v___x_3953_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3940_);
v_f_4016_ = l_Lean_Expr_getAppFn(v___x_3953_);
if (lean_obj_tag(v_f_4016_) == 11)
{
lean_object* v_keyedConfig_4017_; uint8_t v_trackZetaDelta_4018_; lean_object* v_zetaDeltaSet_4019_; lean_object* v_lctx_4020_; lean_object* v_localInstances_4021_; lean_object* v_defEqCtx_x3f_4022_; lean_object* v_synthPendingDepth_4023_; lean_object* v_customCanUnfoldPredicate_x3f_4024_; uint8_t v_univApprox_4025_; uint8_t v_inTypeClassResolution_4026_; uint8_t v_cacheInferType_4027_; uint8_t v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_keyedConfig_4017_ = lean_ctor_get(v_a_3948_, 0);
v_trackZetaDelta_4018_ = lean_ctor_get_uint8(v_a_3948_, sizeof(void*)*7);
v_zetaDeltaSet_4019_ = lean_ctor_get(v_a_3948_, 1);
v_lctx_4020_ = lean_ctor_get(v_a_3948_, 2);
v_localInstances_4021_ = lean_ctor_get(v_a_3948_, 3);
v_defEqCtx_x3f_4022_ = lean_ctor_get(v_a_3948_, 4);
v_synthPendingDepth_4023_ = lean_ctor_get(v_a_3948_, 5);
v_customCanUnfoldPredicate_x3f_4024_ = lean_ctor_get(v_a_3948_, 6);
v_univApprox_4025_ = lean_ctor_get_uint8(v_a_3948_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4026_ = lean_ctor_get_uint8(v_a_3948_, sizeof(void*)*7 + 2);
v_cacheInferType_4027_ = lean_ctor_get_uint8(v_a_3948_, sizeof(void*)*7 + 3);
v___x_4028_ = 3;
lean_inc_ref(v_keyedConfig_4017_);
v___x_4029_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4028_, v_keyedConfig_4017_);
lean_inc(v_customCanUnfoldPredicate_x3f_4024_);
lean_inc(v_synthPendingDepth_4023_);
lean_inc(v_defEqCtx_x3f_4022_);
lean_inc_ref(v_localInstances_4021_);
lean_inc_ref(v_lctx_4020_);
lean_inc(v_zetaDeltaSet_4019_);
v___x_4030_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
lean_ctor_set(v___x_4030_, 1, v_zetaDeltaSet_4019_);
lean_ctor_set(v___x_4030_, 2, v_lctx_4020_);
lean_ctor_set(v___x_4030_, 3, v_localInstances_4021_);
lean_ctor_set(v___x_4030_, 4, v_defEqCtx_x3f_4022_);
lean_ctor_set(v___x_4030_, 5, v_synthPendingDepth_4023_);
lean_ctor_set(v___x_4030_, 6, v_customCanUnfoldPredicate_x3f_4024_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*7, v_trackZetaDelta_4018_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*7 + 1, v_univApprox_4025_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4026_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*7 + 3, v_cacheInferType_4027_);
v___x_4031_ = l_Lean_Meta_reduceProj_x3f(v_f_4016_, v___x_4030_, v_a_3949_, v_a_3950_, v_a_3951_);
lean_dec_ref_known(v___x_4030_, 7);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4031_, 1);
v_a_3955_ = v_a_4032_;
goto v___jp_3954_;
}
else
{
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4033_; 
v_a_4033_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4031_, 1);
v_a_3955_ = v_a_4033_;
goto v___jp_3954_;
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
lean_dec_ref(v___x_3953_);
lean_dec_ref(v_info_3940_);
lean_dec(v_goal_3939_);
v_a_4034_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4031_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4031_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
}
else
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
lean_dec_ref(v_f_4016_);
lean_dec_ref(v___x_3953_);
lean_dec_ref(v_info_3940_);
lean_dec(v_goal_3939_);
v___x_4042_ = lean_box(0);
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
return v___x_4043_;
}
v___jp_3954_:
{
if (lean_obj_tag(v_a_3955_) == 1)
{
lean_object* v_val_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_4013_; 
v_val_3956_ = lean_ctor_get(v_a_3955_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_a_3955_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_3958_ = v_a_3955_;
v_isShared_3959_ = v_isSharedCheck_4013_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_val_3956_);
lean_dec(v_a_3955_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_4013_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3960_; 
v___x_3960_ = l_Lean_Meta_Sym_unfoldReducible(v_val_3956_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3962_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref_known(v___x_3960_, 1);
v___x_3962_ = l_Lean_Meta_Sym_shareCommon(v_a_3961_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3962_, 1);
v___x_3964_ = l_Lean_Expr_getAppNumArgs(v___x_3953_);
v___x_3965_ = lean_mk_empty_array_with_capacity(v___x_3964_);
lean_dec(v___x_3964_);
v___x_3966_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3953_, v___x_3965_);
v___x_3967_ = l_Lean_Meta_Sym_betaRevS(v_a_3963_, v___x_3966_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3969_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_a_3968_);
lean_dec_ref_known(v___x_3967_, 1);
v___x_3969_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3939_, v_info_3940_, v_a_3968_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3980_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3972_ = v___x_3969_;
v_isShared_3973_ = v_isSharedCheck_3980_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3980_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v_a_3970_);
v___x_3975_ = v___x_3958_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3977_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3975_);
v___x_3977_ = v___x_3972_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_del_object(v___x_3958_);
v_a_3981_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3969_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3969_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
lean_del_object(v___x_3958_);
lean_dec_ref(v_info_3940_);
lean_dec(v_goal_3939_);
v_a_3989_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3967_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3967_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_del_object(v___x_3958_);
lean_dec_ref(v___x_3953_);
lean_dec_ref(v_info_3940_);
lean_dec(v_goal_3939_);
v_a_3997_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3962_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3962_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
lean_del_object(v___x_3958_);
lean_dec_ref(v___x_3953_);
lean_dec_ref(v_info_3940_);
lean_dec(v_goal_3939_);
v_a_4005_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3960_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3960_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_dec(v_a_3955_);
lean_dec_ref(v___x_3953_);
lean_dec_ref(v_info_3940_);
lean_dec(v_goal_3939_);
v___x_4014_ = lean_box(0);
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
return v___x_4015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f___boxed(lean_object* v_goal_4044_, lean_object* v_info_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f(v_goal_4044_, v_info_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
return v_res_4058_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0));
v___x_4061_ = l_Lean_stringToMessageData(v___x_4060_);
return v___x_4061_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2));
v___x_4064_ = l_Lean_stringToMessageData(v___x_4063_);
return v___x_4064_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4066_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4));
v___x_4067_ = l_Lean_stringToMessageData(v___x_4066_);
return v___x_4067_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6));
v___x_4070_ = l_Lean_stringToMessageData(v___x_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
if (lean_obj_tag(v_a_4071_) == 0)
{
lean_object* v___x_4073_; 
v___x_4073_ = l_List_reverse___redArg(v_a_4072_);
return v___x_4073_;
}
else
{
lean_object* v_head_4074_; lean_object* v_tail_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4103_; 
v_head_4074_ = lean_ctor_get(v_a_4071_, 0);
v_tail_4075_ = lean_ctor_get(v_a_4071_, 1);
v_isSharedCheck_4103_ = !lean_is_exclusive(v_a_4071_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4077_ = v_a_4071_;
v_isShared_4078_ = v_isSharedCheck_4103_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_tail_4075_);
lean_inc(v_head_4074_);
lean_dec(v_a_4071_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4103_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___y_4080_; 
switch(lean_obj_tag(v_head_4074_))
{
case 0:
{
lean_object* v_declName_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v_declName_4085_ = lean_ctor_get(v_head_4074_, 0);
lean_inc(v_declName_4085_);
lean_dec_ref_known(v_head_4074_, 1);
v___x_4086_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_4087_ = l_Lean_MessageData_ofName(v_declName_4085_);
v___x_4088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4086_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
v___y_4080_ = v___x_4088_;
goto v___jp_4079_;
}
case 1:
{
lean_object* v_fvarId_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v_fvarId_4089_ = lean_ctor_get(v_head_4074_, 0);
lean_inc(v_fvarId_4089_);
lean_dec_ref_known(v_head_4074_, 1);
v___x_4090_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_4091_ = l_Lean_mkFVar(v_fvarId_4089_);
v___x_4092_ = l_Lean_MessageData_ofExpr(v___x_4091_);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4090_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___y_4080_ = v___x_4093_;
goto v___jp_4079_;
}
default: 
{
lean_object* v_ref_4094_; lean_object* v_proof_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v_ref_4094_ = lean_ctor_get(v_head_4074_, 1);
lean_inc(v_ref_4094_);
v_proof_4095_ = lean_ctor_get(v_head_4074_, 2);
lean_inc_ref(v_proof_4095_);
lean_dec_ref_known(v_head_4074_, 3);
v___x_4096_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_4097_ = l_Lean_MessageData_ofSyntax(v_ref_4094_);
v___x_4098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4096_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
v___x_4099_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_4100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4098_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
v___x_4101_ = l_Lean_MessageData_ofExpr(v_proof_4095_);
v___x_4102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4100_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
v___y_4080_ = v___x_4102_;
goto v___jp_4079_;
}
}
v___jp_4079_:
{
lean_object* v___x_4082_; 
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 1, v_a_4072_);
lean_ctor_set(v___x_4077_, 0, v___y_4080_);
v___x_4082_ = v___x_4077_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___y_4080_);
lean_ctor_set(v_reuseFailAlloc_4084_, 1, v_a_4072_);
v___x_4082_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
v_a_4071_ = v_tail_4075_;
v_a_4072_ = v___x_4082_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t v_sz_4104_, size_t v_i_4105_, lean_object* v_bs_4106_){
_start:
{
uint8_t v___x_4107_; 
v___x_4107_ = lean_usize_dec_lt(v_i_4105_, v_sz_4104_);
if (v___x_4107_ == 0)
{
return v_bs_4106_;
}
else
{
lean_object* v_v_4108_; lean_object* v_proof_4109_; lean_object* v___x_4110_; lean_object* v_bs_x27_4111_; size_t v___x_4112_; size_t v___x_4113_; lean_object* v___x_4114_; 
v_v_4108_ = lean_array_uget_borrowed(v_bs_4106_, v_i_4105_);
v_proof_4109_ = lean_ctor_get(v_v_4108_, 1);
lean_inc_ref(v_proof_4109_);
v___x_4110_ = lean_unsigned_to_nat(0u);
v_bs_x27_4111_ = lean_array_uset(v_bs_4106_, v_i_4105_, v___x_4110_);
v___x_4112_ = ((size_t)1ULL);
v___x_4113_ = lean_usize_add(v_i_4105_, v___x_4112_);
v___x_4114_ = lean_array_uset(v_bs_x27_4111_, v_i_4105_, v_proof_4109_);
v_i_4105_ = v___x_4113_;
v_bs_4106_ = v___x_4114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object* v_sz_4116_, lean_object* v_i_4117_, lean_object* v_bs_4118_){
_start:
{
size_t v_sz_boxed_4119_; size_t v_i_boxed_4120_; lean_object* v_res_4121_; 
v_sz_boxed_4119_ = lean_unbox_usize(v_sz_4116_);
lean_dec(v_sz_4116_);
v_i_boxed_4120_ = lean_unbox_usize(v_i_4117_);
lean_dec(v_i_4117_);
v_res_4121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_boxed_4119_, v_i_boxed_4120_, v_bs_4118_);
return v_res_4121_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1(void){
_start:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0));
v___x_4124_ = l_Lean_stringToMessageData(v___x_4123_);
return v___x_4124_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3(void){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2));
v___x_4127_ = l_Lean_stringToMessageData(v___x_4126_);
return v___x_4127_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4129_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4));
v___x_4130_ = l_Lean_stringToMessageData(v___x_4129_);
return v___x_4130_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6));
v___x_4133_ = l_Lean_stringToMessageData(v___x_4132_);
return v___x_4133_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9(void){
_start:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8));
v___x_4136_ = l_Lean_stringToMessageData(v___x_4135_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object* v_prog_4137_, lean_object* v_monad_4138_, lean_object* v_thms_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_){
_start:
{
uint8_t v_errorOnMissingSpec_4146_; 
v_errorOnMissingSpec_4146_ = lean_ctor_get_uint8(v_a_4140_, sizeof(void*)*5 + 2);
if (v_errorOnMissingSpec_4146_ == 0)
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4147_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_4147_, 0, v_prog_4137_);
lean_ctor_set(v___x_4147_, 1, v_monad_4138_);
lean_ctor_set(v___x_4147_, 2, v_thms_4139_);
v___x_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
return v___x_4149_;
}
else
{
lean_object* v___x_4150_; lean_object* v___x_4151_; uint8_t v___x_4152_; 
v___x_4150_ = lean_array_get_size(v_thms_4139_);
v___x_4151_ = lean_unsigned_to_nat(0u);
v___x_4152_ = lean_nat_dec_eq(v___x_4150_, v___x_4151_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; size_t v_sz_4162_; size_t v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4153_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1);
v___x_4154_ = l_Lean_MessageData_ofExpr(v_prog_4137_);
v___x_4155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4153_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3);
v___x_4157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4155_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = l_Lean_MessageData_ofExpr(v_monad_4138_);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4157_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5);
v___x_4161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v_sz_4162_ = lean_array_size(v_thms_4139_);
v___x_4163_ = ((size_t)0ULL);
v___x_4164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_4162_, v___x_4163_, v_thms_4139_);
v___x_4165_ = lean_array_to_list(v___x_4164_);
v___x_4166_ = lean_box(0);
v___x_4167_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1(v___x_4165_, v___x_4166_);
v___x_4168_ = l_Lean_MessageData_ofList(v___x_4167_);
v___x_4169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4161_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_4171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4169_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_4171_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_);
return v___x_4172_;
}
else
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_dec_ref(v_thms_4139_);
lean_dec_ref(v_monad_4138_);
v___x_4173_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9);
v___x_4174_ = l_Lean_MessageData_ofExpr(v_prog_4137_);
v___x_4175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4173_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
v___x_4176_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_4177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4175_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
v___x_4178_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_4177_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_);
return v___x_4178_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object* v_prog_4179_, lean_object* v_monad_4180_, lean_object* v_thms_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_4179_, v_monad_4180_, v_thms_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_);
lean_dec(v_a_4186_);
lean_dec_ref(v_a_4185_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec_ref(v_a_4182_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec(lean_object* v_prog_4189_, lean_object* v_monad_4190_, lean_object* v_thms_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_4189_, v_monad_4190_, v_thms_4191_, v_a_4192_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object* v_prog_4205_, lean_object* v_monad_4206_, lean_object* v_thms_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec(v_prog_4205_, v_monad_4206_, v_thms_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
lean_dec(v_a_4210_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
return v_res_4220_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1(void){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4222_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__0));
v___x_4223_ = l_Lean_stringToMessageData(v___x_4222_);
return v___x_4223_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3(void){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__2));
v___x_4226_ = l_Lean_stringToMessageData(v___x_4225_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(lean_object* v_prog_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v_untilPat_x3f_4236_; 
v_untilPat_x3f_4236_ = lean_ctor_get(v_a_4228_, 4);
if (lean_obj_tag(v_untilPat_x3f_4236_) == 1)
{
lean_object* v_val_4237_; uint8_t v___x_4238_; lean_object* v___x_4239_; 
v_val_4237_ = lean_ctor_get(v_untilPat_x3f_4236_, 0);
v___x_4238_ = 1;
lean_inc_ref(v_prog_4227_);
lean_inc(v_val_4237_);
v___x_4239_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_val_4237_, v_prog_4227_, v___x_4238_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4286_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4242_ = v___x_4239_;
v_isShared_4243_ = v_isSharedCheck_4286_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4239_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4286_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
if (lean_obj_tag(v_a_4240_) == 0)
{
uint8_t v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4247_; 
lean_dec_ref(v_prog_4227_);
v___x_4244_ = 0;
v___x_4245_ = lean_box(v___x_4244_);
if (v_isShared_4243_ == 0)
{
lean_ctor_set(v___x_4242_, 0, v___x_4245_);
v___x_4247_ = v___x_4242_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4245_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
else
{
lean_object* v_options_4249_; uint8_t v_hasTrace_4250_; 
lean_dec_ref_known(v_a_4240_, 1);
v_options_4249_ = lean_ctor_get(v_a_4233_, 2);
v_hasTrace_4250_ = lean_ctor_get_uint8(v_options_4249_, sizeof(void*)*1);
if (v_hasTrace_4250_ == 0)
{
lean_object* v___x_4251_; lean_object* v___x_4253_; 
lean_dec_ref(v_prog_4227_);
v___x_4251_ = lean_box(v___x_4238_);
if (v_isShared_4243_ == 0)
{
lean_ctor_set(v___x_4242_, 0, v___x_4251_);
v___x_4253_ = v___x_4242_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4251_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
else
{
lean_object* v_inheritedTraceOptions_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; uint8_t v___x_4258_; 
v_inheritedTraceOptions_4255_ = lean_ctor_get(v_a_4233_, 13);
v___x_4256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_4257_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_4258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4255_, v_options_4249_, v___x_4257_);
if (v___x_4258_ == 0)
{
lean_object* v___x_4259_; lean_object* v___x_4261_; 
lean_dec_ref(v_prog_4227_);
v___x_4259_ = lean_box(v___x_4238_);
if (v_isShared_4243_ == 0)
{
lean_ctor_set(v___x_4242_, 0, v___x_4259_);
v___x_4261_ = v___x_4242_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
else
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
lean_del_object(v___x_4242_);
v___x_4263_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1);
v___x_4264_ = l_Lean_MessageData_ofExpr(v_prog_4227_);
v___x_4265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4263_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
v___x_4266_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3);
v___x_4267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4265_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4256_, v___x_4267_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4276_; 
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4276_ == 0)
{
lean_object* v_unused_4277_; 
v_unused_4277_ = lean_ctor_get(v___x_4268_, 0);
lean_dec(v_unused_4277_);
v___x_4270_ = v___x_4268_;
v_isShared_4271_ = v_isSharedCheck_4276_;
goto v_resetjp_4269_;
}
else
{
lean_dec(v___x_4268_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4276_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4272_; lean_object* v___x_4274_; 
v___x_4272_ = lean_box(v___x_4238_);
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 0, v___x_4272_);
v___x_4274_ = v___x_4270_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4272_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
v_a_4278_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4268_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4268_);
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
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_dec_ref(v_prog_4227_);
v_a_4287_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4239_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4239_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
else
{
uint8_t v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
lean_dec_ref(v_prog_4227_);
v___x_4295_ = 0;
v___x_4296_ = lean_box(v___x_4295_);
v___x_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4296_);
return v___x_4297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___boxed(lean_object* v_prog_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v_prog_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_);
lean_dec(v_a_4305_);
lean_dec_ref(v_a_4304_);
lean_dec(v_a_4303_);
lean_dec_ref(v_a_4302_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec_ref(v_a_4299_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern(lean_object* v_prog_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v_prog_4308_, v_a_4309_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___boxed(lean_object* v_prog_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern(v_prog_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_);
lean_dec(v_a_4333_);
lean_dec_ref(v_a_4332_);
lean_dec(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec(v_a_4324_);
lean_dec_ref(v_a_4323_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(lean_object* v_k_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v_b_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v___x_4350_; 
lean_inc(v___y_4348_);
lean_inc_ref(v___y_4347_);
lean_inc(v___y_4346_);
lean_inc_ref(v___y_4345_);
lean_inc(v___y_4343_);
lean_inc_ref(v___y_4342_);
lean_inc(v___y_4341_);
lean_inc_ref(v___y_4340_);
lean_inc(v___y_4339_);
lean_inc(v___y_4338_);
lean_inc_ref(v___y_4337_);
v___x_4350_ = lean_apply_13(v_k_4336_, v_b_4344_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, lean_box(0));
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v_b_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(v_k_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v_b_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(lean_object* v_name_4366_, lean_object* v_type_4367_, lean_object* v_val_4368_, lean_object* v_k_4369_, uint8_t v_nondep_4370_, uint8_t v_kind_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___f_4384_; lean_object* v___x_4385_; 
lean_inc(v___y_4378_);
lean_inc_ref(v___y_4377_);
lean_inc(v___y_4376_);
lean_inc_ref(v___y_4375_);
lean_inc(v___y_4374_);
lean_inc(v___y_4373_);
lean_inc_ref(v___y_4372_);
v___f_4384_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_4384_, 0, v_k_4369_);
lean_closure_set(v___f_4384_, 1, v___y_4372_);
lean_closure_set(v___f_4384_, 2, v___y_4373_);
lean_closure_set(v___f_4384_, 3, v___y_4374_);
lean_closure_set(v___f_4384_, 4, v___y_4375_);
lean_closure_set(v___f_4384_, 5, v___y_4376_);
lean_closure_set(v___f_4384_, 6, v___y_4377_);
lean_closure_set(v___f_4384_, 7, v___y_4378_);
v___x_4385_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_4366_, v_type_4367_, v_val_4368_, v___f_4384_, v_nondep_4370_, v_kind_4371_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4385_) == 0)
{
return v___x_4385_;
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4385_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4385_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_name_4394_ = _args[0];
lean_object* v_type_4395_ = _args[1];
lean_object* v_val_4396_ = _args[2];
lean_object* v_k_4397_ = _args[3];
lean_object* v_nondep_4398_ = _args[4];
lean_object* v_kind_4399_ = _args[5];
lean_object* v___y_4400_ = _args[6];
lean_object* v___y_4401_ = _args[7];
lean_object* v___y_4402_ = _args[8];
lean_object* v___y_4403_ = _args[9];
lean_object* v___y_4404_ = _args[10];
lean_object* v___y_4405_ = _args[11];
lean_object* v___y_4406_ = _args[12];
lean_object* v___y_4407_ = _args[13];
lean_object* v___y_4408_ = _args[14];
lean_object* v___y_4409_ = _args[15];
lean_object* v___y_4410_ = _args[16];
lean_object* v___y_4411_ = _args[17];
_start:
{
uint8_t v_nondep_boxed_4412_; uint8_t v_kind_boxed_4413_; lean_object* v_res_4414_; 
v_nondep_boxed_4412_ = lean_unbox(v_nondep_4398_);
v_kind_boxed_4413_ = lean_unbox(v_kind_4399_);
v_res_4414_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4394_, v_type_4395_, v_val_4396_, v_k_4397_, v_nondep_boxed_4412_, v_kind_boxed_4413_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0(lean_object* v_00_u03b1_4415_, lean_object* v_name_4416_, lean_object* v_type_4417_, lean_object* v_val_4418_, lean_object* v_k_4419_, uint8_t v_nondep_4420_, uint8_t v_kind_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4416_, v_type_4417_, v_val_4418_, v_k_4419_, v_nondep_4420_, v_kind_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_4435_ = _args[0];
lean_object* v_name_4436_ = _args[1];
lean_object* v_type_4437_ = _args[2];
lean_object* v_val_4438_ = _args[3];
lean_object* v_k_4439_ = _args[4];
lean_object* v_nondep_4440_ = _args[5];
lean_object* v_kind_4441_ = _args[6];
lean_object* v___y_4442_ = _args[7];
lean_object* v___y_4443_ = _args[8];
lean_object* v___y_4444_ = _args[9];
lean_object* v___y_4445_ = _args[10];
lean_object* v___y_4446_ = _args[11];
lean_object* v___y_4447_ = _args[12];
lean_object* v___y_4448_ = _args[13];
lean_object* v___y_4449_ = _args[14];
lean_object* v___y_4450_ = _args[15];
lean_object* v___y_4451_ = _args[16];
lean_object* v___y_4452_ = _args[17];
lean_object* v___y_4453_ = _args[18];
_start:
{
uint8_t v_nondep_boxed_4454_; uint8_t v_kind_boxed_4455_; lean_object* v_res_4456_; 
v_nondep_boxed_4454_ = lean_unbox(v_nondep_4440_);
v_kind_boxed_4455_ = lean_unbox(v_kind_4441_);
v_res_4456_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0(v_00_u03b1_4435_, v_name_4436_, v_type_4437_, v_val_4438_, v_k_4439_, v_nondep_boxed_4454_, v_kind_boxed_4455_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0___boxed(lean_object* v_acc_4457_, lean_object* v_declInfos_4458_, lean_object* v_k_4459_, lean_object* v_fv_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0(v_acc_4457_, v_declInfos_4458_, v_k_4459_, v_fv_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(lean_object* v_declInfos_4474_, lean_object* v_k_4475_, lean_object* v_acc_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; uint8_t v___x_4491_; 
v___x_4489_ = lean_array_get_size(v_acc_4476_);
v___x_4490_ = lean_array_get_size(v_declInfos_4474_);
v___x_4491_ = lean_nat_dec_lt(v___x_4489_, v___x_4490_);
if (v___x_4491_ == 0)
{
lean_object* v___x_4492_; 
lean_dec_ref(v_declInfos_4474_);
lean_inc(v_a_4487_);
lean_inc_ref(v_a_4486_);
lean_inc(v_a_4485_);
lean_inc_ref(v_a_4484_);
lean_inc(v_a_4483_);
lean_inc_ref(v_a_4482_);
lean_inc(v_a_4481_);
lean_inc_ref(v_a_4480_);
lean_inc(v_a_4479_);
lean_inc(v_a_4478_);
lean_inc_ref(v_a_4477_);
v___x_4492_ = lean_apply_13(v_k_4475_, v_acc_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, lean_box(0));
return v___x_4492_;
}
else
{
lean_object* v___x_4493_; lean_object* v_snd_4494_; lean_object* v_fst_4495_; lean_object* v_fst_4496_; lean_object* v_snd_4497_; lean_object* v___f_4498_; uint8_t v___x_4499_; uint8_t v___x_4500_; lean_object* v___x_4501_; 
v___x_4493_ = lean_array_fget_borrowed(v_declInfos_4474_, v___x_4489_);
v_snd_4494_ = lean_ctor_get(v___x_4493_, 1);
v_fst_4495_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_fst_4495_);
v_fst_4496_ = lean_ctor_get(v_snd_4494_, 0);
lean_inc(v_fst_4496_);
v_snd_4497_ = lean_ctor_get(v_snd_4494_, 1);
lean_inc(v_snd_4497_);
v___f_4498_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4498_, 0, v_acc_4476_);
lean_closure_set(v___f_4498_, 1, v_declInfos_4474_);
lean_closure_set(v___f_4498_, 2, v_k_4475_);
v___x_4499_ = 0;
v___x_4500_ = 0;
v___x_4501_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_fst_4495_, v_fst_4496_, v_snd_4497_, v___f_4498_, v___x_4499_, v___x_4500_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
return v___x_4501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0(lean_object* v_acc_4502_, lean_object* v_declInfos_4503_, lean_object* v_k_4504_, lean_object* v_fv_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4518_ = lean_array_push(v_acc_4502_, v_fv_4505_);
v___x_4519_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4503_, v_k_4504_, v___x_4518_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___boxed(lean_object* v_declInfos_4520_, lean_object* v_k_4521_, lean_object* v_acc_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4520_, v_k_4521_, v_acc_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec(v_a_4529_);
lean_dec_ref(v_a_4528_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec(v_a_4524_);
lean_dec_ref(v_a_4523_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_match__1_splitter___redArg(lean_object* v_x_4536_, lean_object* v_h__1_4537_){
_start:
{
lean_object* v_snd_4538_; lean_object* v_fst_4539_; lean_object* v_fst_4540_; lean_object* v_snd_4541_; lean_object* v___x_4542_; 
v_snd_4538_ = lean_ctor_get(v_x_4536_, 1);
lean_inc(v_snd_4538_);
v_fst_4539_ = lean_ctor_get(v_x_4536_, 0);
lean_inc(v_fst_4539_);
lean_dec_ref(v_x_4536_);
v_fst_4540_ = lean_ctor_get(v_snd_4538_, 0);
lean_inc(v_fst_4540_);
v_snd_4541_ = lean_ctor_get(v_snd_4538_, 1);
lean_inc(v_snd_4541_);
lean_dec(v_snd_4538_);
v___x_4542_ = lean_apply_3(v_h__1_4537_, v_fst_4539_, v_fst_4540_, v_snd_4541_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_match__1_splitter(lean_object* v_motive_4543_, lean_object* v_x_4544_, lean_object* v_h__1_4545_){
_start:
{
lean_object* v_snd_4546_; lean_object* v_fst_4547_; lean_object* v_fst_4548_; lean_object* v_snd_4549_; lean_object* v___x_4550_; 
v_snd_4546_ = lean_ctor_get(v_x_4544_, 1);
lean_inc(v_snd_4546_);
v_fst_4547_ = lean_ctor_get(v_x_4544_, 0);
lean_inc(v_fst_4547_);
lean_dec_ref(v_x_4544_);
v_fst_4548_ = lean_ctor_get(v_snd_4546_, 0);
lean_inc(v_fst_4548_);
v_snd_4549_ = lean_ctor_get(v_snd_4546_, 1);
lean_inc(v_snd_4549_);
lean_dec(v_snd_4546_);
v___x_4550_ = lean_apply_3(v_h__1_4545_, v_fst_4547_, v_fst_4548_, v_snd_4549_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND(lean_object* v_declInfos_4553_, lean_object* v_k_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___closed__0));
v___x_4568_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4553_, v_k_4554_, v___x_4567_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___boxed(lean_object* v_declInfos_4569_, lean_object* v_k_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_){
_start:
{
lean_object* v_res_4583_; 
v_res_4583_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND(v_declInfos_4569_, v_k_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_);
lean_dec(v_a_4581_);
lean_dec_ref(v_a_4580_);
lean_dec(v_a_4579_);
lean_dec_ref(v_a_4578_);
lean_dec(v_a_4577_);
lean_dec_ref(v_a_4576_);
lean_dec(v_a_4575_);
lean_dec_ref(v_a_4574_);
lean_dec(v_a_4573_);
lean_dec(v_a_4572_);
lean_dec_ref(v_a_4571_);
return v_res_4583_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0(lean_object* v_x_4584_){
_start:
{
uint8_t v___x_4585_; 
v___x_4585_ = 0;
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0___boxed(lean_object* v_x_4586_){
_start:
{
uint8_t v_res_4587_; lean_object* v_r_4588_; 
v_res_4587_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0(v_x_4586_);
lean_dec(v_x_4586_);
v_r_4588_ = lean_box(v_res_4587_);
return v_r_4588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1(lean_object* v_frameStx_4589_, lean_object* v___x_4590_, uint8_t v___x_4591_, lean_object* v___x_4592_, lean_object* v_fvs_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = l_Lean_Elab_Term_elabTermEnsuringType(v_frameStx_4589_, v___x_4590_, v___x_4591_, v___x_4591_, v___x_4592_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v_a_4602_; uint8_t v___x_4603_; lean_object* v___x_4604_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_a_4602_);
lean_dec_ref_known(v___x_4601_, 1);
v___x_4603_ = 0;
v___x_4604_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4603_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
if (lean_obj_tag(v___x_4604_) == 0)
{
uint8_t v___x_4605_; lean_object* v___x_4606_; 
lean_dec_ref_known(v___x_4604_, 1);
v___x_4605_ = 1;
v___x_4606_ = l_Lean_Meta_mkLetFVars(v_fvs_4593_, v_a_4602_, v___x_4591_, v___x_4591_, v___x_4605_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
return v___x_4606_;
}
else
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
lean_dec(v_a_4602_);
v_a_4607_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4604_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4604_);
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
return v___x_4601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1___boxed(lean_object* v_frameStx_4615_, lean_object* v___x_4616_, lean_object* v___x_4617_, lean_object* v___x_4618_, lean_object* v_fvs_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
uint8_t v___x_12406__boxed_4627_; lean_object* v_res_4628_; 
v___x_12406__boxed_4627_ = lean_unbox(v___x_4617_);
v_res_4628_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1(v_frameStx_4615_, v___x_4616_, v___x_12406__boxed_4627_, v___x_4618_, v_fvs_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
lean_dec_ref(v_fvs_4619_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2(lean_object* v_resourceTy_4634_, lean_object* v_frameStx_4635_, lean_object* v___f_4636_, lean_object* v_fvs_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v___x_4650_; uint8_t v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___f_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; uint8_t v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4650_, 0, v_resourceTy_4634_);
v___x_4651_ = 1;
v___x_4652_ = lean_box(0);
v___x_4653_ = lean_box(v___x_4651_);
v___f_4654_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4654_, 0, v_frameStx_4635_);
lean_closure_set(v___f_4654_, 1, v___x_4650_);
lean_closure_set(v___f_4654_, 2, v___x_4653_);
lean_closure_set(v___f_4654_, 3, v___x_4652_);
lean_closure_set(v___f_4654_, 4, v_fvs_4637_);
v___x_4655_ = lean_box(0);
v___x_4656_ = lean_box(1);
v___x_4657_ = 0;
v___x_4658_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__0));
v___x_4659_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_4659_, 0, v___x_4652_);
lean_ctor_set(v___x_4659_, 1, v___x_4655_);
lean_ctor_set(v___x_4659_, 2, v___x_4652_);
lean_ctor_set(v___x_4659_, 3, v___f_4636_);
lean_ctor_set(v___x_4659_, 4, v___x_4656_);
lean_ctor_set(v___x_4659_, 5, v___x_4656_);
lean_ctor_set(v___x_4659_, 6, v___x_4652_);
lean_ctor_set(v___x_4659_, 7, v___x_4658_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*8, v___x_4651_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*8 + 1, v___x_4651_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*8 + 2, v___x_4651_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*8 + 3, v___x_4651_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*8 + 4, v___x_4657_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*8 + 5, v___x_4657_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*8 + 6, v___x_4657_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*8 + 7, v___x_4657_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*8 + 8, v___x_4651_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*8 + 9, v___x_4657_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*8 + 10, v___x_4651_);
v___x_4660_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__1));
v___x_4661_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_4654_, v___x_4659_, v___x_4660_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4661_) == 0)
{
lean_object* v_a_4662_; lean_object* v_fst_4663_; lean_object* v___x_4664_; 
v_a_4662_ = lean_ctor_get(v___x_4661_, 0);
lean_inc(v_a_4662_);
lean_dec_ref_known(v___x_4661_, 1);
v_fst_4663_ = lean_ctor_get(v_a_4662_, 0);
lean_inc(v_fst_4663_);
lean_dec(v_a_4662_);
v___x_4664_ = l_Lean_Meta_Sym_instantiateMVarsS(v_fst_4663_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
return v___x_4664_;
}
else
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4672_; 
v_a_4665_ = lean_ctor_get(v___x_4661_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4661_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4667_ = v___x_4661_;
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4661_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4670_; 
if (v_isShared_4668_ == 0)
{
v___x_4670_ = v___x_4667_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4665_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___boxed(lean_object* v_resourceTy_4673_, lean_object* v_frameStx_4674_, lean_object* v___f_4675_, lean_object* v_fvs_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2(v_resourceTy_4673_, v_frameStx_4674_, v___f_4675_, v_fvs_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(lean_object* v_as_4690_, size_t v_sz_4691_, size_t v_i_4692_, lean_object* v_b_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v_a_4700_; uint8_t v___x_4704_; 
v___x_4704_ = lean_usize_dec_lt(v_i_4692_, v_sz_4691_);
if (v___x_4704_ == 0)
{
lean_object* v___x_4705_; 
v___x_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4705_, 0, v_b_4693_);
return v___x_4705_;
}
else
{
lean_object* v_snd_4706_; lean_object* v_fst_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4753_; 
v_snd_4706_ = lean_ctor_get(v_b_4693_, 1);
v_fst_4707_ = lean_ctor_get(v_b_4693_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v_b_4693_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4709_ = v_b_4693_;
v_isShared_4710_ = v_isSharedCheck_4753_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_snd_4706_);
lean_inc(v_fst_4707_);
lean_dec(v_b_4693_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4753_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v_array_4711_; lean_object* v_start_4712_; lean_object* v_stop_4713_; uint8_t v___x_4714_; 
v_array_4711_ = lean_ctor_get(v_snd_4706_, 0);
v_start_4712_ = lean_ctor_get(v_snd_4706_, 1);
v_stop_4713_ = lean_ctor_get(v_snd_4706_, 2);
v___x_4714_ = lean_nat_dec_lt(v_start_4712_, v_stop_4713_);
if (v___x_4714_ == 0)
{
lean_object* v___x_4716_; 
if (v_isShared_4710_ == 0)
{
v___x_4716_ = v___x_4709_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_fst_4707_);
lean_ctor_set(v_reuseFailAlloc_4718_, 1, v_snd_4706_);
v___x_4716_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
lean_object* v___x_4717_; 
v___x_4717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4716_);
return v___x_4717_;
}
}
else
{
lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4749_; 
lean_inc(v_stop_4713_);
lean_inc(v_start_4712_);
lean_inc_ref(v_array_4711_);
v_isSharedCheck_4749_ = !lean_is_exclusive(v_snd_4706_);
if (v_isSharedCheck_4749_ == 0)
{
lean_object* v_unused_4750_; lean_object* v_unused_4751_; lean_object* v_unused_4752_; 
v_unused_4750_ = lean_ctor_get(v_snd_4706_, 2);
lean_dec(v_unused_4750_);
v_unused_4751_ = lean_ctor_get(v_snd_4706_, 1);
lean_dec(v_unused_4751_);
v_unused_4752_ = lean_ctor_get(v_snd_4706_, 0);
lean_dec(v_unused_4752_);
v___x_4720_ = v_snd_4706_;
v_isShared_4721_ = v_isSharedCheck_4749_;
goto v_resetjp_4719_;
}
else
{
lean_dec(v_snd_4706_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4749_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v_a_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4727_; 
v_a_4722_ = lean_array_uget_borrowed(v_as_4690_, v_i_4692_);
v___x_4723_ = lean_array_fget(v_array_4711_, v_start_4712_);
v___x_4724_ = lean_unsigned_to_nat(1u);
v___x_4725_ = lean_nat_add(v_start_4712_, v___x_4724_);
lean_dec(v_start_4712_);
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 1, v___x_4725_);
v___x_4727_ = v___x_4720_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_array_4711_);
lean_ctor_set(v_reuseFailAlloc_4748_, 1, v___x_4725_);
lean_ctor_set(v_reuseFailAlloc_4748_, 2, v_stop_4713_);
v___x_4727_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
if (lean_obj_tag(v_a_4722_) == 1)
{
lean_object* v_val_4728_; lean_object* v___x_4729_; 
v_val_4728_ = lean_ctor_get(v_a_4722_, 0);
lean_inc(v___y_4697_);
lean_inc_ref(v___y_4696_);
lean_inc(v___y_4695_);
lean_inc_ref(v___y_4694_);
lean_inc(v___x_4723_);
v___x_4729_ = lean_infer_type(v___x_4723_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4732_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
lean_inc(v_a_4730_);
lean_dec_ref_known(v___x_4729_, 1);
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 1, v___x_4723_);
lean_ctor_set(v___x_4709_, 0, v_a_4730_);
v___x_4732_ = v___x_4709_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
lean_ctor_set(v_reuseFailAlloc_4736_, 1, v___x_4723_);
v___x_4732_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
lean_inc(v_val_4728_);
v___x_4733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4733_, 0, v_val_4728_);
lean_ctor_set(v___x_4733_, 1, v___x_4732_);
v___x_4734_ = lean_array_push(v_fst_4707_, v___x_4733_);
v___x_4735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4735_, 0, v___x_4734_);
lean_ctor_set(v___x_4735_, 1, v___x_4727_);
v_a_4700_ = v___x_4735_;
goto v___jp_4699_;
}
}
else
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
lean_dec_ref(v___x_4727_);
lean_dec(v___x_4723_);
lean_del_object(v___x_4709_);
lean_dec(v_fst_4707_);
v_a_4737_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4739_ = v___x_4729_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4729_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4737_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
}
else
{
lean_object* v___x_4746_; 
lean_dec(v___x_4723_);
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 1, v___x_4727_);
v___x_4746_ = v___x_4709_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_fst_4707_);
lean_ctor_set(v_reuseFailAlloc_4747_, 1, v___x_4727_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
v_a_4700_ = v___x_4746_;
goto v___jp_4699_;
}
}
}
}
}
}
}
v___jp_4699_:
{
size_t v___x_4701_; size_t v___x_4702_; 
v___x_4701_ = ((size_t)1ULL);
v___x_4702_ = lean_usize_add(v_i_4692_, v___x_4701_);
v_i_4692_ = v___x_4702_;
v_b_4693_ = v_a_4700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg___boxed(lean_object* v_as_4754_, lean_object* v_sz_4755_, lean_object* v_i_4756_, lean_object* v_b_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_){
_start:
{
size_t v_sz_boxed_4763_; size_t v_i_boxed_4764_; lean_object* v_res_4765_; 
v_sz_boxed_4763_ = lean_unbox_usize(v_sz_4755_);
lean_dec(v_sz_4755_);
v_i_boxed_4764_ = lean_unbox_usize(v_i_4756_);
lean_dec(v_i_4756_);
v_res_4765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_as_4754_, v_sz_boxed_4763_, v_i_boxed_4764_, v_b_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec_ref(v_as_4754_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(lean_object* v_resourceTy_4769_, lean_object* v_entry_4770_, lean_object* v_res_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_){
_start:
{
lean_object* v_args_4784_; lean_object* v_varNames_4785_; lean_object* v_frameStx_4786_; lean_object* v___x_4787_; lean_object* v_decls_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; size_t v_sz_4792_; size_t v___x_4793_; lean_object* v___x_4794_; 
v_args_4784_ = lean_ctor_get(v_res_4771_, 1);
lean_inc_ref(v_args_4784_);
lean_dec_ref(v_res_4771_);
v_varNames_4785_ = lean_ctor_get(v_entry_4770_, 1);
lean_inc_ref(v_varNames_4785_);
v_frameStx_4786_ = lean_ctor_get(v_entry_4770_, 2);
lean_inc(v_frameStx_4786_);
lean_dec_ref(v_entry_4770_);
v___x_4787_ = lean_unsigned_to_nat(0u);
v_decls_4788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__0));
v___x_4789_ = lean_array_get_size(v_args_4784_);
v___x_4790_ = l_Array_toSubarray___redArg(v_args_4784_, v___x_4787_, v___x_4789_);
v___x_4791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4791_, 0, v_decls_4788_);
lean_ctor_set(v___x_4791_, 1, v___x_4790_);
v_sz_4792_ = lean_array_size(v_varNames_4785_);
v___x_4793_ = ((size_t)0ULL);
v___x_4794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_varNames_4785_, v_sz_4792_, v___x_4793_, v___x_4791_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_);
lean_dec_ref(v_varNames_4785_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v_a_4795_; lean_object* v_fst_4796_; lean_object* v_keyedConfig_4797_; uint8_t v_trackZetaDelta_4798_; lean_object* v_zetaDeltaSet_4799_; lean_object* v_lctx_4800_; lean_object* v_localInstances_4801_; lean_object* v_defEqCtx_x3f_4802_; lean_object* v_synthPendingDepth_4803_; lean_object* v_customCanUnfoldPredicate_x3f_4804_; uint8_t v_univApprox_4805_; uint8_t v_inTypeClassResolution_4806_; uint8_t v_cacheInferType_4807_; lean_object* v___f_4808_; lean_object* v___f_4809_; uint8_t v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v_a_4795_ = lean_ctor_get(v___x_4794_, 0);
lean_inc(v_a_4795_);
lean_dec_ref_known(v___x_4794_, 1);
v_fst_4796_ = lean_ctor_get(v_a_4795_, 0);
lean_inc(v_fst_4796_);
lean_dec(v_a_4795_);
v_keyedConfig_4797_ = lean_ctor_get(v_a_4779_, 0);
v_trackZetaDelta_4798_ = lean_ctor_get_uint8(v_a_4779_, sizeof(void*)*7);
v_zetaDeltaSet_4799_ = lean_ctor_get(v_a_4779_, 1);
v_lctx_4800_ = lean_ctor_get(v_a_4779_, 2);
v_localInstances_4801_ = lean_ctor_get(v_a_4779_, 3);
v_defEqCtx_x3f_4802_ = lean_ctor_get(v_a_4779_, 4);
v_synthPendingDepth_4803_ = lean_ctor_get(v_a_4779_, 5);
v_customCanUnfoldPredicate_x3f_4804_ = lean_ctor_get(v_a_4779_, 6);
v_univApprox_4805_ = lean_ctor_get_uint8(v_a_4779_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4806_ = lean_ctor_get_uint8(v_a_4779_, sizeof(void*)*7 + 2);
v_cacheInferType_4807_ = lean_ctor_get_uint8(v_a_4779_, sizeof(void*)*7 + 3);
v___f_4808_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__1));
v___f_4809_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___boxed), 16, 3);
lean_closure_set(v___f_4809_, 0, v_resourceTy_4769_);
lean_closure_set(v___f_4809_, 1, v_frameStx_4786_);
lean_closure_set(v___f_4809_, 2, v___f_4808_);
v___x_4810_ = 1;
lean_inc_ref(v_keyedConfig_4797_);
v___x_4811_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4810_, v_keyedConfig_4797_);
lean_inc(v_customCanUnfoldPredicate_x3f_4804_);
lean_inc(v_synthPendingDepth_4803_);
lean_inc(v_defEqCtx_x3f_4802_);
lean_inc_ref(v_localInstances_4801_);
lean_inc_ref(v_lctx_4800_);
lean_inc(v_zetaDeltaSet_4799_);
v___x_4812_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4812_, 0, v___x_4811_);
lean_ctor_set(v___x_4812_, 1, v_zetaDeltaSet_4799_);
lean_ctor_set(v___x_4812_, 2, v_lctx_4800_);
lean_ctor_set(v___x_4812_, 3, v_localInstances_4801_);
lean_ctor_set(v___x_4812_, 4, v_defEqCtx_x3f_4802_);
lean_ctor_set(v___x_4812_, 5, v_synthPendingDepth_4803_);
lean_ctor_set(v___x_4812_, 6, v_customCanUnfoldPredicate_x3f_4804_);
lean_ctor_set_uint8(v___x_4812_, sizeof(void*)*7, v_trackZetaDelta_4798_);
lean_ctor_set_uint8(v___x_4812_, sizeof(void*)*7 + 1, v_univApprox_4805_);
lean_ctor_set_uint8(v___x_4812_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4806_);
lean_ctor_set_uint8(v___x_4812_, sizeof(void*)*7 + 3, v_cacheInferType_4807_);
v___x_4813_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_fst_4796_, v___f_4809_, v_decls_4788_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v___x_4812_, v_a_4780_, v_a_4781_, v_a_4782_);
lean_dec_ref_known(v___x_4812_, 7);
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
return v___x_4813_;
}
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_dec(v_frameStx_4786_);
lean_dec_ref(v_resourceTy_4769_);
v_a_4822_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4794_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4794_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___boxed(lean_object* v_resourceTy_4830_, lean_object* v_entry_4831_, lean_object* v_res_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(v_resourceTy_4830_, v_entry_4831_, v_res_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_);
lean_dec(v_a_4843_);
lean_dec_ref(v_a_4842_);
lean_dec(v_a_4841_);
lean_dec_ref(v_a_4840_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
lean_dec(v_a_4837_);
lean_dec_ref(v_a_4836_);
lean_dec(v_a_4835_);
lean_dec(v_a_4834_);
lean_dec_ref(v_a_4833_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0(lean_object* v_as_4846_, size_t v_sz_4847_, size_t v_i_4848_, lean_object* v_b_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
lean_object* v___x_4862_; 
v___x_4862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_as_4846_, v_sz_4847_, v_i_4848_, v_b_4849_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___boxed(lean_object* v_as_4863_, lean_object* v_sz_4864_, lean_object* v_i_4865_, lean_object* v_b_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_){
_start:
{
size_t v_sz_boxed_4879_; size_t v_i_boxed_4880_; lean_object* v_res_4881_; 
v_sz_boxed_4879_ = lean_unbox_usize(v_sz_4864_);
lean_dec(v_sz_4864_);
v_i_boxed_4880_ = lean_unbox_usize(v_i_4865_);
lean_dec(v_i_4865_);
v_res_4881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0(v_as_4863_, v_sz_boxed_4879_, v_i_boxed_4880_, v_b_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
lean_dec(v___y_4877_);
lean_dec_ref(v___y_4876_);
lean_dec(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec(v___y_4868_);
lean_dec_ref(v___y_4867_);
lean_dec_ref(v_as_4863_);
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(lean_object* v___x_4882_, lean_object* v___x_4883_, lean_object* v_as_4884_, size_t v_sz_4885_, size_t v_i_4886_, lean_object* v_b_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v_a_4896_; uint8_t v___x_4900_; 
v___x_4900_ = lean_usize_dec_lt(v_i_4886_, v_sz_4885_);
if (v___x_4900_ == 0)
{
lean_object* v___x_4901_; 
lean_dec_ref(v___x_4883_);
v___x_4901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4901_, 0, v_b_4887_);
return v___x_4901_;
}
else
{
lean_object* v_a_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; uint8_t v_retired_4905_; 
v_a_4902_ = lean_array_uget_borrowed(v_as_4884_, v_i_4886_);
v___x_4903_ = l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default;
v___x_4904_ = lean_array_get_borrowed(v___x_4903_, v___x_4882_, v_a_4902_);
v_retired_4905_ = lean_ctor_get_uint8(v___x_4904_, sizeof(void*)*4);
if (v_retired_4905_ == 0)
{
lean_object* v_pat_4906_; lean_object* v_srcIdx_4907_; lean_object* v___x_4908_; 
v_pat_4906_ = lean_ctor_get(v___x_4904_, 0);
v_srcIdx_4907_ = lean_ctor_get(v___x_4904_, 3);
lean_inc_ref(v___x_4883_);
lean_inc_ref(v_pat_4906_);
v___x_4908_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pat_4906_, v___x_4883_, v___x_4900_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4909_);
lean_dec_ref_known(v___x_4908_, 1);
if (lean_obj_tag(v_a_4909_) == 1)
{
if (lean_obj_tag(v_b_4887_) == 0)
{
lean_object* v_val_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4918_; 
v_val_4910_ = lean_ctor_get(v_a_4909_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v_a_4909_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4912_ = v_a_4909_;
v_isShared_4913_ = v_isSharedCheck_4918_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_val_4910_);
lean_dec(v_a_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4918_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4914_; lean_object* v___x_4916_; 
lean_inc(v___x_4904_);
v___x_4914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4904_);
lean_ctor_set(v___x_4914_, 1, v_val_4910_);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v___x_4914_);
v___x_4916_ = v___x_4912_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v___x_4914_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
v_a_4896_ = v___x_4916_;
goto v___jp_4895_;
}
}
}
else
{
lean_object* v_val_4919_; lean_object* v_fst_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4938_; 
v_val_4919_ = lean_ctor_get(v_b_4887_, 0);
lean_inc(v_val_4919_);
v_fst_4920_ = lean_ctor_get(v_val_4919_, 0);
v_isSharedCheck_4938_ = !lean_is_exclusive(v_val_4919_);
if (v_isSharedCheck_4938_ == 0)
{
lean_object* v_unused_4939_; 
v_unused_4939_ = lean_ctor_get(v_val_4919_, 1);
lean_dec(v_unused_4939_);
v___x_4922_ = v_val_4919_;
v_isShared_4923_ = v_isSharedCheck_4938_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_fst_4920_);
lean_dec(v_val_4919_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4938_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v_val_4924_; lean_object* v_srcIdx_4925_; uint8_t v___x_4926_; 
v_val_4924_ = lean_ctor_get(v_a_4909_, 0);
lean_inc(v_val_4924_);
lean_dec_ref_known(v_a_4909_, 1);
v_srcIdx_4925_ = lean_ctor_get(v_fst_4920_, 3);
lean_inc(v_srcIdx_4925_);
lean_dec(v_fst_4920_);
v___x_4926_ = lean_nat_dec_lt(v_srcIdx_4907_, v_srcIdx_4925_);
lean_dec(v_srcIdx_4925_);
if (v___x_4926_ == 0)
{
lean_dec(v_val_4924_);
lean_del_object(v___x_4922_);
v_a_4896_ = v_b_4887_;
goto v___jp_4895_;
}
else
{
lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4936_; 
v_isSharedCheck_4936_ = !lean_is_exclusive(v_b_4887_);
if (v_isSharedCheck_4936_ == 0)
{
lean_object* v_unused_4937_; 
v_unused_4937_ = lean_ctor_get(v_b_4887_, 0);
lean_dec(v_unused_4937_);
v___x_4928_ = v_b_4887_;
v_isShared_4929_ = v_isSharedCheck_4936_;
goto v_resetjp_4927_;
}
else
{
lean_dec(v_b_4887_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4936_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4931_; 
lean_inc(v___x_4904_);
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 1, v_val_4924_);
lean_ctor_set(v___x_4922_, 0, v___x_4904_);
v___x_4931_ = v___x_4922_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4904_);
lean_ctor_set(v_reuseFailAlloc_4935_, 1, v_val_4924_);
v___x_4931_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4933_; 
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 0, v___x_4931_);
v___x_4933_ = v___x_4928_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
v_a_4896_ = v___x_4933_;
goto v___jp_4895_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_4909_);
v_a_4896_ = v_b_4887_;
goto v___jp_4895_;
}
}
else
{
lean_object* v_a_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4947_; 
lean_dec(v_b_4887_);
lean_dec_ref(v___x_4883_);
v_a_4940_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4942_ = v___x_4908_;
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_a_4940_);
lean_dec(v___x_4908_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4945_; 
if (v_isShared_4943_ == 0)
{
v___x_4945_ = v___x_4942_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4940_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
}
else
{
v_a_4896_ = v_b_4887_;
goto v___jp_4895_;
}
}
v___jp_4895_:
{
size_t v___x_4897_; size_t v___x_4898_; 
v___x_4897_ = ((size_t)1ULL);
v___x_4898_ = lean_usize_add(v_i_4886_, v___x_4897_);
v_i_4886_ = v___x_4898_;
v_b_4887_ = v_a_4896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object* v___x_4948_, lean_object* v___x_4949_, lean_object* v_as_4950_, lean_object* v_sz_4951_, lean_object* v_i_4952_, lean_object* v_b_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_){
_start:
{
size_t v_sz_boxed_4961_; size_t v_i_boxed_4962_; lean_object* v_res_4963_; 
v_sz_boxed_4961_ = lean_unbox_usize(v_sz_4951_);
lean_dec(v_sz_4951_);
v_i_boxed_4962_ = lean_unbox_usize(v_i_4952_);
lean_dec(v_i_4952_);
v_res_4963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v___x_4948_, v___x_4949_, v_as_4950_, v_sz_boxed_4961_, v_i_boxed_4962_, v_b_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
lean_dec(v___y_4957_);
lean_dec_ref(v___y_4956_);
lean_dec(v___y_4955_);
lean_dec_ref(v___y_4954_);
lean_dec_ref(v_as_4950_);
lean_dec_ref(v___x_4948_);
return v_res_4963_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1(void){
_start:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4965_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__0));
v___x_4966_ = l_Lean_stringToMessageData(v___x_4965_);
return v___x_4966_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3(void){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4968_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__2));
v___x_4969_ = l_Lean_stringToMessageData(v___x_4968_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(lean_object* v_fp_4970_, lean_object* v_info_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_){
_start:
{
lean_object* v___x_4984_; lean_object* v_frameDB_4985_; lean_object* v_tree_4986_; lean_object* v_entries_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_5124_; 
v___x_4984_ = lean_st_ref_get(v_a_4973_);
v_frameDB_4985_ = lean_ctor_get(v___x_4984_, 4);
lean_inc_ref(v_frameDB_4985_);
lean_dec(v___x_4984_);
v_tree_4986_ = lean_ctor_get(v_frameDB_4985_, 0);
v_entries_4987_ = lean_ctor_get(v_frameDB_4985_, 1);
v_isSharedCheck_5124_ = !lean_is_exclusive(v_frameDB_4985_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_4989_ = v_frameDB_4985_;
v_isShared_4990_ = v_isSharedCheck_5124_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_entries_4987_);
lean_inc(v_tree_4986_);
lean_dec(v_frameDB_4985_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_5124_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; uint8_t v___x_4993_; 
v___x_4991_ = lean_array_get_size(v_entries_4987_);
v___x_4992_ = lean_unsigned_to_nat(0u);
v___x_4993_ = lean_nat_dec_eq(v___x_4991_, v___x_4992_);
if (v___x_4993_ == 0)
{
lean_object* v___x_4994_; lean_object* v_mctx_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; size_t v_sz_4999_; size_t v___x_5000_; lean_object* v___x_5001_; 
v___x_4994_ = lean_st_ref_get(v_a_4980_);
v_mctx_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc_ref(v_mctx_4995_);
lean_dec(v___x_4994_);
v___x_4996_ = lean_box(0);
v___x_4997_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_4971_);
v___x_4998_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_4995_, v_tree_4986_, v___x_4997_);
lean_dec_ref(v_tree_4986_);
lean_dec_ref(v_mctx_4995_);
v_sz_4999_ = lean_array_size(v___x_4998_);
v___x_5000_ = ((size_t)0ULL);
lean_inc_ref(v___x_4997_);
v___x_5001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v_entries_4987_, v___x_4997_, v___x_4998_, v_sz_4999_, v___x_5000_, v___x_4996_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_);
lean_dec_ref(v___x_4998_);
lean_dec_ref(v_entries_4987_);
if (lean_obj_tag(v___x_5001_) == 0)
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5113_; 
v_a_5002_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5004_ = v___x_5001_;
v_isShared_5005_ = v_isSharedCheck_5113_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_5001_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5113_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
if (lean_obj_tag(v_a_5002_) == 1)
{
lean_object* v_val_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5109_; 
lean_del_object(v___x_5004_);
v_val_5006_ = lean_ctor_get(v_a_5002_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v_a_5002_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_5008_ = v_a_5002_;
v_isShared_5009_ = v_isSharedCheck_5109_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_val_5006_);
lean_dec(v_a_5002_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5109_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v_fst_5010_; lean_object* v_snd_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5108_; 
v_fst_5010_ = lean_ctor_get(v_val_5006_, 0);
v_snd_5011_ = lean_ctor_get(v_val_5006_, 1);
v_isSharedCheck_5108_ = !lean_is_exclusive(v_val_5006_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5013_ = v_val_5006_;
v_isShared_5014_ = v_isSharedCheck_5108_;
goto v_resetjp_5012_;
}
else
{
lean_inc(v_snd_5011_);
lean_inc(v_fst_5010_);
lean_dec(v_val_5006_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5108_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
lean_object* v___x_5015_; lean_object* v_frameDB_5016_; lean_object* v_specBackwardRuleCache_5017_; lean_object* v_splitBackwardRuleCache_5018_; lean_object* v_latticeBackwardRuleCache_5019_; lean_object* v_frameBackwardRuleCache_5020_; lean_object* v_invariants_5021_; lean_object* v_vcs_5022_; lean_object* v_simpState_5023_; lean_object* v_fuel_5024_; lean_object* v_inlineHandledInvariants_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5107_; 
v___x_5015_ = lean_st_ref_take(v_a_4973_);
v_frameDB_5016_ = lean_ctor_get(v___x_5015_, 4);
v_specBackwardRuleCache_5017_ = lean_ctor_get(v___x_5015_, 0);
v_splitBackwardRuleCache_5018_ = lean_ctor_get(v___x_5015_, 1);
v_latticeBackwardRuleCache_5019_ = lean_ctor_get(v___x_5015_, 2);
v_frameBackwardRuleCache_5020_ = lean_ctor_get(v___x_5015_, 3);
v_invariants_5021_ = lean_ctor_get(v___x_5015_, 5);
v_vcs_5022_ = lean_ctor_get(v___x_5015_, 6);
v_simpState_5023_ = lean_ctor_get(v___x_5015_, 7);
v_fuel_5024_ = lean_ctor_get(v___x_5015_, 8);
v_inlineHandledInvariants_5025_ = lean_ctor_get(v___x_5015_, 9);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5027_ = v___x_5015_;
v_isShared_5028_ = v_isSharedCheck_5107_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_inlineHandledInvariants_5025_);
lean_inc(v_fuel_5024_);
lean_inc(v_simpState_5023_);
lean_inc(v_vcs_5022_);
lean_inc(v_invariants_5021_);
lean_inc(v_frameDB_5016_);
lean_inc(v_frameBackwardRuleCache_5020_);
lean_inc(v_latticeBackwardRuleCache_5019_);
lean_inc(v_splitBackwardRuleCache_5018_);
lean_inc(v_specBackwardRuleCache_5017_);
lean_dec(v___x_5015_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5107_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v_tree_5029_; lean_object* v_entries_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5106_; 
v_tree_5029_ = lean_ctor_get(v_frameDB_5016_, 0);
v_entries_5030_ = lean_ctor_get(v_frameDB_5016_, 1);
v_isSharedCheck_5106_ = !lean_is_exclusive(v_frameDB_5016_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_5032_ = v_frameDB_5016_;
v_isShared_5033_ = v_isSharedCheck_5106_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_entries_5030_);
lean_inc(v_tree_5029_);
lean_dec(v_frameDB_5016_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5106_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v_pat_5034_; lean_object* v_varNames_5035_; lean_object* v_frameStx_5036_; lean_object* v_srcIdx_5037_; uint8_t v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5042_; 
v_pat_5034_ = lean_ctor_get(v_fst_5010_, 0);
v_varNames_5035_ = lean_ctor_get(v_fst_5010_, 1);
v_frameStx_5036_ = lean_ctor_get(v_fst_5010_, 2);
v_srcIdx_5037_ = lean_ctor_get(v_fst_5010_, 3);
v___x_5038_ = 1;
lean_inc(v_srcIdx_5037_);
lean_inc(v_frameStx_5036_);
lean_inc_ref(v_varNames_5035_);
lean_inc_ref(v_pat_5034_);
v___x_5039_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_5039_, 0, v_pat_5034_);
lean_ctor_set(v___x_5039_, 1, v_varNames_5035_);
lean_ctor_set(v___x_5039_, 2, v_frameStx_5036_);
lean_ctor_set(v___x_5039_, 3, v_srcIdx_5037_);
lean_ctor_set_uint8(v___x_5039_, sizeof(void*)*4, v___x_5038_);
v___x_5040_ = lean_array_set(v_entries_5030_, v_srcIdx_5037_, v___x_5039_);
if (v_isShared_5033_ == 0)
{
lean_ctor_set(v___x_5032_, 1, v___x_5040_);
v___x_5042_ = v___x_5032_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_tree_5029_);
lean_ctor_set(v_reuseFailAlloc_5105_, 1, v___x_5040_);
v___x_5042_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
lean_object* v___x_5044_; 
if (v_isShared_5028_ == 0)
{
lean_ctor_set(v___x_5027_, 4, v___x_5042_);
v___x_5044_ = v___x_5027_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_specBackwardRuleCache_5017_);
lean_ctor_set(v_reuseFailAlloc_5104_, 1, v_splitBackwardRuleCache_5018_);
lean_ctor_set(v_reuseFailAlloc_5104_, 2, v_latticeBackwardRuleCache_5019_);
lean_ctor_set(v_reuseFailAlloc_5104_, 3, v_frameBackwardRuleCache_5020_);
lean_ctor_set(v_reuseFailAlloc_5104_, 4, v___x_5042_);
lean_ctor_set(v_reuseFailAlloc_5104_, 5, v_invariants_5021_);
lean_ctor_set(v_reuseFailAlloc_5104_, 6, v_vcs_5022_);
lean_ctor_set(v_reuseFailAlloc_5104_, 7, v_simpState_5023_);
lean_ctor_set(v_reuseFailAlloc_5104_, 8, v_fuel_5024_);
lean_ctor_set(v_reuseFailAlloc_5104_, 9, v_inlineHandledInvariants_5025_);
v___x_5044_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
lean_object* v___x_5045_; lean_object* v_mkResourceTy_5046_; lean_object* v___x_5047_; 
v___x_5045_ = lean_st_ref_put(v_a_4973_, v___x_5044_);
v_mkResourceTy_5046_ = lean_ctor_get(v_fp_4970_, 3);
lean_inc_ref(v_mkResourceTy_5046_);
lean_dec_ref(v_fp_4970_);
lean_inc(v_a_4982_);
lean_inc_ref(v_a_4981_);
lean_inc(v_a_4980_);
lean_inc_ref(v_a_4979_);
v___x_5047_ = lean_apply_6(v_mkResourceTy_5046_, v_info_4971_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, lean_box(0));
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v___x_5049_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
lean_inc(v_a_5048_);
lean_dec_ref_known(v___x_5047_, 1);
v___x_5049_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(v_a_5048_, v_fst_5010_, v_snd_5011_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5087_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5052_ = v___x_5049_;
v_isShared_5053_ = v_isSharedCheck_5087_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5049_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5087_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v_options_5061_; uint8_t v_hasTrace_5062_; 
v_options_5061_ = lean_ctor_get(v_a_4981_, 2);
v_hasTrace_5062_ = lean_ctor_get_uint8(v_options_5061_, sizeof(void*)*1);
if (v_hasTrace_5062_ == 0)
{
lean_del_object(v___x_5013_);
lean_dec_ref(v___x_4997_);
lean_del_object(v___x_4989_);
goto v___jp_5054_;
}
else
{
lean_object* v_inheritedTraceOptions_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; uint8_t v___x_5066_; 
v_inheritedTraceOptions_5063_ = lean_ctor_get(v_a_4981_, 13);
v___x_5064_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5065_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5066_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5063_, v_options_5061_, v___x_5065_);
if (v___x_5066_ == 0)
{
lean_del_object(v___x_5013_);
lean_dec_ref(v___x_4997_);
lean_del_object(v___x_4989_);
goto v___jp_5054_;
}
else
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5070_; 
v___x_5067_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1, &l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1);
v___x_5068_ = l_Lean_MessageData_ofExpr(v___x_4997_);
if (v_isShared_5014_ == 0)
{
lean_ctor_set_tag(v___x_5013_, 7);
lean_ctor_set(v___x_5013_, 1, v___x_5068_);
lean_ctor_set(v___x_5013_, 0, v___x_5067_);
v___x_5070_ = v___x_5013_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v___x_5067_);
lean_ctor_set(v_reuseFailAlloc_5086_, 1, v___x_5068_);
v___x_5070_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
lean_object* v___x_5071_; lean_object* v___x_5073_; 
v___x_5071_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3);
if (v_isShared_4990_ == 0)
{
lean_ctor_set_tag(v___x_4989_, 7);
lean_ctor_set(v___x_4989_, 1, v___x_5071_);
lean_ctor_set(v___x_4989_, 0, v___x_5070_);
v___x_5073_ = v___x_4989_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5070_);
lean_ctor_set(v_reuseFailAlloc_5085_, 1, v___x_5071_);
v___x_5073_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
lean_inc(v_a_5050_);
v___x_5074_ = l_Lean_indentExpr(v_a_5050_);
v___x_5075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5075_, 0, v___x_5073_);
lean_ctor_set(v___x_5075_, 1, v___x_5074_);
v___x_5076_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5064_, v___x_5075_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_dec_ref_known(v___x_5076_, 1);
goto v___jp_5054_;
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
lean_del_object(v___x_5052_);
lean_dec(v_a_5050_);
lean_del_object(v___x_5008_);
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5076_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5076_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
}
}
}
v___jp_5054_:
{
lean_object* v___x_5056_; 
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 0, v_a_5050_);
v___x_5056_ = v___x_5008_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_a_5050_);
v___x_5056_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
lean_object* v___x_5058_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 0, v___x_5056_);
v___x_5058_ = v___x_5052_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v___x_5056_);
v___x_5058_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
return v___x_5058_;
}
}
}
}
}
else
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
lean_del_object(v___x_5013_);
lean_del_object(v___x_5008_);
lean_dec_ref(v___x_4997_);
lean_del_object(v___x_4989_);
v_a_5088_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5090_ = v___x_5049_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_5049_);
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
lean_del_object(v___x_5013_);
lean_dec(v_snd_5011_);
lean_dec(v_fst_5010_);
lean_del_object(v___x_5008_);
lean_dec_ref(v___x_4997_);
lean_del_object(v___x_4989_);
v_a_5096_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_5047_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5047_);
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
}
}
}
}
}
}
else
{
lean_object* v___x_5111_; 
lean_dec(v_a_5002_);
lean_dec_ref(v___x_4997_);
lean_del_object(v___x_4989_);
lean_dec_ref(v_info_4971_);
lean_dec_ref(v_fp_4970_);
if (v_isShared_5005_ == 0)
{
lean_ctor_set(v___x_5004_, 0, v___x_4996_);
v___x_5111_ = v___x_5004_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_4996_);
v___x_5111_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
return v___x_5111_;
}
}
}
}
else
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
lean_dec_ref(v___x_4997_);
lean_del_object(v___x_4989_);
lean_dec_ref(v_info_4971_);
lean_dec_ref(v_fp_4970_);
v_a_5114_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5001_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5001_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5114_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
}
else
{
lean_object* v___x_5122_; lean_object* v___x_5123_; 
lean_del_object(v___x_4989_);
lean_dec_ref(v_entries_4987_);
lean_dec_ref(v_tree_4986_);
lean_dec_ref(v_info_4971_);
lean_dec_ref(v_fp_4970_);
v___x_5122_ = lean_box(0);
v___x_5123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5123_, 0, v___x_5122_);
return v___x_5123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___boxed(lean_object* v_fp_5125_, lean_object* v_info_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(v_fp_5125_, v_info_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_);
lean_dec(v_a_5137_);
lean_dec_ref(v_a_5136_);
lean_dec(v_a_5135_);
lean_dec_ref(v_a_5134_);
lean_dec(v_a_5133_);
lean_dec_ref(v_a_5132_);
lean_dec(v_a_5131_);
lean_dec_ref(v_a_5130_);
lean_dec(v_a_5129_);
lean_dec(v_a_5128_);
lean_dec_ref(v_a_5127_);
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0(lean_object* v___x_5140_, lean_object* v___x_5141_, lean_object* v_as_5142_, size_t v_sz_5143_, size_t v_i_5144_, lean_object* v_b_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_){
_start:
{
lean_object* v___x_5158_; 
v___x_5158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v___x_5140_, v___x_5141_, v_as_5142_, v_sz_5143_, v_i_5144_, v_b_5145_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_);
return v___x_5158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___boxed(lean_object** _args){
lean_object* v___x_5159_ = _args[0];
lean_object* v___x_5160_ = _args[1];
lean_object* v_as_5161_ = _args[2];
lean_object* v_sz_5162_ = _args[3];
lean_object* v_i_5163_ = _args[4];
lean_object* v_b_5164_ = _args[5];
lean_object* v___y_5165_ = _args[6];
lean_object* v___y_5166_ = _args[7];
lean_object* v___y_5167_ = _args[8];
lean_object* v___y_5168_ = _args[9];
lean_object* v___y_5169_ = _args[10];
lean_object* v___y_5170_ = _args[11];
lean_object* v___y_5171_ = _args[12];
lean_object* v___y_5172_ = _args[13];
lean_object* v___y_5173_ = _args[14];
lean_object* v___y_5174_ = _args[15];
lean_object* v___y_5175_ = _args[16];
lean_object* v___y_5176_ = _args[17];
_start:
{
size_t v_sz_boxed_5177_; size_t v_i_boxed_5178_; lean_object* v_res_5179_; 
v_sz_boxed_5177_ = lean_unbox_usize(v_sz_5162_);
lean_dec(v_sz_5162_);
v_i_boxed_5178_ = lean_unbox_usize(v_i_5163_);
lean_dec(v_i_5163_);
v_res_5179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0(v___x_5159_, v___x_5160_, v_as_5161_, v_sz_boxed_5177_, v_i_boxed_5178_, v_b_5164_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
lean_dec(v___y_5175_);
lean_dec_ref(v___y_5174_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec(v___y_5166_);
lean_dec_ref(v___y_5165_);
lean_dec_ref(v_as_5161_);
lean_dec_ref(v___x_5159_);
return v_res_5179_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost(lean_object* v_post_5187_){
_start:
{
lean_object* v___y_5189_; uint8_t v___x_5194_; 
v___x_5194_ = l_Lean_Expr_isLambda(v_post_5187_);
if (v___x_5194_ == 0)
{
v___y_5189_ = v_post_5187_;
goto v___jp_5188_;
}
else
{
lean_object* v___x_5195_; 
v___x_5195_ = l_Lean_Expr_bindingBody_x21(v_post_5187_);
lean_dec_ref(v_post_5187_);
v___y_5189_ = v___x_5195_;
goto v___jp_5188_;
}
v___jp_5188_:
{
lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; uint8_t v___x_5193_; 
v___x_5190_ = l_Lean_Expr_consumeMData(v___y_5189_);
lean_dec_ref(v___y_5189_);
v___x_5191_ = l_Lean_Expr_getAppFn(v___x_5190_);
lean_dec_ref(v___x_5190_);
v___x_5192_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2));
v___x_5193_ = l_Lean_Expr_isConstOf(v___x_5191_, v___x_5192_);
lean_dec_ref(v___x_5191_);
return v___x_5193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___boxed(lean_object* v_post_5196_){
_start:
{
uint8_t v_res_5197_; lean_object* v_r_5198_; 
v_res_5197_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost(v_post_5196_);
v_r_5198_ = lean_box(v_res_5197_);
return v_r_5198_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1(void){
_start:
{
lean_object* v___x_5200_; lean_object* v___x_5201_; 
v___x_5200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__0));
v___x_5201_ = l_Lean_stringToMessageData(v___x_5200_);
return v___x_5201_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3(void){
_start:
{
lean_object* v___x_5203_; lean_object* v___x_5204_; 
v___x_5203_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__2));
v___x_5204_ = l_Lean_stringToMessageData(v___x_5203_);
return v___x_5204_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5(void){
_start:
{
lean_object* v___x_5206_; lean_object* v___x_5207_; 
v___x_5206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__4));
v___x_5207_ = l_Lean_stringToMessageData(v___x_5206_);
return v___x_5207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule(lean_object* v_goal_5208_, lean_object* v_info_5209_, lean_object* v_fp_5210_, lean_object* v_split_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_){
_start:
{
lean_object* v___x_5224_; 
lean_inc_ref(v_info_5209_);
v___x_5224_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_5210_, v_info_5209_, v_a_5213_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
if (lean_obj_tag(v___x_5224_) == 0)
{
lean_object* v_a_5225_; lean_object* v_rule_5226_; lean_object* v_splitVCIdx_5227_; lean_object* v_frameIdx_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; 
v_a_5225_ = lean_ctor_get(v___x_5224_, 0);
lean_inc(v_a_5225_);
lean_dec_ref_known(v___x_5224_, 1);
v_rule_5226_ = lean_ctor_get(v_a_5225_, 0);
lean_inc_ref(v_rule_5226_);
v_splitVCIdx_5227_ = lean_ctor_get(v_a_5225_, 1);
lean_inc(v_splitVCIdx_5227_);
v_frameIdx_5228_ = lean_ctor_get(v_a_5225_, 2);
lean_inc(v_frameIdx_5228_);
lean_dec(v_a_5225_);
v___x_5229_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1);
v___x_5230_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5209_);
v___x_5231_ = l_Lean_indentExpr(v___x_5230_);
lean_inc_ref(v___x_5231_);
v___x_5232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5229_);
lean_ctor_set(v___x_5232_, 1, v___x_5231_);
v___x_5233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5233_, 0, v___x_5232_);
v___x_5234_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_5226_, v_goal_5208_, v___x_5233_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
if (lean_obj_tag(v___x_5234_) == 0)
{
lean_object* v_a_5235_; 
v_a_5235_ = lean_ctor_get(v___x_5234_, 0);
lean_inc(v_a_5235_);
lean_dec_ref_known(v___x_5234_, 1);
if (lean_obj_tag(v_a_5235_) == 1)
{
lean_object* v_mvarIds_5236_; lean_object* v_frame_5237_; lean_object* v_residualPre_5238_; lean_object* v_splitVCProof_5239_; lean_object* v_subgoals_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; 
lean_dec_ref(v___x_5231_);
v_mvarIds_5236_ = lean_ctor_get(v_a_5235_, 0);
lean_inc(v_mvarIds_5236_);
lean_dec_ref_known(v_a_5235_, 1);
v_frame_5237_ = lean_ctor_get(v_split_5211_, 0);
lean_inc_ref(v_frame_5237_);
v_residualPre_5238_ = lean_ctor_get(v_split_5211_, 1);
lean_inc(v_residualPre_5238_);
v_splitVCProof_5239_ = lean_ctor_get(v_split_5211_, 2);
lean_inc_ref(v_splitVCProof_5239_);
v_subgoals_5240_ = lean_ctor_get(v_split_5211_, 3);
lean_inc(v_subgoals_5240_);
lean_dec_ref(v_split_5211_);
v___x_5241_ = lean_box(0);
v___x_5242_ = lean_array_mk(v_mvarIds_5236_);
v___x_5243_ = lean_array_get(v___x_5241_, v___x_5242_, v_frameIdx_5228_);
lean_dec(v_frameIdx_5228_);
v___x_5244_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v___x_5243_, v_frame_5237_, v_a_5220_);
lean_dec_ref(v___x_5244_);
v___x_5245_ = lean_array_get(v___x_5241_, v___x_5242_, v_splitVCIdx_5227_);
lean_dec(v_splitVCIdx_5227_);
lean_inc(v___x_5245_);
v___x_5246_ = l_Lean_MVarId_getType(v___x_5245_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_object* v_a_5247_; lean_object* v___y_5249_; lean_object* v___y_5250_; lean_object* v___y_5251_; lean_object* v___y_5252_; lean_object* v___x_5257_; uint8_t v___x_5258_; 
v_a_5247_ = lean_ctor_get(v___x_5246_, 0);
lean_inc_n(v_a_5247_, 2);
lean_dec_ref_known(v___x_5246_, 1);
v___x_5257_ = l_Lean_Expr_cleanupAnnotations(v_a_5247_);
v___x_5258_ = l_Lean_Expr_isApp(v___x_5257_);
if (v___x_5258_ == 0)
{
lean_dec_ref(v___x_5257_);
lean_dec(v___x_5245_);
lean_dec_ref(v___x_5242_);
lean_dec(v_subgoals_5240_);
lean_dec_ref(v_splitVCProof_5239_);
lean_dec(v_residualPre_5238_);
lean_dec_ref(v_info_5209_);
v___y_5249_ = v_a_5219_;
v___y_5250_ = v_a_5220_;
v___y_5251_ = v_a_5221_;
v___y_5252_ = v_a_5222_;
goto v___jp_5248_;
}
else
{
lean_object* v_arg_5259_; lean_object* v___x_5260_; uint8_t v___x_5261_; 
v_arg_5259_ = lean_ctor_get(v___x_5257_, 1);
lean_inc_ref(v_arg_5259_);
v___x_5260_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5257_);
v___x_5261_ = l_Lean_Expr_isApp(v___x_5260_);
if (v___x_5261_ == 0)
{
lean_dec_ref(v___x_5260_);
lean_dec_ref(v_arg_5259_);
lean_dec(v___x_5245_);
lean_dec_ref(v___x_5242_);
lean_dec(v_subgoals_5240_);
lean_dec_ref(v_splitVCProof_5239_);
lean_dec(v_residualPre_5238_);
lean_dec_ref(v_info_5209_);
v___y_5249_ = v_a_5219_;
v___y_5250_ = v_a_5220_;
v___y_5251_ = v_a_5221_;
v___y_5252_ = v_a_5222_;
goto v___jp_5248_;
}
else
{
lean_object* v___x_5262_; uint8_t v___x_5263_; 
v___x_5262_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5260_);
v___x_5263_ = l_Lean_Expr_isApp(v___x_5262_);
if (v___x_5263_ == 0)
{
lean_dec_ref(v___x_5262_);
lean_dec_ref(v_arg_5259_);
lean_dec(v___x_5245_);
lean_dec_ref(v___x_5242_);
lean_dec(v_subgoals_5240_);
lean_dec_ref(v_splitVCProof_5239_);
lean_dec(v_residualPre_5238_);
lean_dec_ref(v_info_5209_);
v___y_5249_ = v_a_5219_;
v___y_5250_ = v_a_5220_;
v___y_5251_ = v_a_5221_;
v___y_5252_ = v_a_5222_;
goto v___jp_5248_;
}
else
{
lean_object* v___x_5264_; uint8_t v___x_5265_; 
v___x_5264_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5262_);
v___x_5265_ = l_Lean_Expr_isApp(v___x_5264_);
if (v___x_5265_ == 0)
{
lean_dec_ref(v___x_5264_);
lean_dec_ref(v_arg_5259_);
lean_dec(v___x_5245_);
lean_dec_ref(v___x_5242_);
lean_dec(v_subgoals_5240_);
lean_dec_ref(v_splitVCProof_5239_);
lean_dec(v_residualPre_5238_);
lean_dec_ref(v_info_5209_);
v___y_5249_ = v_a_5219_;
v___y_5250_ = v_a_5220_;
v___y_5251_ = v_a_5221_;
v___y_5252_ = v_a_5222_;
goto v___jp_5248_;
}
else
{
lean_object* v___x_5266_; lean_object* v___x_5267_; uint8_t v___x_5268_; 
v___x_5266_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5264_);
v___x_5267_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10));
v___x_5268_ = l_Lean_Expr_isConstOf(v___x_5266_, v___x_5267_);
lean_dec_ref(v___x_5266_);
if (v___x_5268_ == 0)
{
lean_dec_ref(v_arg_5259_);
lean_dec(v___x_5245_);
lean_dec_ref(v___x_5242_);
lean_dec(v_subgoals_5240_);
lean_dec_ref(v_splitVCProof_5239_);
lean_dec(v_residualPre_5238_);
lean_dec_ref(v_info_5209_);
v___y_5249_ = v_a_5219_;
v___y_5250_ = v_a_5220_;
v___y_5251_ = v_a_5221_;
v___y_5252_ = v_a_5222_;
goto v___jp_5248_;
}
else
{
lean_object* v_excessArgs_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5283_; 
lean_dec(v_a_5247_);
v_excessArgs_5269_ = lean_ctor_get(v_info_5209_, 2);
lean_inc_ref(v_excessArgs_5269_);
lean_dec_ref(v_info_5209_);
v___x_5270_ = lean_array_get_size(v_excessArgs_5269_);
lean_dec_ref(v_excessArgs_5269_);
v___x_5271_ = l_Lean_Expr_stripArgsN(v_arg_5259_, v___x_5270_);
lean_dec_ref(v_arg_5259_);
v___x_5272_ = l_Lean_Expr_appArg_x21(v___x_5271_);
lean_dec_ref(v___x_5271_);
v___x_5273_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_residualPre_5238_, v___x_5272_, v_a_5220_);
lean_dec_ref(v___x_5273_);
v___x_5274_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v___x_5245_, v_splitVCProof_5239_, v_a_5220_);
v_isSharedCheck_5283_ = !lean_is_exclusive(v___x_5274_);
if (v_isSharedCheck_5283_ == 0)
{
lean_object* v_unused_5284_; 
v_unused_5284_ = lean_ctor_get(v___x_5274_, 0);
lean_dec(v_unused_5284_);
v___x_5276_ = v___x_5274_;
v_isShared_5277_ = v_isSharedCheck_5283_;
goto v_resetjp_5275_;
}
else
{
lean_dec(v___x_5274_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5283_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5281_; 
v___x_5278_ = lean_array_to_list(v___x_5242_);
v___x_5279_ = l_List_appendTR___redArg(v___x_5278_, v_subgoals_5240_);
if (v_isShared_5277_ == 0)
{
lean_ctor_set(v___x_5276_, 0, v___x_5279_);
v___x_5281_ = v___x_5276_;
goto v_reusejp_5280_;
}
else
{
lean_object* v_reuseFailAlloc_5282_; 
v_reuseFailAlloc_5282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5282_, 0, v___x_5279_);
v___x_5281_ = v_reuseFailAlloc_5282_;
goto v_reusejp_5280_;
}
v_reusejp_5280_:
{
return v___x_5281_;
}
}
}
}
}
}
}
v___jp_5248_:
{
lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; 
v___x_5253_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3);
v___x_5254_ = l_Lean_indentExpr(v_a_5247_);
v___x_5255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5255_, 0, v___x_5253_);
lean_ctor_set(v___x_5255_, 1, v___x_5254_);
v___x_5256_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5255_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_);
return v___x_5256_;
}
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5292_; 
lean_dec(v___x_5245_);
lean_dec_ref(v___x_5242_);
lean_dec(v_subgoals_5240_);
lean_dec_ref(v_splitVCProof_5239_);
lean_dec(v_residualPre_5238_);
lean_dec_ref(v_info_5209_);
v_a_5285_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5287_ = v___x_5246_;
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5246_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5290_; 
if (v_isShared_5288_ == 0)
{
v___x_5290_ = v___x_5287_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
}
else
{
lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; 
lean_dec(v_a_5235_);
lean_dec(v_frameIdx_5228_);
lean_dec(v_splitVCIdx_5227_);
lean_dec_ref(v_split_5211_);
lean_dec_ref(v_info_5209_);
v___x_5293_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5);
v___x_5294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5293_);
lean_ctor_set(v___x_5294_, 1, v___x_5231_);
v___x_5295_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5294_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
return v___x_5295_;
}
}
else
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5303_; 
lean_dec_ref(v___x_5231_);
lean_dec(v_frameIdx_5228_);
lean_dec(v_splitVCIdx_5227_);
lean_dec_ref(v_split_5211_);
lean_dec_ref(v_info_5209_);
v_a_5296_ = lean_ctor_get(v___x_5234_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5234_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5298_ = v___x_5234_;
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v___x_5234_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___x_5301_; 
if (v_isShared_5299_ == 0)
{
v___x_5301_ = v___x_5298_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5296_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
}
else
{
lean_object* v_a_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5311_; 
lean_dec_ref(v_split_5211_);
lean_dec_ref(v_info_5209_);
lean_dec(v_goal_5208_);
v_a_5304_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5311_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5306_ = v___x_5224_;
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_a_5304_);
lean_dec(v___x_5224_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
lean_object* v___x_5309_; 
if (v_isShared_5307_ == 0)
{
v___x_5309_ = v___x_5306_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_a_5304_);
v___x_5309_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
return v___x_5309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___boxed(lean_object* v_goal_5312_, lean_object* v_info_5313_, lean_object* v_fp_5314_, lean_object* v_split_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_){
_start:
{
lean_object* v_res_5328_; 
v_res_5328_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule(v_goal_5312_, v_info_5313_, v_fp_5314_, v_split_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec_ref(v_a_5323_);
lean_dec(v_a_5322_);
lean_dec_ref(v_a_5321_);
lean_dec(v_a_5320_);
lean_dec_ref(v_a_5319_);
lean_dec(v_a_5318_);
lean_dec(v_a_5317_);
lean_dec_ref(v_a_5316_);
return v_res_5328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0(lean_object* v_mkOpAppM_5329_, lean_object* v_info_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_){
_start:
{
lean_object* v___x_5338_; 
lean_inc(v___y_5336_);
lean_inc_ref(v___y_5335_);
lean_inc(v___y_5334_);
lean_inc_ref(v___y_5333_);
v___x_5338_ = lean_apply_6(v_mkOpAppM_5329_, v_info_5330_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, lean_box(0));
if (lean_obj_tag(v___x_5338_) == 0)
{
lean_object* v_a_5339_; lean_object* v___x_5340_; 
v_a_5339_ = lean_ctor_get(v___x_5338_, 0);
lean_inc(v_a_5339_);
lean_dec_ref_known(v___x_5338_, 1);
v___x_5340_ = l_Lean_Meta_Sym_shareCommon(v_a_5339_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_);
return v___x_5340_;
}
else
{
return v___x_5338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0___boxed(lean_object* v_mkOpAppM_5341_, lean_object* v_info_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0(v_mkOpAppM_5341_, v_info_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(lean_object* v_a_5351_, lean_object* v_a_5352_){
_start:
{
if (lean_obj_tag(v_a_5351_) == 0)
{
lean_object* v___x_5353_; 
v___x_5353_ = l_List_reverse___redArg(v_a_5352_);
return v___x_5353_;
}
else
{
lean_object* v_head_5354_; lean_object* v_tail_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5364_; 
v_head_5354_ = lean_ctor_get(v_a_5351_, 0);
v_tail_5355_ = lean_ctor_get(v_a_5351_, 1);
v_isSharedCheck_5364_ = !lean_is_exclusive(v_a_5351_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5357_ = v_a_5351_;
v_isShared_5358_ = v_isSharedCheck_5364_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_tail_5355_);
lean_inc(v_head_5354_);
lean_dec(v_a_5351_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5364_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5359_; lean_object* v___x_5361_; 
v___x_5359_ = l_Lean_MessageData_ofExpr(v_head_5354_);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 1, v_a_5352_);
lean_ctor_set(v___x_5357_, 0, v___x_5359_);
v___x_5361_ = v___x_5357_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5359_);
lean_ctor_set(v_reuseFailAlloc_5363_, 1, v_a_5352_);
v___x_5361_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
v_a_5351_ = v_tail_5355_;
v_a_5352_ = v___x_5361_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(lean_object* v_a_5365_, lean_object* v_x_5366_){
_start:
{
if (lean_obj_tag(v_x_5366_) == 0)
{
lean_object* v___x_5367_; 
v___x_5367_ = lean_box(0);
return v___x_5367_;
}
else
{
lean_object* v_key_5368_; lean_object* v_value_5369_; lean_object* v_tail_5370_; uint8_t v___x_5371_; 
v_key_5368_ = lean_ctor_get(v_x_5366_, 0);
v_value_5369_ = lean_ctor_get(v_x_5366_, 1);
v_tail_5370_ = lean_ctor_get(v_x_5366_, 2);
v___x_5371_ = lean_name_eq(v_key_5368_, v_a_5365_);
if (v___x_5371_ == 0)
{
v_x_5366_ = v_tail_5370_;
goto _start;
}
else
{
lean_object* v___x_5373_; 
lean_inc(v_value_5369_);
v___x_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5373_, 0, v_value_5369_);
return v___x_5373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg___boxed(lean_object* v_a_5374_, lean_object* v_x_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(v_a_5374_, v_x_5375_);
lean_dec(v_x_5375_);
lean_dec(v_a_5374_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(lean_object* v_m_5377_, lean_object* v_a_5378_){
_start:
{
lean_object* v_buckets_5379_; lean_object* v___x_5380_; uint64_t v___y_5382_; 
v_buckets_5379_ = lean_ctor_get(v_m_5377_, 1);
v___x_5380_ = lean_array_get_size(v_buckets_5379_);
if (lean_obj_tag(v_a_5378_) == 0)
{
uint64_t v___x_5396_; 
v___x_5396_ = 1723ULL;
v___y_5382_ = v___x_5396_;
goto v___jp_5381_;
}
else
{
uint64_t v_hash_5397_; 
v_hash_5397_ = lean_ctor_get_uint64(v_a_5378_, sizeof(void*)*2);
v___y_5382_ = v_hash_5397_;
goto v___jp_5381_;
}
v___jp_5381_:
{
uint64_t v___x_5383_; uint64_t v___x_5384_; uint64_t v_fold_5385_; uint64_t v___x_5386_; uint64_t v___x_5387_; uint64_t v___x_5388_; size_t v___x_5389_; size_t v___x_5390_; size_t v___x_5391_; size_t v___x_5392_; size_t v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___x_5383_ = 32ULL;
v___x_5384_ = lean_uint64_shift_right(v___y_5382_, v___x_5383_);
v_fold_5385_ = lean_uint64_xor(v___y_5382_, v___x_5384_);
v___x_5386_ = 16ULL;
v___x_5387_ = lean_uint64_shift_right(v_fold_5385_, v___x_5386_);
v___x_5388_ = lean_uint64_xor(v_fold_5385_, v___x_5387_);
v___x_5389_ = lean_uint64_to_usize(v___x_5388_);
v___x_5390_ = lean_usize_of_nat(v___x_5380_);
v___x_5391_ = ((size_t)1ULL);
v___x_5392_ = lean_usize_sub(v___x_5390_, v___x_5391_);
v___x_5393_ = lean_usize_land(v___x_5389_, v___x_5392_);
v___x_5394_ = lean_array_uget_borrowed(v_buckets_5379_, v___x_5393_);
v___x_5395_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(v_a_5378_, v___x_5394_);
return v___x_5395_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg___boxed(lean_object* v_m_5398_, lean_object* v_a_5399_){
_start:
{
lean_object* v_res_5400_; 
v_res_5400_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(v_m_5398_, v_a_5399_);
lean_dec(v_a_5399_);
lean_dec_ref(v_m_5398_);
return v_res_5400_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1(void){
_start:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; 
v___x_5402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__0));
v___x_5403_ = l_Lean_stringToMessageData(v___x_5402_);
return v___x_5403_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3(void){
_start:
{
lean_object* v___x_5405_; lean_object* v___x_5406_; 
v___x_5405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__2));
v___x_5406_ = l_Lean_stringToMessageData(v___x_5405_);
return v___x_5406_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5(void){
_start:
{
lean_object* v___x_5408_; lean_object* v___x_5409_; 
v___x_5408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__4));
v___x_5409_ = l_Lean_stringToMessageData(v___x_5408_);
return v___x_5409_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7(void){
_start:
{
lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__6));
v___x_5412_ = l_Lean_stringToMessageData(v___x_5411_);
return v___x_5412_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9(void){
_start:
{
lean_object* v___x_5414_; lean_object* v___x_5415_; 
v___x_5414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__8));
v___x_5415_ = l_Lean_stringToMessageData(v___x_5414_);
return v___x_5415_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11(void){
_start:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; 
v___x_5417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__10));
v___x_5418_ = l_Lean_stringToMessageData(v___x_5417_);
return v___x_5418_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13(void){
_start:
{
lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5420_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__12));
v___x_5421_ = l_Lean_stringToMessageData(v___x_5420_);
return v___x_5421_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15(void){
_start:
{
lean_object* v___x_5423_; lean_object* v___x_5424_; 
v___x_5423_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__14));
v___x_5424_ = l_Lean_stringToMessageData(v___x_5423_);
return v___x_5424_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17(void){
_start:
{
lean_object* v___x_5426_; lean_object* v___x_5427_; 
v___x_5426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__16));
v___x_5427_ = l_Lean_stringToMessageData(v___x_5426_);
return v___x_5427_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19(void){
_start:
{
lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5429_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__18));
v___x_5430_ = l_Lean_stringToMessageData(v___x_5429_);
return v___x_5430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(lean_object* v_scope_5431_, lean_object* v_goal_5432_, lean_object* v_info_5433_, lean_object* v_thm_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_){
_start:
{
lean_object* v___y_5448_; lean_object* v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v___y_5455_; lean_object* v___y_5456_; lean_object* v___y_5457_; lean_object* v___y_5458_; lean_object* v___y_5459_; lean_object* v___y_5496_; lean_object* v___y_5497_; lean_object* v___y_5498_; lean_object* v___y_5499_; lean_object* v___y_5500_; lean_object* v___y_5501_; lean_object* v___y_5502_; lean_object* v___y_5503_; lean_object* v___y_5504_; lean_object* v___y_5505_; lean_object* v___y_5506_; lean_object* v___y_5507_; lean_object* v___y_5508_; lean_object* v___y_5509_; lean_object* v___y_5510_; lean_object* v___y_5535_; lean_object* v___y_5536_; lean_object* v___y_5537_; lean_object* v___y_5538_; lean_object* v___y_5539_; lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v___y_5542_; lean_object* v___y_5543_; lean_object* v___y_5544_; lean_object* v___y_5545_; lean_object* v___y_5546_; lean_object* v___y_5574_; lean_object* v___y_5575_; lean_object* v___y_5576_; lean_object* v___y_5577_; lean_object* v___y_5578_; lean_object* v___y_5579_; lean_object* v___y_5580_; lean_object* v___y_5581_; lean_object* v___y_5582_; lean_object* v___y_5583_; lean_object* v___y_5584_; lean_object* v___y_5585_; lean_object* v___y_5586_; lean_object* v___y_5617_; lean_object* v___y_5618_; lean_object* v___y_5671_; lean_object* v___y_5674_; lean_object* v___x_5704_; 
lean_inc_ref(v_info_5433_);
lean_inc_ref(v_thm_5434_);
v___x_5704_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(v_thm_5434_, v_info_5433_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_);
if (lean_obj_tag(v___x_5704_) == 0)
{
v___y_5674_ = v___x_5704_;
goto v___jp_5673_;
}
else
{
lean_object* v_a_5705_; lean_object* v___y_5707_; lean_object* v___y_5708_; lean_object* v___y_5709_; uint8_t v___y_5739_; uint8_t v___x_5770_; 
v_a_5705_ = lean_ctor_get(v___x_5704_, 0);
lean_inc(v_a_5705_);
v___x_5770_ = l_Lean_Exception_isInterrupt(v_a_5705_);
if (v___x_5770_ == 0)
{
uint8_t v___x_5771_; 
lean_inc(v_a_5705_);
v___x_5771_ = l_Lean_Exception_isRuntime(v_a_5705_);
v___y_5739_ = v___x_5771_;
goto v___jp_5738_;
}
else
{
v___y_5739_ = v___x_5770_;
goto v___jp_5738_;
}
v___jp_5706_:
{
lean_object* v_excessArgs_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; 
v_excessArgs_5710_ = lean_ctor_get(v_info_5433_, 2);
lean_inc_ref(v___y_5707_);
v___x_5711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5711_, 0, v___y_5707_);
lean_ctor_set(v___x_5711_, 1, v___y_5709_);
v___x_5712_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_5713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5711_);
lean_ctor_set(v___x_5713_, 1, v___x_5712_);
v___x_5714_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5433_);
v___x_5715_ = l_Lean_indentExpr(v___x_5714_);
v___x_5716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5716_, 0, v___x_5713_);
lean_ctor_set(v___x_5716_, 1, v___x_5715_);
v___x_5717_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11);
v___x_5718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5716_);
lean_ctor_set(v___x_5718_, 1, v___x_5717_);
v___x_5719_ = l_Lean_Exception_toMessageData(v_a_5705_);
v___x_5720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5718_);
lean_ctor_set(v___x_5720_, 1, v___x_5719_);
v___x_5721_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13);
v___x_5722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5720_);
lean_ctor_set(v___x_5722_, 1, v___x_5721_);
v___x_5723_ = l_Lean_indentExpr(v___y_5708_);
v___x_5724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5722_);
lean_ctor_set(v___x_5724_, 1, v___x_5723_);
v___x_5725_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15);
v___x_5726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5724_);
lean_ctor_set(v___x_5726_, 1, v___x_5725_);
v___x_5727_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_5433_);
v___x_5728_ = l_Lean_indentExpr(v___x_5727_);
v___x_5729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5726_);
lean_ctor_set(v___x_5729_, 1, v___x_5728_);
v___x_5730_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17);
v___x_5731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5729_);
lean_ctor_set(v___x_5731_, 1, v___x_5730_);
lean_inc_ref(v_excessArgs_5710_);
v___x_5732_ = lean_array_to_list(v_excessArgs_5710_);
v___x_5733_ = lean_box(0);
v___x_5734_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(v___x_5732_, v___x_5733_);
v___x_5735_ = l_Lean_MessageData_ofList(v___x_5734_);
v___x_5736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5731_);
lean_ctor_set(v___x_5736_, 1, v___x_5735_);
v___x_5737_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5736_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_);
v___y_5674_ = v___x_5737_;
goto v___jp_5673_;
}
v___jp_5738_:
{
if (v___y_5739_ == 0)
{
lean_object* v___x_5740_; 
lean_dec_ref_known(v___x_5704_, 1);
lean_inc(v_goal_5432_);
v___x_5740_ = l_Lean_MVarId_getType(v_goal_5432_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_);
if (lean_obj_tag(v___x_5740_) == 0)
{
lean_object* v_a_5741_; lean_object* v_proof_5742_; lean_object* v___x_5743_; 
v_a_5741_ = lean_ctor_get(v___x_5740_, 0);
lean_inc(v_a_5741_);
lean_dec_ref_known(v___x_5740_, 1);
v_proof_5742_ = lean_ctor_get(v_thm_5434_, 1);
v___x_5743_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19);
switch(lean_obj_tag(v_proof_5742_))
{
case 0:
{
lean_object* v_declName_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; 
v_declName_5744_ = lean_ctor_get(v_proof_5742_, 0);
v___x_5745_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_5744_);
v___x_5746_ = l_Lean_MessageData_ofName(v_declName_5744_);
v___x_5747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5745_);
lean_ctor_set(v___x_5747_, 1, v___x_5746_);
v___y_5707_ = v___x_5743_;
v___y_5708_ = v_a_5741_;
v___y_5709_ = v___x_5747_;
goto v___jp_5706_;
}
case 1:
{
lean_object* v_fvarId_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; 
v_fvarId_5748_ = lean_ctor_get(v_proof_5742_, 0);
v___x_5749_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_5748_);
v___x_5750_ = l_Lean_mkFVar(v_fvarId_5748_);
v___x_5751_ = l_Lean_MessageData_ofExpr(v___x_5750_);
v___x_5752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5749_);
lean_ctor_set(v___x_5752_, 1, v___x_5751_);
v___y_5707_ = v___x_5743_;
v___y_5708_ = v_a_5741_;
v___y_5709_ = v___x_5752_;
goto v___jp_5706_;
}
default: 
{
lean_object* v_ref_5753_; lean_object* v_proof_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; 
v_ref_5753_ = lean_ctor_get(v_proof_5742_, 1);
v_proof_5754_ = lean_ctor_get(v_proof_5742_, 2);
v___x_5755_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_5753_);
v___x_5756_ = l_Lean_MessageData_ofSyntax(v_ref_5753_);
v___x_5757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5755_);
lean_ctor_set(v___x_5757_, 1, v___x_5756_);
v___x_5758_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_5759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5759_, 0, v___x_5757_);
lean_ctor_set(v___x_5759_, 1, v___x_5758_);
lean_inc_ref(v_proof_5754_);
v___x_5760_ = l_Lean_MessageData_ofExpr(v_proof_5754_);
v___x_5761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5761_, 0, v___x_5759_);
lean_ctor_set(v___x_5761_, 1, v___x_5760_);
v___y_5707_ = v___x_5743_;
v___y_5708_ = v_a_5741_;
v___y_5709_ = v___x_5761_;
goto v___jp_5706_;
}
}
}
else
{
lean_object* v_a_5762_; lean_object* v___x_5764_; uint8_t v_isShared_5765_; uint8_t v_isSharedCheck_5769_; 
lean_dec(v_a_5705_);
lean_dec_ref(v_thm_5434_);
lean_dec_ref(v_info_5433_);
lean_dec(v_goal_5432_);
lean_dec_ref(v_scope_5431_);
v_a_5762_ = lean_ctor_get(v___x_5740_, 0);
v_isSharedCheck_5769_ = !lean_is_exclusive(v___x_5740_);
if (v_isSharedCheck_5769_ == 0)
{
v___x_5764_ = v___x_5740_;
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
else
{
lean_inc(v_a_5762_);
lean_dec(v___x_5740_);
v___x_5764_ = lean_box(0);
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
v_resetjp_5763_:
{
lean_object* v___x_5767_; 
if (v_isShared_5765_ == 0)
{
v___x_5767_ = v___x_5764_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_a_5762_);
v___x_5767_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
return v___x_5767_;
}
}
}
}
else
{
lean_dec(v_a_5705_);
v___y_5674_ = v___x_5704_;
goto v___jp_5673_;
}
}
}
v___jp_5447_:
{
lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; 
v___x_5460_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1);
v___x_5461_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5433_);
lean_dec_ref(v_info_5433_);
v___x_5462_ = l_Lean_indentExpr(v___x_5461_);
v___x_5463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5463_, 0, v___x_5460_);
lean_ctor_set(v___x_5463_, 1, v___x_5462_);
v___x_5464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5464_, 0, v___x_5463_);
v___x_5465_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v___y_5448_, v_goal_5432_, v___x_5464_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_);
if (lean_obj_tag(v___x_5465_) == 0)
{
lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5486_; 
v_a_5466_ = lean_ctor_get(v___x_5465_, 0);
v_isSharedCheck_5486_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5486_ == 0)
{
v___x_5468_ = v___x_5465_;
v_isShared_5469_ = v_isSharedCheck_5486_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___x_5465_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5486_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
if (lean_obj_tag(v_a_5466_) == 1)
{
lean_object* v_mvarIds_5470_; lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5481_; 
v_mvarIds_5470_ = lean_ctor_get(v_a_5466_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v_a_5466_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5472_ = v_a_5466_;
v_isShared_5473_ = v_isSharedCheck_5481_;
goto v_resetjp_5471_;
}
else
{
lean_inc(v_mvarIds_5470_);
lean_dec(v_a_5466_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5481_;
goto v_resetjp_5471_;
}
v_resetjp_5471_:
{
lean_object* v___x_5474_; lean_object* v___x_5476_; 
v___x_5474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5474_, 0, v_scope_5431_);
lean_ctor_set(v___x_5474_, 1, v_mvarIds_5470_);
if (v_isShared_5473_ == 0)
{
lean_ctor_set(v___x_5472_, 0, v___x_5474_);
v___x_5476_ = v___x_5472_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v___x_5474_);
v___x_5476_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
lean_object* v___x_5478_; 
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 0, v___x_5476_);
v___x_5478_ = v___x_5468_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v___x_5476_);
v___x_5478_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
return v___x_5478_;
}
}
}
}
else
{
lean_object* v___x_5482_; lean_object* v___x_5484_; 
lean_dec(v_a_5466_);
lean_dec_ref(v_scope_5431_);
v___x_5482_ = lean_box(0);
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 0, v___x_5482_);
v___x_5484_ = v___x_5468_;
goto v_reusejp_5483_;
}
else
{
lean_object* v_reuseFailAlloc_5485_; 
v_reuseFailAlloc_5485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5485_, 0, v___x_5482_);
v___x_5484_ = v_reuseFailAlloc_5485_;
goto v_reusejp_5483_;
}
v_reusejp_5483_:
{
return v___x_5484_;
}
}
}
}
else
{
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5494_; 
lean_dec_ref(v_scope_5431_);
v_a_5487_ = lean_ctor_get(v___x_5465_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5465_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5465_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5492_; 
if (v_isShared_5490_ == 0)
{
v___x_5492_ = v___x_5489_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
v___jp_5495_:
{
lean_object* v_excessArgs_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; 
v_excessArgs_5511_ = lean_ctor_get(v_info_5433_, 2);
lean_inc_ref(v___y_5497_);
v___x_5512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5512_, 0, v___y_5497_);
lean_ctor_set(v___x_5512_, 1, v___y_5510_);
v___x_5513_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_5514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5514_, 0, v___x_5512_);
lean_ctor_set(v___x_5514_, 1, v___x_5513_);
v___x_5515_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5433_);
v___x_5516_ = l_Lean_MessageData_ofExpr(v___x_5515_);
v___x_5517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5517_, 0, v___x_5514_);
lean_ctor_set(v___x_5517_, 1, v___x_5516_);
v___x_5518_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5);
v___x_5519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5519_, 0, v___x_5517_);
lean_ctor_set(v___x_5519_, 1, v___x_5518_);
lean_inc_ref(v_excessArgs_5511_);
v___x_5520_ = lean_array_to_list(v_excessArgs_5511_);
v___x_5521_ = lean_box(0);
v___x_5522_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(v___x_5520_, v___x_5521_);
v___x_5523_ = l_Lean_MessageData_ofList(v___x_5522_);
v___x_5524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5519_);
lean_ctor_set(v___x_5524_, 1, v___x_5523_);
lean_inc(v___y_5498_);
v___x_5525_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___y_5498_, v___x_5524_, v___y_5499_, v___y_5500_, v___y_5507_, v___y_5505_);
if (lean_obj_tag(v___x_5525_) == 0)
{
lean_dec_ref_known(v___x_5525_, 1);
v___y_5448_ = v___y_5504_;
v___y_5449_ = v___y_5501_;
v___y_5450_ = v___y_5502_;
v___y_5451_ = v___y_5509_;
v___y_5452_ = v___y_5508_;
v___y_5453_ = v___y_5503_;
v___y_5454_ = v___y_5506_;
v___y_5455_ = v___y_5496_;
v___y_5456_ = v___y_5499_;
v___y_5457_ = v___y_5500_;
v___y_5458_ = v___y_5507_;
v___y_5459_ = v___y_5505_;
goto v___jp_5447_;
}
else
{
lean_object* v_a_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5533_; 
lean_dec_ref(v___y_5504_);
lean_dec_ref(v_info_5433_);
lean_dec(v_goal_5432_);
lean_dec_ref(v_scope_5431_);
v_a_5526_ = lean_ctor_get(v___x_5525_, 0);
v_isSharedCheck_5533_ = !lean_is_exclusive(v___x_5525_);
if (v_isSharedCheck_5533_ == 0)
{
v___x_5528_ = v___x_5525_;
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_a_5526_);
lean_dec(v___x_5525_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5531_; 
if (v_isShared_5529_ == 0)
{
v___x_5531_ = v___x_5528_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_a_5526_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
v___jp_5534_:
{
lean_object* v_options_5547_; uint8_t v_hasTrace_5548_; 
v_options_5547_ = lean_ctor_get(v___y_5545_, 2);
v_hasTrace_5548_ = lean_ctor_get_uint8(v_options_5547_, sizeof(void*)*1);
if (v_hasTrace_5548_ == 0)
{
lean_dec_ref(v_thm_5434_);
v___y_5448_ = v___y_5535_;
v___y_5449_ = v___y_5536_;
v___y_5450_ = v___y_5537_;
v___y_5451_ = v___y_5538_;
v___y_5452_ = v___y_5539_;
v___y_5453_ = v___y_5540_;
v___y_5454_ = v___y_5541_;
v___y_5455_ = v___y_5542_;
v___y_5456_ = v___y_5543_;
v___y_5457_ = v___y_5544_;
v___y_5458_ = v___y_5545_;
v___y_5459_ = v___y_5546_;
goto v___jp_5447_;
}
else
{
lean_object* v_inheritedTraceOptions_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; uint8_t v___x_5552_; 
v_inheritedTraceOptions_5549_ = lean_ctor_get(v___y_5545_, 13);
v___x_5550_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5551_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5552_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5549_, v_options_5547_, v___x_5551_);
if (v___x_5552_ == 0)
{
lean_dec_ref(v_thm_5434_);
v___y_5448_ = v___y_5535_;
v___y_5449_ = v___y_5536_;
v___y_5450_ = v___y_5537_;
v___y_5451_ = v___y_5538_;
v___y_5452_ = v___y_5539_;
v___y_5453_ = v___y_5540_;
v___y_5454_ = v___y_5541_;
v___y_5455_ = v___y_5542_;
v___y_5456_ = v___y_5543_;
v___y_5457_ = v___y_5544_;
v___y_5458_ = v___y_5545_;
v___y_5459_ = v___y_5546_;
goto v___jp_5447_;
}
else
{
lean_object* v_proof_5553_; lean_object* v___x_5554_; 
v_proof_5553_ = lean_ctor_get(v_thm_5434_, 1);
lean_inc_ref(v_proof_5553_);
lean_dec_ref(v_thm_5434_);
v___x_5554_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7);
switch(lean_obj_tag(v_proof_5553_))
{
case 0:
{
lean_object* v_declName_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; 
v_declName_5555_ = lean_ctor_get(v_proof_5553_, 0);
lean_inc(v_declName_5555_);
lean_dec_ref_known(v_proof_5553_, 1);
v___x_5556_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_5557_ = l_Lean_MessageData_ofName(v_declName_5555_);
v___x_5558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5558_, 0, v___x_5556_);
lean_ctor_set(v___x_5558_, 1, v___x_5557_);
v___y_5496_ = v___y_5542_;
v___y_5497_ = v___x_5554_;
v___y_5498_ = v___x_5550_;
v___y_5499_ = v___y_5543_;
v___y_5500_ = v___y_5544_;
v___y_5501_ = v___y_5536_;
v___y_5502_ = v___y_5537_;
v___y_5503_ = v___y_5540_;
v___y_5504_ = v___y_5535_;
v___y_5505_ = v___y_5546_;
v___y_5506_ = v___y_5541_;
v___y_5507_ = v___y_5545_;
v___y_5508_ = v___y_5539_;
v___y_5509_ = v___y_5538_;
v___y_5510_ = v___x_5558_;
goto v___jp_5495_;
}
case 1:
{
lean_object* v_fvarId_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; 
v_fvarId_5559_ = lean_ctor_get(v_proof_5553_, 0);
lean_inc(v_fvarId_5559_);
lean_dec_ref_known(v_proof_5553_, 1);
v___x_5560_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_5561_ = l_Lean_mkFVar(v_fvarId_5559_);
v___x_5562_ = l_Lean_MessageData_ofExpr(v___x_5561_);
v___x_5563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5563_, 0, v___x_5560_);
lean_ctor_set(v___x_5563_, 1, v___x_5562_);
v___y_5496_ = v___y_5542_;
v___y_5497_ = v___x_5554_;
v___y_5498_ = v___x_5550_;
v___y_5499_ = v___y_5543_;
v___y_5500_ = v___y_5544_;
v___y_5501_ = v___y_5536_;
v___y_5502_ = v___y_5537_;
v___y_5503_ = v___y_5540_;
v___y_5504_ = v___y_5535_;
v___y_5505_ = v___y_5546_;
v___y_5506_ = v___y_5541_;
v___y_5507_ = v___y_5545_;
v___y_5508_ = v___y_5539_;
v___y_5509_ = v___y_5538_;
v___y_5510_ = v___x_5563_;
goto v___jp_5495_;
}
default: 
{
lean_object* v_ref_5564_; lean_object* v_proof_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; 
v_ref_5564_ = lean_ctor_get(v_proof_5553_, 1);
lean_inc(v_ref_5564_);
v_proof_5565_ = lean_ctor_get(v_proof_5553_, 2);
lean_inc_ref(v_proof_5565_);
lean_dec_ref_known(v_proof_5553_, 3);
v___x_5566_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_5567_ = l_Lean_MessageData_ofSyntax(v_ref_5564_);
v___x_5568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5568_, 0, v___x_5566_);
lean_ctor_set(v___x_5568_, 1, v___x_5567_);
v___x_5569_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_5570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5570_, 0, v___x_5568_);
lean_ctor_set(v___x_5570_, 1, v___x_5569_);
v___x_5571_ = l_Lean_MessageData_ofExpr(v_proof_5565_);
v___x_5572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5572_, 0, v___x_5570_);
lean_ctor_set(v___x_5572_, 1, v___x_5571_);
v___y_5496_ = v___y_5542_;
v___y_5497_ = v___x_5554_;
v___y_5498_ = v___x_5550_;
v___y_5499_ = v___y_5543_;
v___y_5500_ = v___y_5544_;
v___y_5501_ = v___y_5536_;
v___y_5502_ = v___y_5537_;
v___y_5503_ = v___y_5540_;
v___y_5504_ = v___y_5535_;
v___y_5505_ = v___y_5546_;
v___y_5506_ = v___y_5541_;
v___y_5507_ = v___y_5545_;
v___y_5508_ = v___y_5539_;
v___y_5509_ = v___y_5538_;
v___y_5510_ = v___x_5572_;
goto v___jp_5495_;
}
}
}
}
}
v___jp_5573_:
{
lean_object* v___x_5587_; 
v___x_5587_ = l_Lean_Elab_Tactic_VCGen_FrameSplit_instantiateMVarsS(v___y_5574_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_);
if (lean_obj_tag(v___x_5587_) == 0)
{
lean_object* v_a_5588_; lean_object* v___x_5589_; 
v_a_5588_ = lean_ctor_get(v___x_5587_, 0);
lean_inc(v_a_5588_);
lean_dec_ref_known(v___x_5587_, 1);
v___x_5589_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule(v_goal_5432_, v_info_5433_, v___y_5575_, v_a_5588_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_);
if (lean_obj_tag(v___x_5589_) == 0)
{
lean_object* v_a_5590_; lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5599_; 
v_a_5590_ = lean_ctor_get(v___x_5589_, 0);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5599_ == 0)
{
v___x_5592_ = v___x_5589_;
v_isShared_5593_ = v_isSharedCheck_5599_;
goto v_resetjp_5591_;
}
else
{
lean_inc(v_a_5590_);
lean_dec(v___x_5589_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5599_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5597_; 
v___x_5594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5594_, 0, v_scope_5431_);
lean_ctor_set(v___x_5594_, 1, v_a_5590_);
v___x_5595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5595_, 0, v___x_5594_);
if (v_isShared_5593_ == 0)
{
lean_ctor_set(v___x_5592_, 0, v___x_5595_);
v___x_5597_ = v___x_5592_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v___x_5595_);
v___x_5597_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
return v___x_5597_;
}
}
}
else
{
lean_object* v_a_5600_; lean_object* v___x_5602_; uint8_t v_isShared_5603_; uint8_t v_isSharedCheck_5607_; 
lean_dec_ref(v_scope_5431_);
v_a_5600_ = lean_ctor_get(v___x_5589_, 0);
v_isSharedCheck_5607_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5602_ = v___x_5589_;
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
else
{
lean_inc(v_a_5600_);
lean_dec(v___x_5589_);
v___x_5602_ = lean_box(0);
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
v_resetjp_5601_:
{
lean_object* v___x_5605_; 
if (v_isShared_5603_ == 0)
{
v___x_5605_ = v___x_5602_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_a_5600_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
return v___x_5605_;
}
}
}
}
else
{
lean_object* v_a_5608_; lean_object* v___x_5610_; uint8_t v_isShared_5611_; uint8_t v_isSharedCheck_5615_; 
lean_dec_ref(v___y_5575_);
lean_dec_ref(v_info_5433_);
lean_dec(v_goal_5432_);
lean_dec_ref(v_scope_5431_);
v_a_5608_ = lean_ctor_get(v___x_5587_, 0);
v_isSharedCheck_5615_ = !lean_is_exclusive(v___x_5587_);
if (v_isSharedCheck_5615_ == 0)
{
v___x_5610_ = v___x_5587_;
v_isShared_5611_ = v_isSharedCheck_5615_;
goto v_resetjp_5609_;
}
else
{
lean_inc(v_a_5608_);
lean_dec(v___x_5587_);
v___x_5610_ = lean_box(0);
v_isShared_5611_ = v_isSharedCheck_5615_;
goto v_resetjp_5609_;
}
v_resetjp_5609_:
{
lean_object* v___x_5613_; 
if (v_isShared_5611_ == 0)
{
v___x_5613_ = v___x_5610_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v_a_5608_);
v___x_5613_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
return v___x_5613_;
}
}
}
}
v___jp_5616_:
{
lean_object* v___x_5619_; 
lean_inc_ref(v_info_5433_);
lean_inc_ref(v___y_5618_);
v___x_5619_ = l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(v___y_5618_, v_info_5433_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_);
if (lean_obj_tag(v___x_5619_) == 0)
{
lean_object* v_a_5620_; lean_object* v_mkOpAppM_5621_; lean_object* v_proc_5622_; lean_object* v___x_5623_; lean_object* v___f_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; 
v_a_5620_ = lean_ctor_get(v___x_5619_, 0);
lean_inc(v_a_5620_);
lean_dec_ref_known(v___x_5619_, 1);
v_mkOpAppM_5621_ = lean_ctor_get(v___y_5618_, 2);
v_proc_5622_ = lean_ctor_get(v___y_5618_, 4);
lean_inc_ref(v_thm_5434_);
v___x_5623_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorem_global_x3f(v_thm_5434_);
lean_inc_ref_n(v_info_5433_, 2);
lean_inc_ref(v_mkOpAppM_5621_);
v___f_5624_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5624_, 0, v_mkOpAppM_5621_);
lean_closure_set(v___f_5624_, 1, v_info_5433_);
lean_inc_ref(v___y_5617_);
lean_inc(v_goal_5432_);
v___x_5625_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5625_, 0, v_info_5433_);
lean_ctor_set(v___x_5625_, 1, v_goal_5432_);
lean_ctor_set(v___x_5625_, 2, v_a_5620_);
lean_ctor_set(v___x_5625_, 3, v___x_5623_);
lean_ctor_set(v___x_5625_, 4, v___y_5617_);
lean_ctor_set(v___x_5625_, 5, v___f_5624_);
lean_inc_ref(v_proc_5622_);
lean_inc(v_a_5445_);
lean_inc_ref(v_a_5444_);
lean_inc(v_a_5443_);
lean_inc_ref(v_a_5442_);
lean_inc(v_a_5441_);
lean_inc_ref(v_a_5440_);
v___x_5626_ = lean_apply_8(v_proc_5622_, v___x_5625_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_, lean_box(0));
if (lean_obj_tag(v___x_5626_) == 0)
{
lean_object* v_a_5627_; 
v_a_5627_ = lean_ctor_get(v___x_5626_, 0);
lean_inc(v_a_5627_);
lean_dec_ref_known(v___x_5626_, 1);
if (lean_obj_tag(v_a_5627_) == 1)
{
lean_object* v_options_5628_; uint8_t v_hasTrace_5629_; 
lean_dec_ref(v___y_5617_);
lean_dec_ref(v_thm_5434_);
v_options_5628_ = lean_ctor_get(v_a_5444_, 2);
v_hasTrace_5629_ = lean_ctor_get_uint8(v_options_5628_, sizeof(void*)*1);
if (v_hasTrace_5629_ == 0)
{
lean_object* v_val_5630_; 
v_val_5630_ = lean_ctor_get(v_a_5627_, 0);
lean_inc(v_val_5630_);
lean_dec_ref_known(v_a_5627_, 1);
v___y_5574_ = v_val_5630_;
v___y_5575_ = v___y_5618_;
v___y_5576_ = v_a_5435_;
v___y_5577_ = v_a_5436_;
v___y_5578_ = v_a_5437_;
v___y_5579_ = v_a_5438_;
v___y_5580_ = v_a_5439_;
v___y_5581_ = v_a_5440_;
v___y_5582_ = v_a_5441_;
v___y_5583_ = v_a_5442_;
v___y_5584_ = v_a_5443_;
v___y_5585_ = v_a_5444_;
v___y_5586_ = v_a_5445_;
goto v___jp_5573_;
}
else
{
lean_object* v_val_5631_; lean_object* v_inheritedTraceOptions_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; uint8_t v___x_5635_; 
v_val_5631_ = lean_ctor_get(v_a_5627_, 0);
lean_inc(v_val_5631_);
lean_dec_ref_known(v_a_5627_, 1);
v_inheritedTraceOptions_5632_ = lean_ctor_get(v_a_5444_, 13);
v___x_5633_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5634_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5635_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5632_, v_options_5628_, v___x_5634_);
if (v___x_5635_ == 0)
{
v___y_5574_ = v_val_5631_;
v___y_5575_ = v___y_5618_;
v___y_5576_ = v_a_5435_;
v___y_5577_ = v_a_5436_;
v___y_5578_ = v_a_5437_;
v___y_5579_ = v_a_5438_;
v___y_5580_ = v_a_5439_;
v___y_5581_ = v_a_5440_;
v___y_5582_ = v_a_5441_;
v___y_5583_ = v_a_5442_;
v___y_5584_ = v_a_5443_;
v___y_5585_ = v_a_5444_;
v___y_5586_ = v_a_5445_;
goto v___jp_5573_;
}
else
{
lean_object* v_frame_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; 
v_frame_5636_ = lean_ctor_get(v_val_5631_, 0);
v___x_5637_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9);
v___x_5638_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5433_);
v___x_5639_ = l_Lean_MessageData_ofExpr(v___x_5638_);
v___x_5640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5637_);
lean_ctor_set(v___x_5640_, 1, v___x_5639_);
v___x_5641_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3);
v___x_5642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5640_);
lean_ctor_set(v___x_5642_, 1, v___x_5641_);
lean_inc_ref(v_frame_5636_);
v___x_5643_ = l_Lean_indentExpr(v_frame_5636_);
v___x_5644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5642_);
lean_ctor_set(v___x_5644_, 1, v___x_5643_);
v___x_5645_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5633_, v___x_5644_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_);
if (lean_obj_tag(v___x_5645_) == 0)
{
lean_dec_ref_known(v___x_5645_, 1);
v___y_5574_ = v_val_5631_;
v___y_5575_ = v___y_5618_;
v___y_5576_ = v_a_5435_;
v___y_5577_ = v_a_5436_;
v___y_5578_ = v_a_5437_;
v___y_5579_ = v_a_5438_;
v___y_5580_ = v_a_5439_;
v___y_5581_ = v_a_5440_;
v___y_5582_ = v_a_5441_;
v___y_5583_ = v_a_5442_;
v___y_5584_ = v_a_5443_;
v___y_5585_ = v_a_5444_;
v___y_5586_ = v_a_5445_;
goto v___jp_5573_;
}
else
{
lean_object* v_a_5646_; lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5653_; 
lean_dec(v_val_5631_);
lean_dec_ref(v___y_5618_);
lean_dec_ref(v_info_5433_);
lean_dec(v_goal_5432_);
lean_dec_ref(v_scope_5431_);
v_a_5646_ = lean_ctor_get(v___x_5645_, 0);
v_isSharedCheck_5653_ = !lean_is_exclusive(v___x_5645_);
if (v_isSharedCheck_5653_ == 0)
{
v___x_5648_ = v___x_5645_;
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
else
{
lean_inc(v_a_5646_);
lean_dec(v___x_5645_);
v___x_5648_ = lean_box(0);
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
v_resetjp_5647_:
{
lean_object* v___x_5651_; 
if (v_isShared_5649_ == 0)
{
v___x_5651_ = v___x_5648_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_a_5646_);
v___x_5651_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
return v___x_5651_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5627_);
lean_dec_ref(v___y_5618_);
v___y_5535_ = v___y_5617_;
v___y_5536_ = v_a_5435_;
v___y_5537_ = v_a_5436_;
v___y_5538_ = v_a_5437_;
v___y_5539_ = v_a_5438_;
v___y_5540_ = v_a_5439_;
v___y_5541_ = v_a_5440_;
v___y_5542_ = v_a_5441_;
v___y_5543_ = v_a_5442_;
v___y_5544_ = v_a_5443_;
v___y_5545_ = v_a_5444_;
v___y_5546_ = v_a_5445_;
goto v___jp_5534_;
}
}
else
{
lean_object* v_a_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5661_; 
lean_dec_ref(v___y_5618_);
lean_dec_ref(v___y_5617_);
lean_dec_ref(v_thm_5434_);
lean_dec_ref(v_info_5433_);
lean_dec(v_goal_5432_);
lean_dec_ref(v_scope_5431_);
v_a_5654_ = lean_ctor_get(v___x_5626_, 0);
v_isSharedCheck_5661_ = !lean_is_exclusive(v___x_5626_);
if (v_isSharedCheck_5661_ == 0)
{
v___x_5656_ = v___x_5626_;
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_a_5654_);
lean_dec(v___x_5626_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v___x_5659_; 
if (v_isShared_5657_ == 0)
{
v___x_5659_ = v___x_5656_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5654_);
v___x_5659_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
return v___x_5659_;
}
}
}
}
else
{
lean_object* v_a_5662_; lean_object* v___x_5664_; uint8_t v_isShared_5665_; uint8_t v_isSharedCheck_5669_; 
lean_dec_ref(v___y_5618_);
lean_dec_ref(v___y_5617_);
lean_dec_ref(v_thm_5434_);
lean_dec_ref(v_info_5433_);
lean_dec(v_goal_5432_);
lean_dec_ref(v_scope_5431_);
v_a_5662_ = lean_ctor_get(v___x_5619_, 0);
v_isSharedCheck_5669_ = !lean_is_exclusive(v___x_5619_);
if (v_isSharedCheck_5669_ == 0)
{
v___x_5664_ = v___x_5619_;
v_isShared_5665_ = v_isSharedCheck_5669_;
goto v_resetjp_5663_;
}
else
{
lean_inc(v_a_5662_);
lean_dec(v___x_5619_);
v___x_5664_ = lean_box(0);
v_isShared_5665_ = v_isSharedCheck_5669_;
goto v_resetjp_5663_;
}
v_resetjp_5663_:
{
lean_object* v___x_5667_; 
if (v_isShared_5665_ == 0)
{
v___x_5667_ = v___x_5664_;
goto v_reusejp_5666_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_a_5662_);
v___x_5667_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5666_;
}
v_reusejp_5666_:
{
return v___x_5667_;
}
}
}
}
v___jp_5670_:
{
lean_object* v___x_5672_; 
v___x_5672_ = l_Lean_Elab_Tactic_VCGen_meetFrameProc;
v___y_5617_ = v___y_5671_;
v___y_5618_ = v___x_5672_;
goto v___jp_5616_;
}
v___jp_5673_:
{
if (lean_obj_tag(v___y_5674_) == 0)
{
lean_object* v_a_5675_; lean_object* v___x_5677_; uint8_t v_isShared_5678_; uint8_t v_isSharedCheck_5695_; 
v_a_5675_ = lean_ctor_get(v___y_5674_, 0);
v_isSharedCheck_5695_ = !lean_is_exclusive(v___y_5674_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5677_ = v___y_5674_;
v_isShared_5678_ = v_isSharedCheck_5695_;
goto v_resetjp_5676_;
}
else
{
lean_inc(v_a_5675_);
lean_dec(v___y_5674_);
v___x_5677_ = lean_box(0);
v_isShared_5678_ = v_isSharedCheck_5695_;
goto v_resetjp_5676_;
}
v_resetjp_5676_:
{
if (lean_obj_tag(v_a_5675_) == 1)
{
uint8_t v_conjunctivePre_5679_; 
lean_del_object(v___x_5677_);
v_conjunctivePre_5679_ = lean_ctor_get_uint8(v_thm_5434_, sizeof(void*)*4);
if (v_conjunctivePre_5679_ == 0)
{
lean_object* v_val_5680_; lean_object* v___x_5681_; uint8_t v___x_5682_; 
v_val_5680_ = lean_ctor_get(v_a_5675_, 0);
lean_inc(v_val_5680_);
lean_dec_ref_known(v_a_5675_, 1);
v___x_5681_ = l_Lean_Elab_Tactic_VCGen_WPApp_post(v_info_5433_);
v___x_5682_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost(v___x_5681_);
if (v___x_5682_ == 0)
{
lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; 
v___x_5683_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v_info_5433_);
v___x_5684_ = l_Lean_Expr_getAppFn(v___x_5683_);
lean_dec_ref(v___x_5683_);
v___x_5685_ = l_Lean_Expr_constName_x3f(v___x_5684_);
lean_dec_ref(v___x_5684_);
if (lean_obj_tag(v___x_5685_) == 0)
{
v___y_5671_ = v_val_5680_;
goto v___jp_5670_;
}
else
{
lean_object* v_val_5686_; lean_object* v_frameProcs_5687_; lean_object* v___x_5688_; 
v_val_5686_ = lean_ctor_get(v___x_5685_, 0);
lean_inc(v_val_5686_);
lean_dec_ref_known(v___x_5685_, 1);
v_frameProcs_5687_ = lean_ctor_get(v_a_5435_, 1);
v___x_5688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(v_frameProcs_5687_, v_val_5686_);
lean_dec(v_val_5686_);
if (lean_obj_tag(v___x_5688_) == 0)
{
v___y_5671_ = v_val_5680_;
goto v___jp_5670_;
}
else
{
lean_object* v_val_5689_; 
v_val_5689_ = lean_ctor_get(v___x_5688_, 0);
lean_inc(v_val_5689_);
lean_dec_ref_known(v___x_5688_, 1);
v___y_5617_ = v_val_5680_;
v___y_5618_ = v_val_5689_;
goto v___jp_5616_;
}
}
}
else
{
v___y_5535_ = v_val_5680_;
v___y_5536_ = v_a_5435_;
v___y_5537_ = v_a_5436_;
v___y_5538_ = v_a_5437_;
v___y_5539_ = v_a_5438_;
v___y_5540_ = v_a_5439_;
v___y_5541_ = v_a_5440_;
v___y_5542_ = v_a_5441_;
v___y_5543_ = v_a_5442_;
v___y_5544_ = v_a_5443_;
v___y_5545_ = v_a_5444_;
v___y_5546_ = v_a_5445_;
goto v___jp_5534_;
}
}
else
{
lean_object* v_val_5690_; 
v_val_5690_ = lean_ctor_get(v_a_5675_, 0);
lean_inc(v_val_5690_);
lean_dec_ref_known(v_a_5675_, 1);
v___y_5535_ = v_val_5690_;
v___y_5536_ = v_a_5435_;
v___y_5537_ = v_a_5436_;
v___y_5538_ = v_a_5437_;
v___y_5539_ = v_a_5438_;
v___y_5540_ = v_a_5439_;
v___y_5541_ = v_a_5440_;
v___y_5542_ = v_a_5441_;
v___y_5543_ = v_a_5442_;
v___y_5544_ = v_a_5443_;
v___y_5545_ = v_a_5444_;
v___y_5546_ = v_a_5445_;
goto v___jp_5534_;
}
}
else
{
lean_object* v___x_5691_; lean_object* v___x_5693_; 
lean_dec(v_a_5675_);
lean_dec_ref(v_thm_5434_);
lean_dec_ref(v_info_5433_);
lean_dec(v_goal_5432_);
lean_dec_ref(v_scope_5431_);
v___x_5691_ = lean_box(0);
if (v_isShared_5678_ == 0)
{
lean_ctor_set(v___x_5677_, 0, v___x_5691_);
v___x_5693_ = v___x_5677_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v___x_5691_);
v___x_5693_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
return v___x_5693_;
}
}
}
}
else
{
lean_object* v_a_5696_; lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5703_; 
lean_dec_ref(v_thm_5434_);
lean_dec_ref(v_info_5433_);
lean_dec(v_goal_5432_);
lean_dec_ref(v_scope_5431_);
v_a_5696_ = lean_ctor_get(v___y_5674_, 0);
v_isSharedCheck_5703_ = !lean_is_exclusive(v___y_5674_);
if (v_isSharedCheck_5703_ == 0)
{
v___x_5698_ = v___y_5674_;
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
else
{
lean_inc(v_a_5696_);
lean_dec(v___y_5674_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
lean_object* v___x_5701_; 
if (v_isShared_5699_ == 0)
{
v___x_5701_ = v___x_5698_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_a_5696_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___boxed(lean_object* v_scope_5772_, lean_object* v_goal_5773_, lean_object* v_info_5774_, lean_object* v_thm_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_){
_start:
{
lean_object* v_res_5788_; 
v_res_5788_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(v_scope_5772_, v_goal_5773_, v_info_5774_, v_thm_5775_, v_a_5776_, v_a_5777_, v_a_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_);
lean_dec(v_a_5786_);
lean_dec_ref(v_a_5785_);
lean_dec(v_a_5784_);
lean_dec_ref(v_a_5783_);
lean_dec(v_a_5782_);
lean_dec_ref(v_a_5781_);
lean_dec(v_a_5780_);
lean_dec_ref(v_a_5779_);
lean_dec(v_a_5778_);
lean_dec(v_a_5777_);
lean_dec_ref(v_a_5776_);
return v_res_5788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1(lean_object* v_00_u03b2_5789_, lean_object* v_m_5790_, lean_object* v_a_5791_){
_start:
{
lean_object* v___x_5792_; 
v___x_5792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(v_m_5790_, v_a_5791_);
return v___x_5792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___boxed(lean_object* v_00_u03b2_5793_, lean_object* v_m_5794_, lean_object* v_a_5795_){
_start:
{
lean_object* v_res_5796_; 
v_res_5796_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1(v_00_u03b2_5793_, v_m_5794_, v_a_5795_);
lean_dec(v_a_5795_);
lean_dec_ref(v_m_5794_);
return v_res_5796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1(lean_object* v_00_u03b2_5797_, lean_object* v_a_5798_, lean_object* v_x_5799_){
_start:
{
lean_object* v___x_5800_; 
v___x_5800_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(v_a_5798_, v_x_5799_);
return v___x_5800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5801_, lean_object* v_a_5802_, lean_object* v_x_5803_){
_start:
{
lean_object* v_res_5804_; 
v_res_5804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1(v_00_u03b2_5801_, v_a_5802_, v_x_5803_);
lean_dec(v_x_5803_);
lean_dec(v_a_5802_);
return v_res_5804_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_5809_; lean_object* v___x_5810_; 
v___x_5809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__1));
v___x_5810_ = l_Lean_stringToMessageData(v___x_5809_);
return v___x_5810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(lean_object* v_scope_5811_, lean_object* v_goal_5812_, lean_object* v_info_5813_, lean_object* v___x_5814_, lean_object* v_as_5815_, size_t v_sz_5816_, size_t v_i_5817_, lean_object* v_b_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_){
_start:
{
lean_object* v_a_5832_; uint8_t v___x_5836_; 
v___x_5836_ = lean_usize_dec_lt(v_i_5817_, v_sz_5816_);
if (v___x_5836_ == 0)
{
lean_object* v___x_5837_; 
lean_dec_ref(v___x_5814_);
lean_dec_ref(v_info_5813_);
lean_dec(v_goal_5812_);
lean_dec_ref(v_scope_5811_);
v___x_5837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5837_, 0, v_b_5818_);
return v___x_5837_;
}
else
{
lean_object* v_a_5838_; lean_object* v___x_5839_; 
lean_dec_ref(v_b_5818_);
v_a_5838_ = lean_array_uget_borrowed(v_as_5815_, v_i_5817_);
lean_inc(v_a_5838_);
lean_inc_ref(v_info_5813_);
lean_inc(v_goal_5812_);
lean_inc_ref(v_scope_5811_);
v___x_5839_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(v_scope_5811_, v_goal_5812_, v_info_5813_, v_a_5838_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_);
if (lean_obj_tag(v___x_5839_) == 0)
{
lean_object* v_a_5840_; lean_object* v___x_5842_; uint8_t v_isShared_5843_; uint8_t v_isSharedCheck_5892_; 
v_a_5840_ = lean_ctor_get(v___x_5839_, 0);
v_isSharedCheck_5892_ = !lean_is_exclusive(v___x_5839_);
if (v_isSharedCheck_5892_ == 0)
{
v___x_5842_ = v___x_5839_;
v_isShared_5843_ = v_isSharedCheck_5892_;
goto v_resetjp_5841_;
}
else
{
lean_inc(v_a_5840_);
lean_dec(v___x_5839_);
v___x_5842_ = lean_box(0);
v_isShared_5843_ = v_isSharedCheck_5892_;
goto v_resetjp_5841_;
}
v_resetjp_5841_:
{
lean_object* v___x_5844_; 
v___x_5844_ = lean_box(0);
if (lean_obj_tag(v_a_5840_) == 1)
{
lean_object* v___x_5845_; lean_object* v___x_5847_; 
lean_dec_ref(v___x_5814_);
lean_dec_ref(v_info_5813_);
lean_dec(v_goal_5812_);
lean_dec_ref(v_scope_5811_);
v___x_5845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5845_, 0, v_a_5840_);
lean_ctor_set(v___x_5845_, 1, v___x_5844_);
if (v_isShared_5843_ == 0)
{
lean_ctor_set(v___x_5842_, 0, v___x_5845_);
v___x_5847_ = v___x_5842_;
goto v_reusejp_5846_;
}
else
{
lean_object* v_reuseFailAlloc_5848_; 
v_reuseFailAlloc_5848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5848_, 0, v___x_5845_);
v___x_5847_ = v_reuseFailAlloc_5848_;
goto v_reusejp_5846_;
}
v_reusejp_5846_:
{
return v___x_5847_;
}
}
else
{
lean_object* v_options_5849_; lean_object* v_inheritedTraceOptions_5850_; uint8_t v_hasTrace_5851_; lean_object* v___x_5852_; 
lean_del_object(v___x_5842_);
lean_dec(v_a_5840_);
v_options_5849_ = lean_ctor_get(v___y_5828_, 2);
v_inheritedTraceOptions_5850_ = lean_ctor_get(v___y_5828_, 13);
v_hasTrace_5851_ = lean_ctor_get_uint8(v_options_5849_, sizeof(void*)*1);
v___x_5852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0));
if (v_hasTrace_5851_ == 0)
{
v_a_5832_ = v___x_5852_;
goto v___jp_5831_;
}
else
{
lean_object* v___x_5853_; lean_object* v___x_5854_; uint8_t v___x_5855_; 
v___x_5853_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5854_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5855_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5850_, v_options_5849_, v___x_5854_);
if (v___x_5855_ == 0)
{
v_a_5832_ = v___x_5852_;
goto v___jp_5831_;
}
else
{
lean_object* v_proof_5856_; lean_object* v___x_5857_; lean_object* v___y_5859_; 
v_proof_5856_ = lean_ctor_get(v_a_5838_, 1);
v___x_5857_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2);
switch(lean_obj_tag(v_proof_5856_))
{
case 0:
{
lean_object* v_declName_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; 
v_declName_5874_ = lean_ctor_get(v_proof_5856_, 0);
v___x_5875_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_5874_);
v___x_5876_ = l_Lean_MessageData_ofName(v_declName_5874_);
v___x_5877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5877_, 0, v___x_5875_);
lean_ctor_set(v___x_5877_, 1, v___x_5876_);
v___y_5859_ = v___x_5877_;
goto v___jp_5858_;
}
case 1:
{
lean_object* v_fvarId_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; 
v_fvarId_5878_ = lean_ctor_get(v_proof_5856_, 0);
v___x_5879_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_5878_);
v___x_5880_ = l_Lean_mkFVar(v_fvarId_5878_);
v___x_5881_ = l_Lean_MessageData_ofExpr(v___x_5880_);
v___x_5882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5882_, 0, v___x_5879_);
lean_ctor_set(v___x_5882_, 1, v___x_5881_);
v___y_5859_ = v___x_5882_;
goto v___jp_5858_;
}
default: 
{
lean_object* v_ref_5883_; lean_object* v_proof_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; 
v_ref_5883_ = lean_ctor_get(v_proof_5856_, 1);
v_proof_5884_ = lean_ctor_get(v_proof_5856_, 2);
v___x_5885_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_5883_);
v___x_5886_ = l_Lean_MessageData_ofSyntax(v_ref_5883_);
v___x_5887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5887_, 0, v___x_5885_);
lean_ctor_set(v___x_5887_, 1, v___x_5886_);
v___x_5888_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_5889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5889_, 0, v___x_5887_);
lean_ctor_set(v___x_5889_, 1, v___x_5888_);
lean_inc_ref(v_proof_5884_);
v___x_5890_ = l_Lean_MessageData_ofExpr(v_proof_5884_);
v___x_5891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5891_, 0, v___x_5889_);
lean_ctor_set(v___x_5891_, 1, v___x_5890_);
v___y_5859_ = v___x_5891_;
goto v___jp_5858_;
}
}
v___jp_5858_:
{
lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; 
v___x_5860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5860_, 0, v___x_5857_);
lean_ctor_set(v___x_5860_, 1, v___y_5859_);
v___x_5861_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_5862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5862_, 0, v___x_5860_);
lean_ctor_set(v___x_5862_, 1, v___x_5861_);
lean_inc_ref(v___x_5814_);
v___x_5863_ = l_Lean_MessageData_ofExpr(v___x_5814_);
v___x_5864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5864_, 0, v___x_5862_);
lean_ctor_set(v___x_5864_, 1, v___x_5863_);
v___x_5865_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5853_, v___x_5864_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_);
if (lean_obj_tag(v___x_5865_) == 0)
{
lean_dec_ref_known(v___x_5865_, 1);
v_a_5832_ = v___x_5852_;
goto v___jp_5831_;
}
else
{
lean_object* v_a_5866_; lean_object* v___x_5868_; uint8_t v_isShared_5869_; uint8_t v_isSharedCheck_5873_; 
lean_dec_ref(v___x_5814_);
lean_dec_ref(v_info_5813_);
lean_dec(v_goal_5812_);
lean_dec_ref(v_scope_5811_);
v_a_5866_ = lean_ctor_get(v___x_5865_, 0);
v_isSharedCheck_5873_ = !lean_is_exclusive(v___x_5865_);
if (v_isSharedCheck_5873_ == 0)
{
v___x_5868_ = v___x_5865_;
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
else
{
lean_inc(v_a_5866_);
lean_dec(v___x_5865_);
v___x_5868_ = lean_box(0);
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
v_resetjp_5867_:
{
lean_object* v___x_5871_; 
if (v_isShared_5869_ == 0)
{
v___x_5871_ = v___x_5868_;
goto v_reusejp_5870_;
}
else
{
lean_object* v_reuseFailAlloc_5872_; 
v_reuseFailAlloc_5872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5872_, 0, v_a_5866_);
v___x_5871_ = v_reuseFailAlloc_5872_;
goto v_reusejp_5870_;
}
v_reusejp_5870_:
{
return v___x_5871_;
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
lean_object* v_a_5893_; lean_object* v___x_5895_; uint8_t v_isShared_5896_; uint8_t v_isSharedCheck_5900_; 
lean_dec_ref(v___x_5814_);
lean_dec_ref(v_info_5813_);
lean_dec(v_goal_5812_);
lean_dec_ref(v_scope_5811_);
v_a_5893_ = lean_ctor_get(v___x_5839_, 0);
v_isSharedCheck_5900_ = !lean_is_exclusive(v___x_5839_);
if (v_isSharedCheck_5900_ == 0)
{
v___x_5895_ = v___x_5839_;
v_isShared_5896_ = v_isSharedCheck_5900_;
goto v_resetjp_5894_;
}
else
{
lean_inc(v_a_5893_);
lean_dec(v___x_5839_);
v___x_5895_ = lean_box(0);
v_isShared_5896_ = v_isSharedCheck_5900_;
goto v_resetjp_5894_;
}
v_resetjp_5894_:
{
lean_object* v___x_5898_; 
if (v_isShared_5896_ == 0)
{
v___x_5898_ = v___x_5895_;
goto v_reusejp_5897_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v_a_5893_);
v___x_5898_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5897_;
}
v_reusejp_5897_:
{
return v___x_5898_;
}
}
}
}
v___jp_5831_:
{
size_t v___x_5833_; size_t v___x_5834_; 
v___x_5833_ = ((size_t)1ULL);
v___x_5834_ = lean_usize_add(v_i_5817_, v___x_5833_);
lean_inc_ref(v_a_5832_);
v_i_5817_ = v___x_5834_;
v_b_5818_ = v_a_5832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___boxed(lean_object** _args){
lean_object* v_scope_5901_ = _args[0];
lean_object* v_goal_5902_ = _args[1];
lean_object* v_info_5903_ = _args[2];
lean_object* v___x_5904_ = _args[3];
lean_object* v_as_5905_ = _args[4];
lean_object* v_sz_5906_ = _args[5];
lean_object* v_i_5907_ = _args[6];
lean_object* v_b_5908_ = _args[7];
lean_object* v___y_5909_ = _args[8];
lean_object* v___y_5910_ = _args[9];
lean_object* v___y_5911_ = _args[10];
lean_object* v___y_5912_ = _args[11];
lean_object* v___y_5913_ = _args[12];
lean_object* v___y_5914_ = _args[13];
lean_object* v___y_5915_ = _args[14];
lean_object* v___y_5916_ = _args[15];
lean_object* v___y_5917_ = _args[16];
lean_object* v___y_5918_ = _args[17];
lean_object* v___y_5919_ = _args[18];
lean_object* v___y_5920_ = _args[19];
_start:
{
size_t v_sz_boxed_5921_; size_t v_i_boxed_5922_; lean_object* v_res_5923_; 
v_sz_boxed_5921_ = lean_unbox_usize(v_sz_5906_);
lean_dec(v_sz_5906_);
v_i_boxed_5922_ = lean_unbox_usize(v_i_5907_);
lean_dec(v_i_5907_);
v_res_5923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(v_scope_5901_, v_goal_5902_, v_info_5903_, v___x_5904_, v_as_5905_, v_sz_boxed_5921_, v_i_boxed_5922_, v_b_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_);
lean_dec(v___y_5919_);
lean_dec_ref(v___y_5918_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
lean_dec(v___y_5915_);
lean_dec_ref(v___y_5914_);
lean_dec(v___y_5913_);
lean_dec_ref(v___y_5912_);
lean_dec(v___y_5911_);
lean_dec(v___y_5910_);
lean_dec_ref(v___y_5909_);
lean_dec_ref(v_as_5905_);
return v_res_5923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0(lean_object* v_specs_5924_, lean_object* v___x_5925_, lean_object* v_scope_5926_, lean_object* v_goal_5927_, lean_object* v_info_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_){
_start:
{
lean_object* v___x_5941_; 
lean_inc_ref(v___x_5925_);
v___x_5941_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_findSpecs(v_specs_5924_, v___x_5925_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_);
if (lean_obj_tag(v___x_5941_) == 0)
{
lean_object* v_a_5942_; lean_object* v___x_5943_; size_t v_sz_5944_; size_t v___x_5945_; lean_object* v___x_5946_; 
v_a_5942_ = lean_ctor_get(v___x_5941_, 0);
lean_inc(v_a_5942_);
lean_dec_ref_known(v___x_5941_, 1);
v___x_5943_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0));
v_sz_5944_ = lean_array_size(v_a_5942_);
v___x_5945_ = ((size_t)0ULL);
lean_inc_ref(v___x_5925_);
lean_inc_ref(v_info_5928_);
v___x_5946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(v_scope_5926_, v_goal_5927_, v_info_5928_, v___x_5925_, v_a_5942_, v_sz_5944_, v___x_5945_, v___x_5943_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_);
if (lean_obj_tag(v___x_5946_) == 0)
{
lean_object* v_a_5947_; lean_object* v___x_5949_; uint8_t v_isShared_5950_; uint8_t v_isSharedCheck_5958_; 
v_a_5947_ = lean_ctor_get(v___x_5946_, 0);
v_isSharedCheck_5958_ = !lean_is_exclusive(v___x_5946_);
if (v_isSharedCheck_5958_ == 0)
{
v___x_5949_ = v___x_5946_;
v_isShared_5950_ = v_isSharedCheck_5958_;
goto v_resetjp_5948_;
}
else
{
lean_inc(v_a_5947_);
lean_dec(v___x_5946_);
v___x_5949_ = lean_box(0);
v_isShared_5950_ = v_isSharedCheck_5958_;
goto v_resetjp_5948_;
}
v_resetjp_5948_:
{
lean_object* v_fst_5951_; 
v_fst_5951_ = lean_ctor_get(v_a_5947_, 0);
lean_inc(v_fst_5951_);
lean_dec(v_a_5947_);
if (lean_obj_tag(v_fst_5951_) == 0)
{
lean_object* v___x_5952_; lean_object* v___x_5953_; 
lean_del_object(v___x_5949_);
v___x_5952_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v_info_5928_);
lean_dec_ref(v_info_5928_);
v___x_5953_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_5925_, v___x_5952_, v_a_5942_, v___y_5929_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_);
return v___x_5953_;
}
else
{
lean_object* v_val_5954_; lean_object* v___x_5956_; 
lean_dec(v_a_5942_);
lean_dec_ref(v_info_5928_);
lean_dec_ref(v___x_5925_);
v_val_5954_ = lean_ctor_get(v_fst_5951_, 0);
lean_inc(v_val_5954_);
lean_dec_ref_known(v_fst_5951_, 1);
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 0, v_val_5954_);
v___x_5956_ = v___x_5949_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v_val_5954_);
v___x_5956_ = v_reuseFailAlloc_5957_;
goto v_reusejp_5955_;
}
v_reusejp_5955_:
{
return v___x_5956_;
}
}
}
}
else
{
lean_object* v_a_5959_; lean_object* v___x_5961_; uint8_t v_isShared_5962_; uint8_t v_isSharedCheck_5966_; 
lean_dec(v_a_5942_);
lean_dec_ref(v_info_5928_);
lean_dec_ref(v___x_5925_);
v_a_5959_ = lean_ctor_get(v___x_5946_, 0);
v_isSharedCheck_5966_ = !lean_is_exclusive(v___x_5946_);
if (v_isSharedCheck_5966_ == 0)
{
v___x_5961_ = v___x_5946_;
v_isShared_5962_ = v_isSharedCheck_5966_;
goto v_resetjp_5960_;
}
else
{
lean_inc(v_a_5959_);
lean_dec(v___x_5946_);
v___x_5961_ = lean_box(0);
v_isShared_5962_ = v_isSharedCheck_5966_;
goto v_resetjp_5960_;
}
v_resetjp_5960_:
{
lean_object* v___x_5964_; 
if (v_isShared_5962_ == 0)
{
v___x_5964_ = v___x_5961_;
goto v_reusejp_5963_;
}
else
{
lean_object* v_reuseFailAlloc_5965_; 
v_reuseFailAlloc_5965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5965_, 0, v_a_5959_);
v___x_5964_ = v_reuseFailAlloc_5965_;
goto v_reusejp_5963_;
}
v_reusejp_5963_:
{
return v___x_5964_;
}
}
}
}
else
{
lean_object* v_a_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5974_; 
lean_dec_ref(v_info_5928_);
lean_dec(v_goal_5927_);
lean_dec_ref(v_scope_5926_);
lean_dec_ref(v___x_5925_);
v_a_5967_ = lean_ctor_get(v___x_5941_, 0);
v_isSharedCheck_5974_ = !lean_is_exclusive(v___x_5941_);
if (v_isSharedCheck_5974_ == 0)
{
v___x_5969_ = v___x_5941_;
v_isShared_5970_ = v_isSharedCheck_5974_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_a_5967_);
lean_dec(v___x_5941_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5974_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5972_; 
if (v_isShared_5970_ == 0)
{
v___x_5972_ = v___x_5969_;
goto v_reusejp_5971_;
}
else
{
lean_object* v_reuseFailAlloc_5973_; 
v_reuseFailAlloc_5973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_a_5967_);
v___x_5972_ = v_reuseFailAlloc_5973_;
goto v_reusejp_5971_;
}
v_reusejp_5971_:
{
return v___x_5972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0___boxed(lean_object** _args){
lean_object* v_specs_5975_ = _args[0];
lean_object* v___x_5976_ = _args[1];
lean_object* v_scope_5977_ = _args[2];
lean_object* v_goal_5978_ = _args[3];
lean_object* v_info_5979_ = _args[4];
lean_object* v___y_5980_ = _args[5];
lean_object* v___y_5981_ = _args[6];
lean_object* v___y_5982_ = _args[7];
lean_object* v___y_5983_ = _args[8];
lean_object* v___y_5984_ = _args[9];
lean_object* v___y_5985_ = _args[10];
lean_object* v___y_5986_ = _args[11];
lean_object* v___y_5987_ = _args[12];
lean_object* v___y_5988_ = _args[13];
lean_object* v___y_5989_ = _args[14];
lean_object* v___y_5990_ = _args[15];
lean_object* v___y_5991_ = _args[16];
_start:
{
lean_object* v_res_5992_; 
v_res_5992_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0(v_specs_5975_, v___x_5976_, v_scope_5977_, v_goal_5978_, v_info_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_);
lean_dec(v___y_5990_);
lean_dec_ref(v___y_5989_);
lean_dec(v___y_5988_);
lean_dec_ref(v___y_5987_);
lean_dec(v___y_5986_);
lean_dec_ref(v___y_5985_);
lean_dec(v___y_5984_);
lean_dec_ref(v___y_5983_);
lean_dec(v___y_5982_);
lean_dec(v___y_5981_);
lean_dec_ref(v___y_5980_);
lean_dec_ref(v_specs_5975_);
return v_res_5992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(lean_object* v_scope_5993_, lean_object* v_goal_5994_, lean_object* v_info_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_, lean_object* v_a_6001_, lean_object* v_a_6002_, lean_object* v_a_6003_, lean_object* v_a_6004_, lean_object* v_a_6005_, lean_object* v_a_6006_){
_start:
{
lean_object* v_specs_6008_; lean_object* v___x_6009_; lean_object* v___f_6010_; lean_object* v___x_6011_; 
v_specs_6008_ = lean_ctor_get(v_scope_5993_, 0);
lean_inc_ref(v_specs_6008_);
v___x_6009_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5995_);
lean_inc(v_goal_5994_);
v___f_6010_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0___boxed), 17, 5);
lean_closure_set(v___f_6010_, 0, v_specs_6008_);
lean_closure_set(v___f_6010_, 1, v___x_6009_);
lean_closure_set(v___f_6010_, 2, v_scope_5993_);
lean_closure_set(v___f_6010_, 3, v_goal_5994_);
lean_closure_set(v___f_6010_, 4, v_info_5995_);
v___x_6011_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_5994_, v___f_6010_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_, v_a_6001_, v_a_6002_, v_a_6003_, v_a_6004_, v_a_6005_, v_a_6006_);
return v___x_6011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___boxed(lean_object* v_scope_6012_, lean_object* v_goal_6013_, lean_object* v_info_6014_, lean_object* v_a_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_, lean_object* v_a_6025_, lean_object* v_a_6026_){
_start:
{
lean_object* v_res_6027_; 
v_res_6027_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(v_scope_6012_, v_goal_6013_, v_info_6014_, v_a_6015_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_, v_a_6024_, v_a_6025_);
lean_dec(v_a_6025_);
lean_dec_ref(v_a_6024_);
lean_dec(v_a_6023_);
lean_dec_ref(v_a_6022_);
lean_dec(v_a_6021_);
lean_dec_ref(v_a_6020_);
lean_dec(v_a_6019_);
lean_dec_ref(v_a_6018_);
lean_dec(v_a_6017_);
lean_dec(v_a_6016_);
lean_dec_ref(v_a_6015_);
return v_res_6027_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6029_; lean_object* v___x_6030_; 
v___x_6029_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__0));
v___x_6030_ = l_Lean_stringToMessageData(v___x_6029_);
return v___x_6030_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3(void){
_start:
{
lean_object* v___x_6032_; lean_object* v___x_6033_; 
v___x_6032_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2));
v___x_6033_ = l_Lean_stringToMessageData(v___x_6032_);
return v___x_6033_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5(void){
_start:
{
lean_object* v___x_6035_; lean_object* v___x_6036_; 
v___x_6035_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4));
v___x_6036_ = l_Lean_stringToMessageData(v___x_6035_);
return v___x_6036_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7(void){
_start:
{
lean_object* v___x_6038_; lean_object* v___x_6039_; 
v___x_6038_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__6));
v___x_6039_ = l_Lean_stringToMessageData(v___x_6038_);
return v___x_6039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0(lean_object* v_goal_6042_, lean_object* v_scope_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_){
_start:
{
lean_object* v_gs_6057_; lean_object* v_g_6061_; lean_object* v___y_6067_; lean_object* v___y_6068_; lean_object* v___y_6073_; lean_object* v_g_6074_; lean_object* v___y_6080_; lean_object* v_gs_6081_; lean_object* v___y_6085_; lean_object* v_g_6086_; lean_object* v___y_6087_; lean_object* v___y_6109_; lean_object* v___y_6110_; lean_object* v___y_6111_; lean_object* v___y_6112_; lean_object* v___y_6113_; lean_object* v___y_6114_; lean_object* v___y_6115_; lean_object* v___y_6116_; lean_object* v___y_6117_; lean_object* v___y_6118_; lean_object* v___y_6119_; lean_object* v___y_6120_; lean_object* v___y_6121_; lean_object* v___y_6133_; lean_object* v___y_6134_; lean_object* v___y_6135_; lean_object* v___y_6136_; lean_object* v___y_6137_; lean_object* v___y_6138_; lean_object* v___y_6139_; lean_object* v___y_6140_; lean_object* v___y_6141_; lean_object* v___y_6142_; lean_object* v___y_6143_; lean_object* v___y_6144_; lean_object* v___y_6145_; lean_object* v___y_6146_; lean_object* v___y_6147_; lean_object* v___x_6271_; 
v___x_6271_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v___y_6045_);
if (lean_obj_tag(v___x_6271_) == 0)
{
lean_object* v_a_6272_; lean_object* v___x_6274_; uint8_t v_isShared_6275_; uint8_t v_isSharedCheck_6536_; 
v_a_6272_ = lean_ctor_get(v___x_6271_, 0);
v_isSharedCheck_6536_ = !lean_is_exclusive(v___x_6271_);
if (v_isSharedCheck_6536_ == 0)
{
v___x_6274_ = v___x_6271_;
v_isShared_6275_ = v_isSharedCheck_6536_;
goto v_resetjp_6273_;
}
else
{
lean_inc(v_a_6272_);
lean_dec(v___x_6271_);
v___x_6274_ = lean_box(0);
v_isShared_6275_ = v_isSharedCheck_6536_;
goto v_resetjp_6273_;
}
v_resetjp_6273_:
{
uint8_t v___x_6276_; 
v___x_6276_ = lean_unbox(v_a_6272_);
lean_dec(v_a_6272_);
if (v___x_6276_ == 0)
{
lean_object* v___x_6277_; 
lean_del_object(v___x_6274_);
lean_inc(v_goal_6042_);
v___x_6277_ = l_Lean_MVarId_getType(v_goal_6042_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_);
if (lean_obj_tag(v___x_6277_) == 0)
{
lean_object* v_a_6278_; lean_object* v___x_6280_; uint8_t v_isShared_6281_; uint8_t v_isSharedCheck_6523_; 
v_a_6278_ = lean_ctor_get(v___x_6277_, 0);
v_isSharedCheck_6523_ = !lean_is_exclusive(v___x_6277_);
if (v_isSharedCheck_6523_ == 0)
{
v___x_6280_ = v___x_6277_;
v_isShared_6281_ = v_isSharedCheck_6523_;
goto v_resetjp_6279_;
}
else
{
lean_inc(v_a_6278_);
lean_dec(v___x_6277_);
v___x_6280_ = lean_box(0);
v_isShared_6281_ = v_isSharedCheck_6523_;
goto v_resetjp_6279_;
}
v_resetjp_6279_:
{
lean_object* v_options_6288_; lean_object* v_inheritedTraceOptions_6289_; uint8_t v_hasTrace_6290_; lean_object* v___x_6291_; lean_object* v___y_6293_; lean_object* v___y_6294_; lean_object* v___y_6295_; lean_object* v___y_6296_; lean_object* v___y_6297_; lean_object* v___y_6298_; lean_object* v___y_6299_; lean_object* v___y_6300_; lean_object* v___y_6301_; lean_object* v___y_6302_; lean_object* v___y_6303_; 
v_options_6288_ = lean_ctor_get(v___y_6053_, 2);
v_inheritedTraceOptions_6289_ = lean_ctor_get(v___y_6053_, 13);
v_hasTrace_6290_ = lean_ctor_get_uint8(v_options_6288_, sizeof(void*)*1);
v___x_6291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_6290_ == 0)
{
v___y_6293_ = v___y_6044_;
v___y_6294_ = v___y_6045_;
v___y_6295_ = v___y_6046_;
v___y_6296_ = v___y_6047_;
v___y_6297_ = v___y_6048_;
v___y_6298_ = v___y_6049_;
v___y_6299_ = v___y_6050_;
v___y_6300_ = v___y_6051_;
v___y_6301_ = v___y_6052_;
v___y_6302_ = v___y_6053_;
v___y_6303_ = v___y_6054_;
goto v___jp_6292_;
}
else
{
lean_object* v___x_6509_; uint8_t v___x_6510_; 
v___x_6509_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_6510_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6289_, v_options_6288_, v___x_6509_);
if (v___x_6510_ == 0)
{
v___y_6293_ = v___y_6044_;
v___y_6294_ = v___y_6045_;
v___y_6295_ = v___y_6046_;
v___y_6296_ = v___y_6047_;
v___y_6297_ = v___y_6048_;
v___y_6298_ = v___y_6049_;
v___y_6299_ = v___y_6050_;
v___y_6300_ = v___y_6051_;
v___y_6301_ = v___y_6052_;
v___y_6302_ = v___y_6053_;
v___y_6303_ = v___y_6054_;
goto v___jp_6292_;
}
else
{
lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v___x_6513_; lean_object* v___x_6514_; 
v___x_6511_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7);
lean_inc(v_a_6278_);
v___x_6512_ = l_Lean_MessageData_ofExpr(v_a_6278_);
v___x_6513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6513_, 0, v___x_6511_);
lean_ctor_set(v___x_6513_, 1, v___x_6512_);
v___x_6514_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_6291_, v___x_6513_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_);
if (lean_obj_tag(v___x_6514_) == 0)
{
lean_dec_ref_known(v___x_6514_, 1);
v___y_6293_ = v___y_6044_;
v___y_6294_ = v___y_6045_;
v___y_6295_ = v___y_6046_;
v___y_6296_ = v___y_6047_;
v___y_6297_ = v___y_6048_;
v___y_6298_ = v___y_6049_;
v___y_6299_ = v___y_6050_;
v___y_6300_ = v___y_6051_;
v___y_6301_ = v___y_6052_;
v___y_6302_ = v___y_6053_;
v___y_6303_ = v___y_6054_;
goto v___jp_6292_;
}
else
{
lean_object* v_a_6515_; lean_object* v___x_6517_; uint8_t v_isShared_6518_; uint8_t v_isSharedCheck_6522_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6515_ = lean_ctor_get(v___x_6514_, 0);
v_isSharedCheck_6522_ = !lean_is_exclusive(v___x_6514_);
if (v_isSharedCheck_6522_ == 0)
{
v___x_6517_ = v___x_6514_;
v_isShared_6518_ = v_isSharedCheck_6522_;
goto v_resetjp_6516_;
}
else
{
lean_inc(v_a_6515_);
lean_dec(v___x_6514_);
v___x_6517_ = lean_box(0);
v_isShared_6518_ = v_isSharedCheck_6522_;
goto v_resetjp_6516_;
}
v_resetjp_6516_:
{
lean_object* v___x_6520_; 
if (v_isShared_6518_ == 0)
{
v___x_6520_ = v___x_6517_;
goto v_reusejp_6519_;
}
else
{
lean_object* v_reuseFailAlloc_6521_; 
v_reuseFailAlloc_6521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6521_, 0, v_a_6515_);
v___x_6520_ = v_reuseFailAlloc_6521_;
goto v_reusejp_6519_;
}
v_reusejp_6519_:
{
return v___x_6520_;
}
}
}
}
}
v___jp_6282_:
{
lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6286_; 
v___x_6283_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6283_, 0, v_a_6278_);
v___x_6284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6284_, 0, v___x_6283_);
if (v_isShared_6281_ == 0)
{
lean_ctor_set(v___x_6280_, 0, v___x_6284_);
v___x_6286_ = v___x_6280_;
goto v_reusejp_6285_;
}
else
{
lean_object* v_reuseFailAlloc_6287_; 
v_reuseFailAlloc_6287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6287_, 0, v___x_6284_);
v___x_6286_ = v_reuseFailAlloc_6287_;
goto v_reusejp_6285_;
}
v_reusejp_6285_:
{
return v___x_6286_;
}
}
v___jp_6292_:
{
lean_object* v___x_6304_; 
lean_inc(v_goal_6042_);
v___x_6304_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg(v_goal_6042_, v_a_6278_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6304_) == 0)
{
lean_object* v_a_6305_; 
v_a_6305_ = lean_ctor_get(v___x_6304_, 0);
lean_inc(v_a_6305_);
lean_dec_ref_known(v___x_6304_, 1);
if (lean_obj_tag(v_a_6305_) == 1)
{
lean_object* v_val_6306_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec(v_goal_6042_);
v_val_6306_ = lean_ctor_get(v_a_6305_, 0);
lean_inc(v_val_6306_);
lean_dec_ref_known(v_a_6305_, 1);
v_g_6061_ = v_val_6306_;
goto v___jp_6060_;
}
else
{
lean_object* v___x_6307_; 
lean_dec(v_a_6305_);
lean_inc(v_goal_6042_);
v___x_6307_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f(v_goal_6042_, v_a_6278_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6307_) == 0)
{
lean_object* v_a_6308_; 
v_a_6308_ = lean_ctor_get(v___x_6307_, 0);
lean_inc(v_a_6308_);
lean_dec_ref_known(v___x_6307_, 1);
if (lean_obj_tag(v_a_6308_) == 1)
{
lean_object* v_val_6309_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec(v_goal_6042_);
v_val_6309_ = lean_ctor_get(v_a_6308_, 0);
lean_inc(v_val_6309_);
lean_dec_ref_known(v_a_6308_, 1);
v_gs_6057_ = v_val_6309_;
goto v___jp_6056_;
}
else
{
lean_object* v___x_6310_; 
lean_dec(v_a_6308_);
lean_inc(v_a_6278_);
lean_inc(v_goal_6042_);
v___x_6310_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f(v_goal_6042_, v_a_6278_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6310_) == 0)
{
lean_object* v_a_6311_; 
v_a_6311_ = lean_ctor_get(v___x_6310_, 0);
lean_inc(v_a_6311_);
lean_dec_ref_known(v___x_6310_, 1);
if (lean_obj_tag(v_a_6311_) == 1)
{
lean_object* v_val_6312_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec(v_goal_6042_);
v_val_6312_ = lean_ctor_get(v_a_6311_, 0);
lean_inc(v_val_6312_);
lean_dec_ref_known(v_a_6311_, 1);
v_g_6061_ = v_val_6312_;
goto v___jp_6060_;
}
else
{
lean_object* v___x_6313_; 
lean_dec(v_a_6311_);
lean_inc(v_goal_6042_);
v___x_6313_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f(v_goal_6042_, v_a_6278_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6313_) == 0)
{
lean_object* v_a_6314_; 
v_a_6314_ = lean_ctor_get(v___x_6313_, 0);
lean_inc(v_a_6314_);
lean_dec_ref_known(v___x_6313_, 1);
if (lean_obj_tag(v_a_6314_) == 1)
{
lean_object* v_val_6315_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec(v_goal_6042_);
v_val_6315_ = lean_ctor_get(v_a_6314_, 0);
lean_inc(v_val_6315_);
lean_dec_ref_known(v_a_6314_, 1);
v_g_6061_ = v_val_6315_;
goto v___jp_6060_;
}
else
{
lean_object* v___x_6316_; 
lean_dec(v_a_6314_);
lean_inc(v_a_6278_);
lean_inc(v_goal_6042_);
v___x_6316_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f(v_goal_6042_, v_a_6278_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6316_) == 0)
{
lean_object* v_a_6317_; 
v_a_6317_ = lean_ctor_get(v___x_6316_, 0);
lean_inc(v_a_6317_);
lean_dec_ref_known(v___x_6316_, 1);
if (lean_obj_tag(v_a_6317_) == 1)
{
lean_object* v_val_6318_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec(v_goal_6042_);
v_val_6318_ = lean_ctor_get(v_a_6317_, 0);
lean_inc(v_val_6318_);
lean_dec_ref_known(v_a_6317_, 1);
v_g_6061_ = v_val_6318_;
goto v___jp_6060_;
}
else
{
lean_object* v___x_6319_; 
lean_dec(v_a_6317_);
lean_inc(v_a_6278_);
lean_inc(v_goal_6042_);
lean_inc_ref(v_scope_6043_);
v___x_6319_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f(v_scope_6043_, v_goal_6042_, v_a_6278_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6319_) == 0)
{
lean_object* v_a_6320_; 
v_a_6320_ = lean_ctor_get(v___x_6319_, 0);
lean_inc(v_a_6320_);
lean_dec_ref_known(v___x_6319_, 1);
if (lean_obj_tag(v_a_6320_) == 1)
{
lean_object* v_val_6321_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec(v_goal_6042_);
v_val_6321_ = lean_ctor_get(v_a_6320_, 0);
lean_inc(v_val_6321_);
lean_dec_ref_known(v_a_6320_, 1);
v_gs_6057_ = v_val_6321_;
goto v___jp_6056_;
}
else
{
lean_object* v___x_6322_; 
lean_dec(v_a_6320_);
lean_inc(v_a_6278_);
lean_inc(v_goal_6042_);
v___x_6322_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(v_goal_6042_, v_a_6278_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6322_) == 0)
{
lean_object* v_a_6323_; 
v_a_6323_ = lean_ctor_get(v___x_6322_, 0);
lean_inc(v_a_6323_);
lean_dec_ref_known(v___x_6322_, 1);
if (lean_obj_tag(v_a_6323_) == 1)
{
lean_object* v_val_6324_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec(v_goal_6042_);
v_val_6324_ = lean_ctor_get(v_a_6323_, 0);
lean_inc(v_val_6324_);
lean_dec_ref_known(v_a_6323_, 1);
v_g_6061_ = v_val_6324_;
goto v___jp_6060_;
}
else
{
lean_object* v___x_6325_; uint8_t v___x_6326_; 
lean_dec(v_a_6323_);
lean_inc(v_a_6278_);
v___x_6325_ = l_Lean_Expr_cleanupAnnotations(v_a_6278_);
v___x_6326_ = l_Lean_Expr_isApp(v___x_6325_);
if (v___x_6326_ == 0)
{
lean_dec_ref(v___x_6325_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
goto v___jp_6282_;
}
else
{
lean_object* v_arg_6327_; lean_object* v___x_6328_; uint8_t v___x_6329_; 
v_arg_6327_ = lean_ctor_get(v___x_6325_, 1);
lean_inc_ref(v_arg_6327_);
v___x_6328_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6325_);
v___x_6329_ = l_Lean_Expr_isApp(v___x_6328_);
if (v___x_6329_ == 0)
{
lean_dec_ref(v___x_6328_);
lean_dec_ref(v_arg_6327_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
goto v___jp_6282_;
}
else
{
lean_object* v_arg_6330_; lean_object* v___x_6331_; uint8_t v___x_6332_; 
v_arg_6330_ = lean_ctor_get(v___x_6328_, 1);
lean_inc_ref(v_arg_6330_);
v___x_6331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6328_);
v___x_6332_ = l_Lean_Expr_isApp(v___x_6331_);
if (v___x_6332_ == 0)
{
lean_dec_ref(v___x_6331_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
goto v___jp_6282_;
}
else
{
lean_object* v_arg_6333_; lean_object* v___x_6334_; uint8_t v___x_6335_; 
v_arg_6333_ = lean_ctor_get(v___x_6331_, 1);
lean_inc_ref(v_arg_6333_);
v___x_6334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6331_);
v___x_6335_ = l_Lean_Expr_isApp(v___x_6334_);
if (v___x_6335_ == 0)
{
lean_dec_ref(v___x_6334_);
lean_dec_ref(v_arg_6333_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
goto v___jp_6282_;
}
else
{
lean_object* v_arg_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; uint8_t v___x_6339_; 
v_arg_6336_ = lean_ctor_get(v___x_6334_, 1);
lean_inc_ref(v_arg_6336_);
v___x_6337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6334_);
v___x_6338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10));
v___x_6339_ = l_Lean_Expr_isConstOf(v___x_6337_, v___x_6338_);
lean_dec_ref(v___x_6337_);
if (v___x_6339_ == 0)
{
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6333_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
goto v___jp_6282_;
}
else
{
lean_object* v___x_6340_; 
lean_del_object(v___x_6280_);
lean_inc(v_goal_6042_);
v___x_6340_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(v_goal_6042_, v___y_6293_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6340_) == 0)
{
lean_object* v_a_6341_; 
v_a_6341_ = lean_ctor_get(v___x_6340_, 0);
lean_inc(v_a_6341_);
lean_dec_ref_known(v___x_6340_, 1);
if (lean_obj_tag(v_a_6341_) == 1)
{
lean_object* v_val_6342_; 
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6333_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_a_6278_);
lean_dec(v_goal_6042_);
v_val_6342_ = lean_ctor_get(v_a_6341_, 0);
lean_inc(v_val_6342_);
lean_dec_ref_known(v_a_6341_, 1);
v_gs_6057_ = v_val_6342_;
goto v___jp_6056_;
}
else
{
lean_object* v___x_6343_; 
lean_dec(v_a_6341_);
lean_inc(v_a_6278_);
lean_inc_ref(v_arg_6330_);
lean_inc(v_goal_6042_);
lean_inc_ref(v_scope_6043_);
v___x_6343_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(v_scope_6043_, v_goal_6042_, v_arg_6336_, v_arg_6330_, v_a_6278_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6343_) == 0)
{
lean_object* v_a_6344_; lean_object* v___x_6346_; uint8_t v_isShared_6347_; uint8_t v_isSharedCheck_6436_; 
v_a_6344_ = lean_ctor_get(v___x_6343_, 0);
v_isSharedCheck_6436_ = !lean_is_exclusive(v___x_6343_);
if (v_isSharedCheck_6436_ == 0)
{
v___x_6346_ = v___x_6343_;
v_isShared_6347_ = v_isSharedCheck_6436_;
goto v_resetjp_6345_;
}
else
{
lean_inc(v_a_6344_);
lean_dec(v___x_6343_);
v___x_6346_ = lean_box(0);
v_isShared_6347_ = v_isSharedCheck_6436_;
goto v_resetjp_6345_;
}
v_resetjp_6345_:
{
if (lean_obj_tag(v_a_6344_) == 1)
{
lean_object* v_val_6348_; lean_object* v_fst_6349_; lean_object* v_snd_6350_; lean_object* v___x_6352_; uint8_t v_isShared_6353_; uint8_t v_isSharedCheck_6360_; 
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6333_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_a_6278_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_val_6348_ = lean_ctor_get(v_a_6344_, 0);
lean_inc(v_val_6348_);
lean_dec_ref_known(v_a_6344_, 1);
v_fst_6349_ = lean_ctor_get(v_val_6348_, 0);
v_snd_6350_ = lean_ctor_get(v_val_6348_, 1);
v_isSharedCheck_6360_ = !lean_is_exclusive(v_val_6348_);
if (v_isSharedCheck_6360_ == 0)
{
v___x_6352_ = v_val_6348_;
v_isShared_6353_ = v_isSharedCheck_6360_;
goto v_resetjp_6351_;
}
else
{
lean_inc(v_snd_6350_);
lean_inc(v_fst_6349_);
lean_dec(v_val_6348_);
v___x_6352_ = lean_box(0);
v_isShared_6353_ = v_isSharedCheck_6360_;
goto v_resetjp_6351_;
}
v_resetjp_6351_:
{
lean_object* v___x_6355_; 
if (v_isShared_6353_ == 0)
{
v___x_6355_ = v___x_6352_;
goto v_reusejp_6354_;
}
else
{
lean_object* v_reuseFailAlloc_6359_; 
v_reuseFailAlloc_6359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6359_, 0, v_fst_6349_);
lean_ctor_set(v_reuseFailAlloc_6359_, 1, v_snd_6350_);
v___x_6355_ = v_reuseFailAlloc_6359_;
goto v_reusejp_6354_;
}
v_reusejp_6354_:
{
lean_object* v___x_6357_; 
if (v_isShared_6347_ == 0)
{
lean_ctor_set(v___x_6346_, 0, v___x_6355_);
v___x_6357_ = v___x_6346_;
goto v_reusejp_6356_;
}
else
{
lean_object* v_reuseFailAlloc_6358_; 
v_reuseFailAlloc_6358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6358_, 0, v___x_6355_);
v___x_6357_ = v_reuseFailAlloc_6358_;
goto v_reusejp_6356_;
}
v_reusejp_6356_:
{
return v___x_6357_;
}
}
}
}
else
{
lean_object* v___x_6361_; 
lean_del_object(v___x_6346_);
lean_dec(v_a_6344_);
lean_inc(v_goal_6042_);
v___x_6361_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(v_scope_6043_, v_goal_6042_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6361_) == 0)
{
lean_object* v_a_6362_; lean_object* v___x_6363_; 
v_a_6362_ = lean_ctor_get(v___x_6361_, 0);
lean_inc(v_a_6362_);
lean_dec_ref_known(v___x_6361_, 1);
lean_inc_ref(v_arg_6327_);
lean_inc_ref(v_arg_6330_);
lean_inc_ref(v_arg_6336_);
lean_inc(v_goal_6042_);
v___x_6363_ = l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f(v_goal_6042_, v_a_6278_, v_arg_6336_, v_arg_6333_, v_arg_6330_, v_arg_6327_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6363_) == 0)
{
lean_object* v_a_6364_; 
v_a_6364_ = lean_ctor_get(v___x_6363_, 0);
lean_inc(v_a_6364_);
lean_dec_ref_known(v___x_6363_, 1);
if (lean_obj_tag(v_a_6364_) == 1)
{
lean_object* v_val_6365_; 
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_goal_6042_);
v_val_6365_ = lean_ctor_get(v_a_6364_, 0);
lean_inc(v_val_6365_);
lean_dec_ref_known(v_a_6364_, 1);
v___y_6073_ = v_a_6362_;
v_g_6074_ = v_val_6365_;
goto v___jp_6072_;
}
else
{
lean_object* v___x_6366_; 
lean_dec(v_a_6364_);
lean_inc_ref(v_arg_6327_);
lean_inc(v_goal_6042_);
v___x_6366_ = l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(v_goal_6042_, v_arg_6327_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6366_) == 0)
{
lean_object* v_a_6367_; 
v_a_6367_ = lean_ctor_get(v___x_6366_, 0);
lean_inc(v_a_6367_);
lean_dec_ref_known(v___x_6366_, 1);
if (lean_obj_tag(v_a_6367_) == 1)
{
lean_object* v_val_6368_; 
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_goal_6042_);
v_val_6368_ = lean_ctor_get(v_a_6367_, 0);
lean_inc(v_val_6368_);
lean_dec_ref_known(v_a_6367_, 1);
v___y_6080_ = v_a_6362_;
v_gs_6081_ = v_val_6368_;
goto v___jp_6079_;
}
else
{
lean_object* v___x_6369_; 
lean_dec(v_a_6367_);
lean_inc(v_goal_6042_);
v___x_6369_ = l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(v_goal_6042_, v_arg_6327_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6369_) == 0)
{
lean_object* v_a_6370_; 
v_a_6370_ = lean_ctor_get(v___x_6369_, 0);
lean_inc(v_a_6370_);
lean_dec_ref_known(v___x_6369_, 1);
if (lean_obj_tag(v_a_6370_) == 1)
{
lean_object* v_val_6371_; 
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_goal_6042_);
v_val_6371_ = lean_ctor_get(v_a_6370_, 0);
lean_inc(v_val_6371_);
lean_dec_ref_known(v_a_6370_, 1);
v___y_6080_ = v_a_6362_;
v_gs_6081_ = v_val_6371_;
goto v___jp_6079_;
}
else
{
lean_object* v___x_6372_; 
lean_dec(v_a_6370_);
lean_inc_ref(v_arg_6327_);
lean_inc_ref(v_arg_6330_);
lean_inc(v_goal_6042_);
lean_inc(v_a_6362_);
v___x_6372_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f(v_a_6362_, v_goal_6042_, v_arg_6336_, v_arg_6330_, v_arg_6327_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
lean_dec_ref(v_arg_6336_);
if (lean_obj_tag(v___x_6372_) == 0)
{
lean_object* v_a_6373_; 
v_a_6373_ = lean_ctor_get(v___x_6372_, 0);
lean_inc(v_a_6373_);
lean_dec_ref_known(v___x_6372_, 1);
if (lean_obj_tag(v_a_6373_) == 1)
{
lean_object* v_val_6374_; 
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_goal_6042_);
v_val_6374_ = lean_ctor_get(v_a_6373_, 0);
lean_inc(v_val_6374_);
lean_dec_ref_known(v_a_6373_, 1);
v___y_6080_ = v_a_6362_;
v_gs_6081_ = v_val_6374_;
goto v___jp_6079_;
}
else
{
lean_object* v___x_6375_; 
lean_dec(v_a_6373_);
lean_inc_ref(v_arg_6327_);
v___x_6375_ = l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(v_arg_6327_);
if (lean_obj_tag(v___x_6375_) == 1)
{
lean_object* v_options_6376_; uint8_t v_hasTrace_6377_; 
v_options_6376_ = lean_ctor_get(v___y_6302_, 2);
v_hasTrace_6377_ = lean_ctor_get_uint8(v_options_6376_, sizeof(void*)*1);
if (v_hasTrace_6377_ == 0)
{
lean_object* v_val_6378_; 
v_val_6378_ = lean_ctor_get(v___x_6375_, 0);
lean_inc(v_val_6378_);
lean_dec_ref_known(v___x_6375_, 1);
v___y_6133_ = v_arg_6327_;
v___y_6134_ = v_val_6378_;
v___y_6135_ = v_arg_6330_;
v___y_6136_ = v_a_6362_;
v___y_6137_ = v___y_6293_;
v___y_6138_ = v___y_6294_;
v___y_6139_ = v___y_6295_;
v___y_6140_ = v___y_6296_;
v___y_6141_ = v___y_6297_;
v___y_6142_ = v___y_6298_;
v___y_6143_ = v___y_6299_;
v___y_6144_ = v___y_6300_;
v___y_6145_ = v___y_6301_;
v___y_6146_ = v___y_6302_;
v___y_6147_ = v___y_6303_;
goto v___jp_6132_;
}
else
{
lean_object* v_val_6379_; lean_object* v_inheritedTraceOptions_6380_; lean_object* v___x_6381_; uint8_t v___x_6382_; 
v_val_6379_ = lean_ctor_get(v___x_6375_, 0);
lean_inc(v_val_6379_);
lean_dec_ref_known(v___x_6375_, 1);
v_inheritedTraceOptions_6380_ = lean_ctor_get(v___y_6302_, 13);
v___x_6381_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_6382_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6380_, v_options_6376_, v___x_6381_);
if (v___x_6382_ == 0)
{
v___y_6133_ = v_arg_6327_;
v___y_6134_ = v_val_6379_;
v___y_6135_ = v_arg_6330_;
v___y_6136_ = v_a_6362_;
v___y_6137_ = v___y_6293_;
v___y_6138_ = v___y_6294_;
v___y_6139_ = v___y_6295_;
v___y_6140_ = v___y_6296_;
v___y_6141_ = v___y_6297_;
v___y_6142_ = v___y_6298_;
v___y_6143_ = v___y_6299_;
v___y_6144_ = v___y_6300_;
v___y_6145_ = v___y_6301_;
v___y_6146_ = v___y_6302_;
v___y_6147_ = v___y_6303_;
goto v___jp_6132_;
}
else
{
lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; 
v___x_6383_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5);
v___x_6384_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_val_6379_);
v___x_6385_ = l_Lean_MessageData_ofExpr(v___x_6384_);
v___x_6386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6386_, 0, v___x_6383_);
lean_ctor_set(v___x_6386_, 1, v___x_6385_);
v___x_6387_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_6291_, v___x_6386_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6387_) == 0)
{
lean_dec_ref_known(v___x_6387_, 1);
v___y_6133_ = v_arg_6327_;
v___y_6134_ = v_val_6379_;
v___y_6135_ = v_arg_6330_;
v___y_6136_ = v_a_6362_;
v___y_6137_ = v___y_6293_;
v___y_6138_ = v___y_6294_;
v___y_6139_ = v___y_6295_;
v___y_6140_ = v___y_6296_;
v___y_6141_ = v___y_6297_;
v___y_6142_ = v___y_6298_;
v___y_6143_ = v___y_6299_;
v___y_6144_ = v___y_6300_;
v___y_6145_ = v___y_6301_;
v___y_6146_ = v___y_6302_;
v___y_6147_ = v___y_6303_;
goto v___jp_6132_;
}
else
{
lean_object* v_a_6388_; lean_object* v___x_6390_; uint8_t v_isShared_6391_; uint8_t v_isSharedCheck_6395_; 
lean_dec(v_val_6379_);
lean_dec(v_a_6362_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_goal_6042_);
v_a_6388_ = lean_ctor_get(v___x_6387_, 0);
v_isSharedCheck_6395_ = !lean_is_exclusive(v___x_6387_);
if (v_isSharedCheck_6395_ == 0)
{
v___x_6390_ = v___x_6387_;
v_isShared_6391_ = v_isSharedCheck_6395_;
goto v_resetjp_6389_;
}
else
{
lean_inc(v_a_6388_);
lean_dec(v___x_6387_);
v___x_6390_ = lean_box(0);
v_isShared_6391_ = v_isSharedCheck_6395_;
goto v_resetjp_6389_;
}
v_resetjp_6389_:
{
lean_object* v___x_6393_; 
if (v_isShared_6391_ == 0)
{
v___x_6393_ = v___x_6390_;
goto v_reusejp_6392_;
}
else
{
lean_object* v_reuseFailAlloc_6394_; 
v_reuseFailAlloc_6394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6394_, 0, v_a_6388_);
v___x_6393_ = v_reuseFailAlloc_6394_;
goto v_reusejp_6392_;
}
v_reusejp_6392_:
{
return v___x_6393_;
}
}
}
}
}
}
else
{
lean_dec(v___x_6375_);
lean_dec(v_a_6362_);
lean_dec(v_goal_6042_);
v___y_6067_ = v_arg_6327_;
v___y_6068_ = v_arg_6330_;
goto v___jp_6066_;
}
}
}
else
{
lean_object* v_a_6396_; lean_object* v___x_6398_; uint8_t v_isShared_6399_; uint8_t v_isSharedCheck_6403_; 
lean_dec(v_a_6362_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_goal_6042_);
v_a_6396_ = lean_ctor_get(v___x_6372_, 0);
v_isSharedCheck_6403_ = !lean_is_exclusive(v___x_6372_);
if (v_isSharedCheck_6403_ == 0)
{
v___x_6398_ = v___x_6372_;
v_isShared_6399_ = v_isSharedCheck_6403_;
goto v_resetjp_6397_;
}
else
{
lean_inc(v_a_6396_);
lean_dec(v___x_6372_);
v___x_6398_ = lean_box(0);
v_isShared_6399_ = v_isSharedCheck_6403_;
goto v_resetjp_6397_;
}
v_resetjp_6397_:
{
lean_object* v___x_6401_; 
if (v_isShared_6399_ == 0)
{
v___x_6401_ = v___x_6398_;
goto v_reusejp_6400_;
}
else
{
lean_object* v_reuseFailAlloc_6402_; 
v_reuseFailAlloc_6402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6402_, 0, v_a_6396_);
v___x_6401_ = v_reuseFailAlloc_6402_;
goto v_reusejp_6400_;
}
v_reusejp_6400_:
{
return v___x_6401_;
}
}
}
}
}
else
{
lean_object* v_a_6404_; lean_object* v___x_6406_; uint8_t v_isShared_6407_; uint8_t v_isSharedCheck_6411_; 
lean_dec(v_a_6362_);
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_goal_6042_);
v_a_6404_ = lean_ctor_get(v___x_6369_, 0);
v_isSharedCheck_6411_ = !lean_is_exclusive(v___x_6369_);
if (v_isSharedCheck_6411_ == 0)
{
v___x_6406_ = v___x_6369_;
v_isShared_6407_ = v_isSharedCheck_6411_;
goto v_resetjp_6405_;
}
else
{
lean_inc(v_a_6404_);
lean_dec(v___x_6369_);
v___x_6406_ = lean_box(0);
v_isShared_6407_ = v_isSharedCheck_6411_;
goto v_resetjp_6405_;
}
v_resetjp_6405_:
{
lean_object* v___x_6409_; 
if (v_isShared_6407_ == 0)
{
v___x_6409_ = v___x_6406_;
goto v_reusejp_6408_;
}
else
{
lean_object* v_reuseFailAlloc_6410_; 
v_reuseFailAlloc_6410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6410_, 0, v_a_6404_);
v___x_6409_ = v_reuseFailAlloc_6410_;
goto v_reusejp_6408_;
}
v_reusejp_6408_:
{
return v___x_6409_;
}
}
}
}
}
else
{
lean_object* v_a_6412_; lean_object* v___x_6414_; uint8_t v_isShared_6415_; uint8_t v_isSharedCheck_6419_; 
lean_dec(v_a_6362_);
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_goal_6042_);
v_a_6412_ = lean_ctor_get(v___x_6366_, 0);
v_isSharedCheck_6419_ = !lean_is_exclusive(v___x_6366_);
if (v_isSharedCheck_6419_ == 0)
{
v___x_6414_ = v___x_6366_;
v_isShared_6415_ = v_isSharedCheck_6419_;
goto v_resetjp_6413_;
}
else
{
lean_inc(v_a_6412_);
lean_dec(v___x_6366_);
v___x_6414_ = lean_box(0);
v_isShared_6415_ = v_isSharedCheck_6419_;
goto v_resetjp_6413_;
}
v_resetjp_6413_:
{
lean_object* v___x_6417_; 
if (v_isShared_6415_ == 0)
{
v___x_6417_ = v___x_6414_;
goto v_reusejp_6416_;
}
else
{
lean_object* v_reuseFailAlloc_6418_; 
v_reuseFailAlloc_6418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6418_, 0, v_a_6412_);
v___x_6417_ = v_reuseFailAlloc_6418_;
goto v_reusejp_6416_;
}
v_reusejp_6416_:
{
return v___x_6417_;
}
}
}
}
}
else
{
lean_object* v_a_6420_; lean_object* v___x_6422_; uint8_t v_isShared_6423_; uint8_t v_isSharedCheck_6427_; 
lean_dec(v_a_6362_);
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_goal_6042_);
v_a_6420_ = lean_ctor_get(v___x_6363_, 0);
v_isSharedCheck_6427_ = !lean_is_exclusive(v___x_6363_);
if (v_isSharedCheck_6427_ == 0)
{
v___x_6422_ = v___x_6363_;
v_isShared_6423_ = v_isSharedCheck_6427_;
goto v_resetjp_6421_;
}
else
{
lean_inc(v_a_6420_);
lean_dec(v___x_6363_);
v___x_6422_ = lean_box(0);
v_isShared_6423_ = v_isSharedCheck_6427_;
goto v_resetjp_6421_;
}
v_resetjp_6421_:
{
lean_object* v___x_6425_; 
if (v_isShared_6423_ == 0)
{
v___x_6425_ = v___x_6422_;
goto v_reusejp_6424_;
}
else
{
lean_object* v_reuseFailAlloc_6426_; 
v_reuseFailAlloc_6426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6426_, 0, v_a_6420_);
v___x_6425_ = v_reuseFailAlloc_6426_;
goto v_reusejp_6424_;
}
v_reusejp_6424_:
{
return v___x_6425_;
}
}
}
}
else
{
lean_object* v_a_6428_; lean_object* v___x_6430_; uint8_t v_isShared_6431_; uint8_t v_isSharedCheck_6435_; 
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6333_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_a_6278_);
lean_dec(v_goal_6042_);
v_a_6428_ = lean_ctor_get(v___x_6361_, 0);
v_isSharedCheck_6435_ = !lean_is_exclusive(v___x_6361_);
if (v_isSharedCheck_6435_ == 0)
{
v___x_6430_ = v___x_6361_;
v_isShared_6431_ = v_isSharedCheck_6435_;
goto v_resetjp_6429_;
}
else
{
lean_inc(v_a_6428_);
lean_dec(v___x_6361_);
v___x_6430_ = lean_box(0);
v_isShared_6431_ = v_isSharedCheck_6435_;
goto v_resetjp_6429_;
}
v_resetjp_6429_:
{
lean_object* v___x_6433_; 
if (v_isShared_6431_ == 0)
{
v___x_6433_ = v___x_6430_;
goto v_reusejp_6432_;
}
else
{
lean_object* v_reuseFailAlloc_6434_; 
v_reuseFailAlloc_6434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6434_, 0, v_a_6428_);
v___x_6433_ = v_reuseFailAlloc_6434_;
goto v_reusejp_6432_;
}
v_reusejp_6432_:
{
return v___x_6433_;
}
}
}
}
}
}
else
{
lean_object* v_a_6437_; lean_object* v___x_6439_; uint8_t v_isShared_6440_; uint8_t v_isSharedCheck_6444_; 
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6333_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_a_6278_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6437_ = lean_ctor_get(v___x_6343_, 0);
v_isSharedCheck_6444_ = !lean_is_exclusive(v___x_6343_);
if (v_isSharedCheck_6444_ == 0)
{
v___x_6439_ = v___x_6343_;
v_isShared_6440_ = v_isSharedCheck_6444_;
goto v_resetjp_6438_;
}
else
{
lean_inc(v_a_6437_);
lean_dec(v___x_6343_);
v___x_6439_ = lean_box(0);
v_isShared_6440_ = v_isSharedCheck_6444_;
goto v_resetjp_6438_;
}
v_resetjp_6438_:
{
lean_object* v___x_6442_; 
if (v_isShared_6440_ == 0)
{
v___x_6442_ = v___x_6439_;
goto v_reusejp_6441_;
}
else
{
lean_object* v_reuseFailAlloc_6443_; 
v_reuseFailAlloc_6443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6443_, 0, v_a_6437_);
v___x_6442_ = v_reuseFailAlloc_6443_;
goto v_reusejp_6441_;
}
v_reusejp_6441_:
{
return v___x_6442_;
}
}
}
}
}
else
{
lean_object* v_a_6445_; lean_object* v___x_6447_; uint8_t v_isShared_6448_; uint8_t v_isSharedCheck_6452_; 
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6333_);
lean_dec_ref(v_arg_6330_);
lean_dec_ref(v_arg_6327_);
lean_dec(v_a_6278_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6445_ = lean_ctor_get(v___x_6340_, 0);
v_isSharedCheck_6452_ = !lean_is_exclusive(v___x_6340_);
if (v_isSharedCheck_6452_ == 0)
{
v___x_6447_ = v___x_6340_;
v_isShared_6448_ = v_isSharedCheck_6452_;
goto v_resetjp_6446_;
}
else
{
lean_inc(v_a_6445_);
lean_dec(v___x_6340_);
v___x_6447_ = lean_box(0);
v_isShared_6448_ = v_isSharedCheck_6452_;
goto v_resetjp_6446_;
}
v_resetjp_6446_:
{
lean_object* v___x_6450_; 
if (v_isShared_6448_ == 0)
{
v___x_6450_ = v___x_6447_;
goto v_reusejp_6449_;
}
else
{
lean_object* v_reuseFailAlloc_6451_; 
v_reuseFailAlloc_6451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6451_, 0, v_a_6445_);
v___x_6450_ = v_reuseFailAlloc_6451_;
goto v_reusejp_6449_;
}
v_reusejp_6449_:
{
return v___x_6450_;
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
lean_object* v_a_6453_; lean_object* v___x_6455_; uint8_t v_isShared_6456_; uint8_t v_isSharedCheck_6460_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6453_ = lean_ctor_get(v___x_6322_, 0);
v_isSharedCheck_6460_ = !lean_is_exclusive(v___x_6322_);
if (v_isSharedCheck_6460_ == 0)
{
v___x_6455_ = v___x_6322_;
v_isShared_6456_ = v_isSharedCheck_6460_;
goto v_resetjp_6454_;
}
else
{
lean_inc(v_a_6453_);
lean_dec(v___x_6322_);
v___x_6455_ = lean_box(0);
v_isShared_6456_ = v_isSharedCheck_6460_;
goto v_resetjp_6454_;
}
v_resetjp_6454_:
{
lean_object* v___x_6458_; 
if (v_isShared_6456_ == 0)
{
v___x_6458_ = v___x_6455_;
goto v_reusejp_6457_;
}
else
{
lean_object* v_reuseFailAlloc_6459_; 
v_reuseFailAlloc_6459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6459_, 0, v_a_6453_);
v___x_6458_ = v_reuseFailAlloc_6459_;
goto v_reusejp_6457_;
}
v_reusejp_6457_:
{
return v___x_6458_;
}
}
}
}
}
else
{
lean_object* v_a_6461_; lean_object* v___x_6463_; uint8_t v_isShared_6464_; uint8_t v_isSharedCheck_6468_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6461_ = lean_ctor_get(v___x_6319_, 0);
v_isSharedCheck_6468_ = !lean_is_exclusive(v___x_6319_);
if (v_isSharedCheck_6468_ == 0)
{
v___x_6463_ = v___x_6319_;
v_isShared_6464_ = v_isSharedCheck_6468_;
goto v_resetjp_6462_;
}
else
{
lean_inc(v_a_6461_);
lean_dec(v___x_6319_);
v___x_6463_ = lean_box(0);
v_isShared_6464_ = v_isSharedCheck_6468_;
goto v_resetjp_6462_;
}
v_resetjp_6462_:
{
lean_object* v___x_6466_; 
if (v_isShared_6464_ == 0)
{
v___x_6466_ = v___x_6463_;
goto v_reusejp_6465_;
}
else
{
lean_object* v_reuseFailAlloc_6467_; 
v_reuseFailAlloc_6467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6467_, 0, v_a_6461_);
v___x_6466_ = v_reuseFailAlloc_6467_;
goto v_reusejp_6465_;
}
v_reusejp_6465_:
{
return v___x_6466_;
}
}
}
}
}
else
{
lean_object* v_a_6469_; lean_object* v___x_6471_; uint8_t v_isShared_6472_; uint8_t v_isSharedCheck_6476_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6469_ = lean_ctor_get(v___x_6316_, 0);
v_isSharedCheck_6476_ = !lean_is_exclusive(v___x_6316_);
if (v_isSharedCheck_6476_ == 0)
{
v___x_6471_ = v___x_6316_;
v_isShared_6472_ = v_isSharedCheck_6476_;
goto v_resetjp_6470_;
}
else
{
lean_inc(v_a_6469_);
lean_dec(v___x_6316_);
v___x_6471_ = lean_box(0);
v_isShared_6472_ = v_isSharedCheck_6476_;
goto v_resetjp_6470_;
}
v_resetjp_6470_:
{
lean_object* v___x_6474_; 
if (v_isShared_6472_ == 0)
{
v___x_6474_ = v___x_6471_;
goto v_reusejp_6473_;
}
else
{
lean_object* v_reuseFailAlloc_6475_; 
v_reuseFailAlloc_6475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6475_, 0, v_a_6469_);
v___x_6474_ = v_reuseFailAlloc_6475_;
goto v_reusejp_6473_;
}
v_reusejp_6473_:
{
return v___x_6474_;
}
}
}
}
}
else
{
lean_object* v_a_6477_; lean_object* v___x_6479_; uint8_t v_isShared_6480_; uint8_t v_isSharedCheck_6484_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6477_ = lean_ctor_get(v___x_6313_, 0);
v_isSharedCheck_6484_ = !lean_is_exclusive(v___x_6313_);
if (v_isSharedCheck_6484_ == 0)
{
v___x_6479_ = v___x_6313_;
v_isShared_6480_ = v_isSharedCheck_6484_;
goto v_resetjp_6478_;
}
else
{
lean_inc(v_a_6477_);
lean_dec(v___x_6313_);
v___x_6479_ = lean_box(0);
v_isShared_6480_ = v_isSharedCheck_6484_;
goto v_resetjp_6478_;
}
v_resetjp_6478_:
{
lean_object* v___x_6482_; 
if (v_isShared_6480_ == 0)
{
v___x_6482_ = v___x_6479_;
goto v_reusejp_6481_;
}
else
{
lean_object* v_reuseFailAlloc_6483_; 
v_reuseFailAlloc_6483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6483_, 0, v_a_6477_);
v___x_6482_ = v_reuseFailAlloc_6483_;
goto v_reusejp_6481_;
}
v_reusejp_6481_:
{
return v___x_6482_;
}
}
}
}
}
else
{
lean_object* v_a_6485_; lean_object* v___x_6487_; uint8_t v_isShared_6488_; uint8_t v_isSharedCheck_6492_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6485_ = lean_ctor_get(v___x_6310_, 0);
v_isSharedCheck_6492_ = !lean_is_exclusive(v___x_6310_);
if (v_isSharedCheck_6492_ == 0)
{
v___x_6487_ = v___x_6310_;
v_isShared_6488_ = v_isSharedCheck_6492_;
goto v_resetjp_6486_;
}
else
{
lean_inc(v_a_6485_);
lean_dec(v___x_6310_);
v___x_6487_ = lean_box(0);
v_isShared_6488_ = v_isSharedCheck_6492_;
goto v_resetjp_6486_;
}
v_resetjp_6486_:
{
lean_object* v___x_6490_; 
if (v_isShared_6488_ == 0)
{
v___x_6490_ = v___x_6487_;
goto v_reusejp_6489_;
}
else
{
lean_object* v_reuseFailAlloc_6491_; 
v_reuseFailAlloc_6491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6491_, 0, v_a_6485_);
v___x_6490_ = v_reuseFailAlloc_6491_;
goto v_reusejp_6489_;
}
v_reusejp_6489_:
{
return v___x_6490_;
}
}
}
}
}
else
{
lean_object* v_a_6493_; lean_object* v___x_6495_; uint8_t v_isShared_6496_; uint8_t v_isSharedCheck_6500_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6493_ = lean_ctor_get(v___x_6307_, 0);
v_isSharedCheck_6500_ = !lean_is_exclusive(v___x_6307_);
if (v_isSharedCheck_6500_ == 0)
{
v___x_6495_ = v___x_6307_;
v_isShared_6496_ = v_isSharedCheck_6500_;
goto v_resetjp_6494_;
}
else
{
lean_inc(v_a_6493_);
lean_dec(v___x_6307_);
v___x_6495_ = lean_box(0);
v_isShared_6496_ = v_isSharedCheck_6500_;
goto v_resetjp_6494_;
}
v_resetjp_6494_:
{
lean_object* v___x_6498_; 
if (v_isShared_6496_ == 0)
{
v___x_6498_ = v___x_6495_;
goto v_reusejp_6497_;
}
else
{
lean_object* v_reuseFailAlloc_6499_; 
v_reuseFailAlloc_6499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6499_, 0, v_a_6493_);
v___x_6498_ = v_reuseFailAlloc_6499_;
goto v_reusejp_6497_;
}
v_reusejp_6497_:
{
return v___x_6498_;
}
}
}
}
}
else
{
lean_object* v_a_6501_; lean_object* v___x_6503_; uint8_t v_isShared_6504_; uint8_t v_isSharedCheck_6508_; 
lean_del_object(v___x_6280_);
lean_dec(v_a_6278_);
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6501_ = lean_ctor_get(v___x_6304_, 0);
v_isSharedCheck_6508_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6508_ == 0)
{
v___x_6503_ = v___x_6304_;
v_isShared_6504_ = v_isSharedCheck_6508_;
goto v_resetjp_6502_;
}
else
{
lean_inc(v_a_6501_);
lean_dec(v___x_6304_);
v___x_6503_ = lean_box(0);
v_isShared_6504_ = v_isSharedCheck_6508_;
goto v_resetjp_6502_;
}
v_resetjp_6502_:
{
lean_object* v___x_6506_; 
if (v_isShared_6504_ == 0)
{
v___x_6506_ = v___x_6503_;
goto v_reusejp_6505_;
}
else
{
lean_object* v_reuseFailAlloc_6507_; 
v_reuseFailAlloc_6507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6507_, 0, v_a_6501_);
v___x_6506_ = v_reuseFailAlloc_6507_;
goto v_reusejp_6505_;
}
v_reusejp_6505_:
{
return v___x_6506_;
}
}
}
}
}
}
else
{
lean_object* v_a_6524_; lean_object* v___x_6526_; uint8_t v_isShared_6527_; uint8_t v_isSharedCheck_6531_; 
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6524_ = lean_ctor_get(v___x_6277_, 0);
v_isSharedCheck_6531_ = !lean_is_exclusive(v___x_6277_);
if (v_isSharedCheck_6531_ == 0)
{
v___x_6526_ = v___x_6277_;
v_isShared_6527_ = v_isSharedCheck_6531_;
goto v_resetjp_6525_;
}
else
{
lean_inc(v_a_6524_);
lean_dec(v___x_6277_);
v___x_6526_ = lean_box(0);
v_isShared_6527_ = v_isSharedCheck_6531_;
goto v_resetjp_6525_;
}
v_resetjp_6525_:
{
lean_object* v___x_6529_; 
if (v_isShared_6527_ == 0)
{
v___x_6529_ = v___x_6526_;
goto v_reusejp_6528_;
}
else
{
lean_object* v_reuseFailAlloc_6530_; 
v_reuseFailAlloc_6530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6530_, 0, v_a_6524_);
v___x_6529_ = v_reuseFailAlloc_6530_;
goto v_reusejp_6528_;
}
v_reusejp_6528_:
{
return v___x_6529_;
}
}
}
}
else
{
lean_object* v___x_6532_; lean_object* v___x_6534_; 
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v___x_6532_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__8));
if (v_isShared_6275_ == 0)
{
lean_ctor_set(v___x_6274_, 0, v___x_6532_);
v___x_6534_ = v___x_6274_;
goto v_reusejp_6533_;
}
else
{
lean_object* v_reuseFailAlloc_6535_; 
v_reuseFailAlloc_6535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6535_, 0, v___x_6532_);
v___x_6534_ = v_reuseFailAlloc_6535_;
goto v_reusejp_6533_;
}
v_reusejp_6533_:
{
return v___x_6534_;
}
}
}
}
else
{
lean_object* v_a_6537_; lean_object* v___x_6539_; uint8_t v_isShared_6540_; uint8_t v_isSharedCheck_6544_; 
lean_dec_ref(v_scope_6043_);
lean_dec(v_goal_6042_);
v_a_6537_ = lean_ctor_get(v___x_6271_, 0);
v_isSharedCheck_6544_ = !lean_is_exclusive(v___x_6271_);
if (v_isSharedCheck_6544_ == 0)
{
v___x_6539_ = v___x_6271_;
v_isShared_6540_ = v_isSharedCheck_6544_;
goto v_resetjp_6538_;
}
else
{
lean_inc(v_a_6537_);
lean_dec(v___x_6271_);
v___x_6539_ = lean_box(0);
v_isShared_6540_ = v_isSharedCheck_6544_;
goto v_resetjp_6538_;
}
v_resetjp_6538_:
{
lean_object* v___x_6542_; 
if (v_isShared_6540_ == 0)
{
v___x_6542_ = v___x_6539_;
goto v_reusejp_6541_;
}
else
{
lean_object* v_reuseFailAlloc_6543_; 
v_reuseFailAlloc_6543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6543_, 0, v_a_6537_);
v___x_6542_ = v_reuseFailAlloc_6543_;
goto v_reusejp_6541_;
}
v_reusejp_6541_:
{
return v___x_6542_;
}
}
}
v___jp_6056_:
{
lean_object* v___x_6058_; lean_object* v___x_6059_; 
v___x_6058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6058_, 0, v_scope_6043_);
lean_ctor_set(v___x_6058_, 1, v_gs_6057_);
v___x_6059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6058_);
return v___x_6059_;
}
v___jp_6060_:
{
lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; 
v___x_6062_ = lean_box(0);
v___x_6063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6063_, 0, v_g_6061_);
lean_ctor_set(v___x_6063_, 1, v___x_6062_);
v___x_6064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6064_, 0, v_scope_6043_);
lean_ctor_set(v___x_6064_, 1, v___x_6063_);
v___x_6065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6064_);
return v___x_6065_;
}
v___jp_6066_:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; 
v___x_6069_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___y_6068_);
lean_ctor_set(v___x_6069_, 1, v___y_6067_);
v___x_6070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6069_);
v___x_6071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6070_);
return v___x_6071_;
}
v___jp_6072_:
{
lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; 
v___x_6075_ = lean_box(0);
v___x_6076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6076_, 0, v_g_6074_);
lean_ctor_set(v___x_6076_, 1, v___x_6075_);
v___x_6077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___y_6073_);
lean_ctor_set(v___x_6077_, 1, v___x_6076_);
v___x_6078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6077_);
return v___x_6078_;
}
v___jp_6079_:
{
lean_object* v___x_6082_; lean_object* v___x_6083_; 
v___x_6082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___y_6080_);
lean_ctor_set(v___x_6082_, 1, v_gs_6081_);
v___x_6083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6083_, 0, v___x_6082_);
return v___x_6083_;
}
v___jp_6084_:
{
lean_object* v___x_6088_; 
v___x_6088_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_6087_);
if (lean_obj_tag(v___x_6088_) == 0)
{
lean_object* v___x_6090_; uint8_t v_isShared_6091_; uint8_t v_isSharedCheck_6098_; 
v_isSharedCheck_6098_ = !lean_is_exclusive(v___x_6088_);
if (v_isSharedCheck_6098_ == 0)
{
lean_object* v_unused_6099_; 
v_unused_6099_ = lean_ctor_get(v___x_6088_, 0);
lean_dec(v_unused_6099_);
v___x_6090_ = v___x_6088_;
v_isShared_6091_ = v_isSharedCheck_6098_;
goto v_resetjp_6089_;
}
else
{
lean_dec(v___x_6088_);
v___x_6090_ = lean_box(0);
v_isShared_6091_ = v_isSharedCheck_6098_;
goto v_resetjp_6089_;
}
v_resetjp_6089_:
{
lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6096_; 
v___x_6092_ = lean_box(0);
v___x_6093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6093_, 0, v_g_6086_);
lean_ctor_set(v___x_6093_, 1, v___x_6092_);
v___x_6094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___y_6085_);
lean_ctor_set(v___x_6094_, 1, v___x_6093_);
if (v_isShared_6091_ == 0)
{
lean_ctor_set(v___x_6090_, 0, v___x_6094_);
v___x_6096_ = v___x_6090_;
goto v_reusejp_6095_;
}
else
{
lean_object* v_reuseFailAlloc_6097_; 
v_reuseFailAlloc_6097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6097_, 0, v___x_6094_);
v___x_6096_ = v_reuseFailAlloc_6097_;
goto v_reusejp_6095_;
}
v_reusejp_6095_:
{
return v___x_6096_;
}
}
}
else
{
lean_object* v_a_6100_; lean_object* v___x_6102_; uint8_t v_isShared_6103_; uint8_t v_isSharedCheck_6107_; 
lean_dec(v_g_6086_);
lean_dec_ref(v___y_6085_);
v_a_6100_ = lean_ctor_get(v___x_6088_, 0);
v_isSharedCheck_6107_ = !lean_is_exclusive(v___x_6088_);
if (v_isSharedCheck_6107_ == 0)
{
v___x_6102_ = v___x_6088_;
v_isShared_6103_ = v_isSharedCheck_6107_;
goto v_resetjp_6101_;
}
else
{
lean_inc(v_a_6100_);
lean_dec(v___x_6088_);
v___x_6102_ = lean_box(0);
v_isShared_6103_ = v_isSharedCheck_6107_;
goto v_resetjp_6101_;
}
v_resetjp_6101_:
{
lean_object* v___x_6105_; 
if (v_isShared_6103_ == 0)
{
v___x_6105_ = v___x_6102_;
goto v_reusejp_6104_;
}
else
{
lean_object* v_reuseFailAlloc_6106_; 
v_reuseFailAlloc_6106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6106_, 0, v_a_6100_);
v___x_6105_ = v_reuseFailAlloc_6106_;
goto v_reusejp_6104_;
}
v_reusejp_6104_:
{
return v___x_6105_;
}
}
}
}
v___jp_6108_:
{
lean_object* v___x_6122_; 
v___x_6122_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_6115_);
if (lean_obj_tag(v___x_6122_) == 0)
{
lean_object* v___x_6123_; 
lean_dec_ref_known(v___x_6122_, 1);
v___x_6123_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(v___y_6120_, v_goal_6042_, v___y_6111_, v___y_6109_, v___y_6115_, v___y_6116_, v___y_6110_, v___y_6117_, v___y_6119_, v___y_6112_, v___y_6113_, v___y_6121_, v___y_6114_, v___y_6118_);
return v___x_6123_;
}
else
{
lean_object* v_a_6124_; lean_object* v___x_6126_; uint8_t v_isShared_6127_; uint8_t v_isSharedCheck_6131_; 
lean_dec_ref(v___y_6120_);
lean_dec_ref(v___y_6111_);
lean_dec(v_goal_6042_);
v_a_6124_ = lean_ctor_get(v___x_6122_, 0);
v_isSharedCheck_6131_ = !lean_is_exclusive(v___x_6122_);
if (v_isSharedCheck_6131_ == 0)
{
v___x_6126_ = v___x_6122_;
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
else
{
lean_inc(v_a_6124_);
lean_dec(v___x_6122_);
v___x_6126_ = lean_box(0);
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
v_resetjp_6125_:
{
lean_object* v___x_6129_; 
if (v_isShared_6127_ == 0)
{
v___x_6129_ = v___x_6126_;
goto v_reusejp_6128_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_a_6124_);
v___x_6129_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6128_;
}
v_reusejp_6128_:
{
return v___x_6129_;
}
}
}
}
v___jp_6132_:
{
lean_object* v___x_6148_; lean_object* v___x_6149_; 
lean_dec_ref(v___y_6135_);
lean_dec_ref(v___y_6133_);
v___x_6148_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v___y_6134_);
lean_inc_ref(v___x_6148_);
v___x_6149_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v___x_6148_, v___y_6137_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
if (lean_obj_tag(v___x_6149_) == 0)
{
lean_object* v_a_6150_; lean_object* v___x_6152_; uint8_t v_isShared_6153_; uint8_t v_isSharedCheck_6262_; 
v_a_6150_ = lean_ctor_get(v___x_6149_, 0);
v_isSharedCheck_6262_ = !lean_is_exclusive(v___x_6149_);
if (v_isSharedCheck_6262_ == 0)
{
v___x_6152_ = v___x_6149_;
v_isShared_6153_ = v_isSharedCheck_6262_;
goto v_resetjp_6151_;
}
else
{
lean_inc(v_a_6150_);
lean_dec(v___x_6149_);
v___x_6152_ = lean_box(0);
v_isShared_6153_ = v_isSharedCheck_6262_;
goto v_resetjp_6151_;
}
v_resetjp_6151_:
{
uint8_t v___x_6154_; 
v___x_6154_ = lean_unbox(v_a_6150_);
lean_dec(v_a_6150_);
if (v___x_6154_ == 0)
{
lean_object* v___x_6155_; 
lean_del_object(v___x_6152_);
lean_inc_ref(v___y_6134_);
lean_inc(v_goal_6042_);
v___x_6155_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(v_goal_6042_, v___y_6134_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
if (lean_obj_tag(v___x_6155_) == 0)
{
lean_object* v_a_6156_; 
v_a_6156_ = lean_ctor_get(v___x_6155_, 0);
lean_inc(v_a_6156_);
lean_dec_ref_known(v___x_6155_, 1);
if (lean_obj_tag(v_a_6156_) == 1)
{
lean_object* v_val_6157_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_val_6157_ = lean_ctor_get(v_a_6156_, 0);
lean_inc(v_val_6157_);
lean_dec_ref_known(v_a_6156_, 1);
v___y_6073_ = v___y_6136_;
v_g_6074_ = v_val_6157_;
goto v___jp_6072_;
}
else
{
lean_object* v___x_6158_; 
lean_dec(v_a_6156_);
lean_inc_ref(v___y_6134_);
lean_inc(v_goal_6042_);
v___x_6158_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(v_goal_6042_, v___y_6134_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
if (lean_obj_tag(v___x_6158_) == 0)
{
lean_object* v_a_6159_; 
v_a_6159_ = lean_ctor_get(v___x_6158_, 0);
lean_inc(v_a_6159_);
lean_dec_ref_known(v___x_6158_, 1);
if (lean_obj_tag(v_a_6159_) == 1)
{
lean_object* v_val_6160_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_val_6160_ = lean_ctor_get(v_a_6159_, 0);
lean_inc(v_val_6160_);
lean_dec_ref_known(v_a_6159_, 1);
v___y_6085_ = v___y_6136_;
v_g_6086_ = v_val_6160_;
v___y_6087_ = v___y_6138_;
goto v___jp_6084_;
}
else
{
lean_object* v___x_6161_; 
lean_dec(v_a_6159_);
lean_inc_ref(v___y_6134_);
lean_inc(v_goal_6042_);
v___x_6161_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(v_goal_6042_, v___y_6134_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
if (lean_obj_tag(v___x_6161_) == 0)
{
lean_object* v_a_6162_; 
v_a_6162_ = lean_ctor_get(v___x_6161_, 0);
lean_inc(v_a_6162_);
lean_dec_ref_known(v___x_6161_, 1);
if (lean_obj_tag(v_a_6162_) == 1)
{
lean_object* v_val_6163_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_val_6163_ = lean_ctor_get(v_a_6162_, 0);
lean_inc(v_val_6163_);
lean_dec_ref_known(v_a_6162_, 1);
v___y_6080_ = v___y_6136_;
v_gs_6081_ = v_val_6163_;
goto v___jp_6079_;
}
else
{
lean_object* v___x_6164_; 
lean_dec(v_a_6162_);
lean_inc_ref(v___y_6134_);
lean_inc(v_goal_6042_);
v___x_6164_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(v_goal_6042_, v___y_6134_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
if (lean_obj_tag(v___x_6164_) == 0)
{
lean_object* v_a_6165_; 
v_a_6165_ = lean_ctor_get(v___x_6164_, 0);
lean_inc(v_a_6165_);
lean_dec_ref_known(v___x_6164_, 1);
if (lean_obj_tag(v_a_6165_) == 1)
{
lean_object* v_val_6166_; lean_object* v___x_6167_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_val_6166_ = lean_ctor_get(v_a_6165_, 0);
lean_inc(v_val_6166_);
lean_dec_ref_known(v_a_6165_, 1);
v___x_6167_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_6138_);
if (lean_obj_tag(v___x_6167_) == 0)
{
lean_object* v___x_6169_; uint8_t v_isShared_6170_; uint8_t v_isSharedCheck_6175_; 
v_isSharedCheck_6175_ = !lean_is_exclusive(v___x_6167_);
if (v_isSharedCheck_6175_ == 0)
{
lean_object* v_unused_6176_; 
v_unused_6176_ = lean_ctor_get(v___x_6167_, 0);
lean_dec(v_unused_6176_);
v___x_6169_ = v___x_6167_;
v_isShared_6170_ = v_isSharedCheck_6175_;
goto v_resetjp_6168_;
}
else
{
lean_dec(v___x_6167_);
v___x_6169_ = lean_box(0);
v_isShared_6170_ = v_isSharedCheck_6175_;
goto v_resetjp_6168_;
}
v_resetjp_6168_:
{
lean_object* v___x_6171_; lean_object* v___x_6173_; 
v___x_6171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6171_, 0, v___y_6136_);
lean_ctor_set(v___x_6171_, 1, v_val_6166_);
if (v_isShared_6170_ == 0)
{
lean_ctor_set(v___x_6169_, 0, v___x_6171_);
v___x_6173_ = v___x_6169_;
goto v_reusejp_6172_;
}
else
{
lean_object* v_reuseFailAlloc_6174_; 
v_reuseFailAlloc_6174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6174_, 0, v___x_6171_);
v___x_6173_ = v_reuseFailAlloc_6174_;
goto v_reusejp_6172_;
}
v_reusejp_6172_:
{
return v___x_6173_;
}
}
}
else
{
lean_object* v_a_6177_; lean_object* v___x_6179_; uint8_t v_isShared_6180_; uint8_t v_isSharedCheck_6184_; 
lean_dec(v_val_6166_);
lean_dec_ref(v___y_6136_);
v_a_6177_ = lean_ctor_get(v___x_6167_, 0);
v_isSharedCheck_6184_ = !lean_is_exclusive(v___x_6167_);
if (v_isSharedCheck_6184_ == 0)
{
v___x_6179_ = v___x_6167_;
v_isShared_6180_ = v_isSharedCheck_6184_;
goto v_resetjp_6178_;
}
else
{
lean_inc(v_a_6177_);
lean_dec(v___x_6167_);
v___x_6179_ = lean_box(0);
v_isShared_6180_ = v_isSharedCheck_6184_;
goto v_resetjp_6178_;
}
v_resetjp_6178_:
{
lean_object* v___x_6182_; 
if (v_isShared_6180_ == 0)
{
v___x_6182_ = v___x_6179_;
goto v_reusejp_6181_;
}
else
{
lean_object* v_reuseFailAlloc_6183_; 
v_reuseFailAlloc_6183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6183_, 0, v_a_6177_);
v___x_6182_ = v_reuseFailAlloc_6183_;
goto v_reusejp_6181_;
}
v_reusejp_6181_:
{
return v___x_6182_;
}
}
}
}
else
{
lean_object* v___x_6185_; 
lean_dec(v_a_6165_);
lean_inc_ref(v___y_6134_);
lean_inc(v_goal_6042_);
v___x_6185_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(v_goal_6042_, v___y_6134_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
if (lean_obj_tag(v___x_6185_) == 0)
{
lean_object* v_a_6186_; 
v_a_6186_ = lean_ctor_get(v___x_6185_, 0);
lean_inc(v_a_6186_);
lean_dec_ref_known(v___x_6185_, 1);
if (lean_obj_tag(v_a_6186_) == 1)
{
lean_object* v_val_6187_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_val_6187_ = lean_ctor_get(v_a_6186_, 0);
lean_inc(v_val_6187_);
lean_dec_ref_known(v_a_6186_, 1);
v___y_6085_ = v___y_6136_;
v_g_6086_ = v_val_6187_;
v___y_6087_ = v___y_6138_;
goto v___jp_6084_;
}
else
{
lean_object* v___x_6188_; 
lean_dec(v_a_6186_);
lean_inc_ref(v___y_6134_);
lean_inc(v_goal_6042_);
v___x_6188_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f(v_goal_6042_, v___y_6134_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
if (lean_obj_tag(v___x_6188_) == 0)
{
lean_object* v_a_6189_; 
v_a_6189_ = lean_ctor_get(v___x_6188_, 0);
lean_inc(v_a_6189_);
lean_dec_ref_known(v___x_6188_, 1);
if (lean_obj_tag(v_a_6189_) == 1)
{
lean_object* v_val_6190_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_val_6190_ = lean_ctor_get(v_a_6189_, 0);
lean_inc(v_val_6190_);
lean_dec_ref_known(v_a_6189_, 1);
v___y_6085_ = v___y_6136_;
v_g_6086_ = v_val_6190_;
v___y_6087_ = v___y_6138_;
goto v___jp_6084_;
}
else
{
lean_object* v___x_6191_; uint8_t v___x_6192_; 
lean_dec(v_a_6189_);
v___x_6191_ = l_Lean_Expr_getAppFn(v___x_6148_);
v___x_6192_ = l_Lean_Expr_isConst(v___x_6191_);
if (v___x_6192_ == 0)
{
uint8_t v___x_6193_; 
v___x_6193_ = l_Lean_Expr_isFVar(v___x_6191_);
lean_dec_ref(v___x_6191_);
if (v___x_6193_ == 0)
{
lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v_a_6200_; lean_object* v___x_6202_; uint8_t v_isShared_6203_; uint8_t v_isSharedCheck_6207_; 
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v___x_6194_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1);
v___x_6195_ = l_Lean_MessageData_ofExpr(v___x_6148_);
v___x_6196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6196_, 0, v___x_6194_);
lean_ctor_set(v___x_6196_, 1, v___x_6195_);
v___x_6197_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3);
v___x_6198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6196_);
lean_ctor_set(v___x_6198_, 1, v___x_6197_);
v___x_6199_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_6198_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
v_a_6200_ = lean_ctor_get(v___x_6199_, 0);
v_isSharedCheck_6207_ = !lean_is_exclusive(v___x_6199_);
if (v_isSharedCheck_6207_ == 0)
{
v___x_6202_ = v___x_6199_;
v_isShared_6203_ = v_isSharedCheck_6207_;
goto v_resetjp_6201_;
}
else
{
lean_inc(v_a_6200_);
lean_dec(v___x_6199_);
v___x_6202_ = lean_box(0);
v_isShared_6203_ = v_isSharedCheck_6207_;
goto v_resetjp_6201_;
}
v_resetjp_6201_:
{
lean_object* v___x_6205_; 
if (v_isShared_6203_ == 0)
{
v___x_6205_ = v___x_6202_;
goto v_reusejp_6204_;
}
else
{
lean_object* v_reuseFailAlloc_6206_; 
v_reuseFailAlloc_6206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6206_, 0, v_a_6200_);
v___x_6205_ = v_reuseFailAlloc_6206_;
goto v_reusejp_6204_;
}
v_reusejp_6204_:
{
return v___x_6205_;
}
}
}
else
{
lean_dec_ref(v___x_6148_);
v___y_6109_ = v___y_6137_;
v___y_6110_ = v___y_6140_;
v___y_6111_ = v___y_6134_;
v___y_6112_ = v___y_6143_;
v___y_6113_ = v___y_6144_;
v___y_6114_ = v___y_6146_;
v___y_6115_ = v___y_6138_;
v___y_6116_ = v___y_6139_;
v___y_6117_ = v___y_6141_;
v___y_6118_ = v___y_6147_;
v___y_6119_ = v___y_6142_;
v___y_6120_ = v___y_6136_;
v___y_6121_ = v___y_6145_;
goto v___jp_6108_;
}
}
else
{
lean_dec_ref(v___x_6191_);
lean_dec_ref(v___x_6148_);
v___y_6109_ = v___y_6137_;
v___y_6110_ = v___y_6140_;
v___y_6111_ = v___y_6134_;
v___y_6112_ = v___y_6143_;
v___y_6113_ = v___y_6144_;
v___y_6114_ = v___y_6146_;
v___y_6115_ = v___y_6138_;
v___y_6116_ = v___y_6139_;
v___y_6117_ = v___y_6141_;
v___y_6118_ = v___y_6147_;
v___y_6119_ = v___y_6142_;
v___y_6120_ = v___y_6136_;
v___y_6121_ = v___y_6145_;
goto v___jp_6108_;
}
}
}
else
{
lean_object* v_a_6208_; lean_object* v___x_6210_; uint8_t v_isShared_6211_; uint8_t v_isSharedCheck_6215_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_a_6208_ = lean_ctor_get(v___x_6188_, 0);
v_isSharedCheck_6215_ = !lean_is_exclusive(v___x_6188_);
if (v_isSharedCheck_6215_ == 0)
{
v___x_6210_ = v___x_6188_;
v_isShared_6211_ = v_isSharedCheck_6215_;
goto v_resetjp_6209_;
}
else
{
lean_inc(v_a_6208_);
lean_dec(v___x_6188_);
v___x_6210_ = lean_box(0);
v_isShared_6211_ = v_isSharedCheck_6215_;
goto v_resetjp_6209_;
}
v_resetjp_6209_:
{
lean_object* v___x_6213_; 
if (v_isShared_6211_ == 0)
{
v___x_6213_ = v___x_6210_;
goto v_reusejp_6212_;
}
else
{
lean_object* v_reuseFailAlloc_6214_; 
v_reuseFailAlloc_6214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6214_, 0, v_a_6208_);
v___x_6213_ = v_reuseFailAlloc_6214_;
goto v_reusejp_6212_;
}
v_reusejp_6212_:
{
return v___x_6213_;
}
}
}
}
}
else
{
lean_object* v_a_6216_; lean_object* v___x_6218_; uint8_t v_isShared_6219_; uint8_t v_isSharedCheck_6223_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_a_6216_ = lean_ctor_get(v___x_6185_, 0);
v_isSharedCheck_6223_ = !lean_is_exclusive(v___x_6185_);
if (v_isSharedCheck_6223_ == 0)
{
v___x_6218_ = v___x_6185_;
v_isShared_6219_ = v_isSharedCheck_6223_;
goto v_resetjp_6217_;
}
else
{
lean_inc(v_a_6216_);
lean_dec(v___x_6185_);
v___x_6218_ = lean_box(0);
v_isShared_6219_ = v_isSharedCheck_6223_;
goto v_resetjp_6217_;
}
v_resetjp_6217_:
{
lean_object* v___x_6221_; 
if (v_isShared_6219_ == 0)
{
v___x_6221_ = v___x_6218_;
goto v_reusejp_6220_;
}
else
{
lean_object* v_reuseFailAlloc_6222_; 
v_reuseFailAlloc_6222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6222_, 0, v_a_6216_);
v___x_6221_ = v_reuseFailAlloc_6222_;
goto v_reusejp_6220_;
}
v_reusejp_6220_:
{
return v___x_6221_;
}
}
}
}
}
else
{
lean_object* v_a_6224_; lean_object* v___x_6226_; uint8_t v_isShared_6227_; uint8_t v_isSharedCheck_6231_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_a_6224_ = lean_ctor_get(v___x_6164_, 0);
v_isSharedCheck_6231_ = !lean_is_exclusive(v___x_6164_);
if (v_isSharedCheck_6231_ == 0)
{
v___x_6226_ = v___x_6164_;
v_isShared_6227_ = v_isSharedCheck_6231_;
goto v_resetjp_6225_;
}
else
{
lean_inc(v_a_6224_);
lean_dec(v___x_6164_);
v___x_6226_ = lean_box(0);
v_isShared_6227_ = v_isSharedCheck_6231_;
goto v_resetjp_6225_;
}
v_resetjp_6225_:
{
lean_object* v___x_6229_; 
if (v_isShared_6227_ == 0)
{
v___x_6229_ = v___x_6226_;
goto v_reusejp_6228_;
}
else
{
lean_object* v_reuseFailAlloc_6230_; 
v_reuseFailAlloc_6230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6230_, 0, v_a_6224_);
v___x_6229_ = v_reuseFailAlloc_6230_;
goto v_reusejp_6228_;
}
v_reusejp_6228_:
{
return v___x_6229_;
}
}
}
}
}
else
{
lean_object* v_a_6232_; lean_object* v___x_6234_; uint8_t v_isShared_6235_; uint8_t v_isSharedCheck_6239_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_a_6232_ = lean_ctor_get(v___x_6161_, 0);
v_isSharedCheck_6239_ = !lean_is_exclusive(v___x_6161_);
if (v_isSharedCheck_6239_ == 0)
{
v___x_6234_ = v___x_6161_;
v_isShared_6235_ = v_isSharedCheck_6239_;
goto v_resetjp_6233_;
}
else
{
lean_inc(v_a_6232_);
lean_dec(v___x_6161_);
v___x_6234_ = lean_box(0);
v_isShared_6235_ = v_isSharedCheck_6239_;
goto v_resetjp_6233_;
}
v_resetjp_6233_:
{
lean_object* v___x_6237_; 
if (v_isShared_6235_ == 0)
{
v___x_6237_ = v___x_6234_;
goto v_reusejp_6236_;
}
else
{
lean_object* v_reuseFailAlloc_6238_; 
v_reuseFailAlloc_6238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6232_);
v___x_6237_ = v_reuseFailAlloc_6238_;
goto v_reusejp_6236_;
}
v_reusejp_6236_:
{
return v___x_6237_;
}
}
}
}
}
else
{
lean_object* v_a_6240_; lean_object* v___x_6242_; uint8_t v_isShared_6243_; uint8_t v_isSharedCheck_6247_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_a_6240_ = lean_ctor_get(v___x_6158_, 0);
v_isSharedCheck_6247_ = !lean_is_exclusive(v___x_6158_);
if (v_isSharedCheck_6247_ == 0)
{
v___x_6242_ = v___x_6158_;
v_isShared_6243_ = v_isSharedCheck_6247_;
goto v_resetjp_6241_;
}
else
{
lean_inc(v_a_6240_);
lean_dec(v___x_6158_);
v___x_6242_ = lean_box(0);
v_isShared_6243_ = v_isSharedCheck_6247_;
goto v_resetjp_6241_;
}
v_resetjp_6241_:
{
lean_object* v___x_6245_; 
if (v_isShared_6243_ == 0)
{
v___x_6245_ = v___x_6242_;
goto v_reusejp_6244_;
}
else
{
lean_object* v_reuseFailAlloc_6246_; 
v_reuseFailAlloc_6246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6246_, 0, v_a_6240_);
v___x_6245_ = v_reuseFailAlloc_6246_;
goto v_reusejp_6244_;
}
v_reusejp_6244_:
{
return v___x_6245_;
}
}
}
}
}
else
{
lean_object* v_a_6248_; lean_object* v___x_6250_; uint8_t v_isShared_6251_; uint8_t v_isSharedCheck_6255_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_a_6248_ = lean_ctor_get(v___x_6155_, 0);
v_isSharedCheck_6255_ = !lean_is_exclusive(v___x_6155_);
if (v_isSharedCheck_6255_ == 0)
{
v___x_6250_ = v___x_6155_;
v_isShared_6251_ = v_isSharedCheck_6255_;
goto v_resetjp_6249_;
}
else
{
lean_inc(v_a_6248_);
lean_dec(v___x_6155_);
v___x_6250_ = lean_box(0);
v_isShared_6251_ = v_isSharedCheck_6255_;
goto v_resetjp_6249_;
}
v_resetjp_6249_:
{
lean_object* v___x_6253_; 
if (v_isShared_6251_ == 0)
{
v___x_6253_ = v___x_6250_;
goto v_reusejp_6252_;
}
else
{
lean_object* v_reuseFailAlloc_6254_; 
v_reuseFailAlloc_6254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6254_, 0, v_a_6248_);
v___x_6253_ = v_reuseFailAlloc_6254_;
goto v_reusejp_6252_;
}
v_reusejp_6252_:
{
return v___x_6253_;
}
}
}
}
else
{
lean_object* v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___x_6260_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6136_);
lean_dec(v_goal_6042_);
v___x_6256_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v___y_6134_);
lean_dec_ref(v___y_6134_);
v___x_6257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6257_, 0, v___x_6256_);
v___x_6258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6258_, 0, v___x_6257_);
if (v_isShared_6153_ == 0)
{
lean_ctor_set(v___x_6152_, 0, v___x_6258_);
v___x_6260_ = v___x_6152_;
goto v_reusejp_6259_;
}
else
{
lean_object* v_reuseFailAlloc_6261_; 
v_reuseFailAlloc_6261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6261_, 0, v___x_6258_);
v___x_6260_ = v_reuseFailAlloc_6261_;
goto v_reusejp_6259_;
}
v_reusejp_6259_:
{
return v___x_6260_;
}
}
}
}
else
{
lean_object* v_a_6263_; lean_object* v___x_6265_; uint8_t v_isShared_6266_; uint8_t v_isSharedCheck_6270_; 
lean_dec_ref(v___x_6148_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6134_);
lean_dec(v_goal_6042_);
v_a_6263_ = lean_ctor_get(v___x_6149_, 0);
v_isSharedCheck_6270_ = !lean_is_exclusive(v___x_6149_);
if (v_isSharedCheck_6270_ == 0)
{
v___x_6265_ = v___x_6149_;
v_isShared_6266_ = v_isSharedCheck_6270_;
goto v_resetjp_6264_;
}
else
{
lean_inc(v_a_6263_);
lean_dec(v___x_6149_);
v___x_6265_ = lean_box(0);
v_isShared_6266_ = v_isSharedCheck_6270_;
goto v_resetjp_6264_;
}
v_resetjp_6264_:
{
lean_object* v___x_6268_; 
if (v_isShared_6266_ == 0)
{
v___x_6268_ = v___x_6265_;
goto v_reusejp_6267_;
}
else
{
lean_object* v_reuseFailAlloc_6269_; 
v_reuseFailAlloc_6269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6269_, 0, v_a_6263_);
v___x_6268_ = v_reuseFailAlloc_6269_;
goto v_reusejp_6267_;
}
v_reusejp_6267_:
{
return v___x_6268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___boxed(lean_object* v_goal_6545_, lean_object* v_scope_6546_, lean_object* v___y_6547_, lean_object* v___y_6548_, lean_object* v___y_6549_, lean_object* v___y_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_){
_start:
{
lean_object* v_res_6559_; 
v_res_6559_ = l_Lean_Elab_Tactic_VCGen_solve___lam__0(v_goal_6545_, v_scope_6546_, v___y_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_);
lean_dec(v___y_6557_);
lean_dec_ref(v___y_6556_);
lean_dec(v___y_6555_);
lean_dec_ref(v___y_6554_);
lean_dec(v___y_6553_);
lean_dec_ref(v___y_6552_);
lean_dec(v___y_6551_);
lean_dec_ref(v___y_6550_);
lean_dec(v___y_6549_);
lean_dec(v___y_6548_);
lean_dec_ref(v___y_6547_);
return v_res_6559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve(lean_object* v_scope_6560_, lean_object* v_goal_6561_, lean_object* v_a_6562_, lean_object* v_a_6563_, lean_object* v_a_6564_, lean_object* v_a_6565_, lean_object* v_a_6566_, lean_object* v_a_6567_, lean_object* v_a_6568_, lean_object* v_a_6569_, lean_object* v_a_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_){
_start:
{
lean_object* v___f_6574_; lean_object* v___x_6575_; 
lean_inc(v_goal_6561_);
v___f_6574_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___boxed), 14, 2);
lean_closure_set(v___f_6574_, 0, v_goal_6561_);
lean_closure_set(v___f_6574_, 1, v_scope_6560_);
v___x_6575_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_6561_, v___f_6574_, v_a_6562_, v_a_6563_, v_a_6564_, v_a_6565_, v_a_6566_, v_a_6567_, v_a_6568_, v_a_6569_, v_a_6570_, v_a_6571_, v_a_6572_);
return v___x_6575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___boxed(lean_object* v_scope_6576_, lean_object* v_goal_6577_, lean_object* v_a_6578_, lean_object* v_a_6579_, lean_object* v_a_6580_, lean_object* v_a_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_, lean_object* v_a_6584_, lean_object* v_a_6585_, lean_object* v_a_6586_, lean_object* v_a_6587_, lean_object* v_a_6588_, lean_object* v_a_6589_){
_start:
{
lean_object* v_res_6590_; 
v_res_6590_ = l_Lean_Elab_Tactic_VCGen_solve(v_scope_6576_, v_goal_6577_, v_a_6578_, v_a_6579_, v_a_6580_, v_a_6581_, v_a_6582_, v_a_6583_, v_a_6584_, v_a_6585_, v_a_6586_, v_a_6587_, v_a_6588_);
lean_dec(v_a_6588_);
lean_dec_ref(v_a_6587_);
lean_dec(v_a_6586_);
lean_dec_ref(v_a_6585_);
lean_dec(v_a_6584_);
lean_dec_ref(v_a_6583_);
lean_dec(v_a_6582_);
lean_dec_ref(v_a_6581_);
lean_dec(v_a_6580_);
lean_dec(v_a_6579_);
lean_dec_ref(v_a_6578_);
return v_res_6590_;
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
