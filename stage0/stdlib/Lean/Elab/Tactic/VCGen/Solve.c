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
size_t v_x_8521__boxed_910_; size_t v_x_8522__boxed_911_; lean_object* v_res_912_; 
v_x_8521__boxed_910_ = lean_unbox_usize(v_x_906_);
lean_dec(v_x_906_);
v_x_8522__boxed_911_ = lean_unbox_usize(v_x_907_);
lean_dec(v_x_907_);
v_res_912_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_905_, v_x_8521__boxed_910_, v_x_8522__boxed_911_, v_x_908_, v_x_909_);
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
lean_object* v___x_924_; lean_object* v_mctx_925_; lean_object* v_cache_926_; lean_object* v_zetaDeltaFVarIds_927_; lean_object* v_postponed_928_; lean_object* v_diag_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_958_; 
v___x_924_ = lean_st_ref_take(v___y_922_);
v_mctx_925_ = lean_ctor_get(v___x_924_, 0);
v_cache_926_ = lean_ctor_get(v___x_924_, 1);
v_zetaDeltaFVarIds_927_ = lean_ctor_get(v___x_924_, 2);
v_postponed_928_ = lean_ctor_get(v___x_924_, 3);
v_diag_929_ = lean_ctor_get(v___x_924_, 4);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_958_ == 0)
{
v___x_931_ = v___x_924_;
v_isShared_932_ = v_isSharedCheck_958_;
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
v_isShared_932_ = v_isSharedCheck_958_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_depth_933_; lean_object* v_levelAssignDepth_934_; lean_object* v_lmvarCounter_935_; lean_object* v_mvarCounter_936_; lean_object* v_lDecls_937_; lean_object* v_decls_938_; lean_object* v_userNames_939_; lean_object* v_lAssignment_940_; lean_object* v_eAssignment_941_; lean_object* v_dAssignment_942_; lean_object* v_instanceTypedMVars_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_957_; 
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
v_instanceTypedMVars_943_ = lean_ctor_get(v_mctx_925_, 10);
v_isSharedCheck_957_ = !lean_is_exclusive(v_mctx_925_);
if (v_isSharedCheck_957_ == 0)
{
v___x_945_ = v_mctx_925_;
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_instanceTypedMVars_943_);
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
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_eAssignment_941_, v_mvarId_920_, v_val_921_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 8, v___x_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_depth_933_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_levelAssignDepth_934_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_lmvarCounter_935_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_mvarCounter_936_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v_lDecls_937_);
lean_ctor_set(v_reuseFailAlloc_956_, 5, v_decls_938_);
lean_ctor_set(v_reuseFailAlloc_956_, 6, v_userNames_939_);
lean_ctor_set(v_reuseFailAlloc_956_, 7, v_lAssignment_940_);
lean_ctor_set(v_reuseFailAlloc_956_, 8, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_956_, 9, v_dAssignment_942_);
lean_ctor_set(v_reuseFailAlloc_956_, 10, v_instanceTypedMVars_943_);
v___x_949_ = v_reuseFailAlloc_956_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_949_);
v___x_951_ = v___x_931_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_cache_926_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_zetaDeltaFVarIds_927_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_postponed_928_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v_diag_929_);
v___x_951_ = v_reuseFailAlloc_955_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_st_ref_put(v___y_922_, v___x_951_);
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
size_t v_x_9031__boxed_1146_; size_t v_x_9032__boxed_1147_; lean_object* v_res_1148_; 
v_x_9031__boxed_1146_ = lean_unbox_usize(v_x_1142_);
lean_dec(v_x_1142_);
v_x_9032__boxed_1147_ = lean_unbox_usize(v_x_1143_);
lean_dec(v_x_1143_);
v_res_1148_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1140_, v_x_1141_, v_x_9031__boxed_1146_, v_x_9032__boxed_1147_, v_x_1144_, v_x_1145_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(lean_object* v_rhs_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = l_Lean_Expr_hasMVar(v_rhs_1744_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec_ref(v_rhs_1744_);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
else
{
lean_object* v_n_1755_; lean_object* v___x_1756_; uint8_t v___y_1758_; uint8_t v___x_1805_; 
v_n_1755_ = l_Lean_Expr_getAppNumArgs(v_rhs_1744_);
v___x_1756_ = lean_unsigned_to_nat(7u);
v___x_1805_ = lean_nat_dec_lt(v___x_1756_, v_n_1755_);
if (v___x_1805_ == 0)
{
v___y_1758_ = v___x_1805_;
goto v___jp_1757_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1806_ = l_Lean_Expr_getAppFn(v_rhs_1744_);
v___x_1807_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1));
v___x_1808_ = l_Lean_Expr_isConstOf(v___x_1806_, v___x_1807_);
lean_dec_ref(v___x_1806_);
v___y_1758_ = v___x_1808_;
goto v___jp_1757_;
}
v___jp_1757_:
{
if (v___y_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v_n_1755_);
lean_dec_ref(v_rhs_1744_);
v___x_1759_ = lean_box(0);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v_prog_1764_; lean_object* v___x_1765_; 
v___x_1761_ = lean_nat_sub(v_n_1755_, v___x_1756_);
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_nat_sub(v___x_1761_, v___x_1762_);
lean_dec(v___x_1761_);
v_prog_1764_ = l_Lean_Expr_getRevArg_x21(v_rhs_1744_, v___x_1763_);
lean_inc_ref(v_prog_1764_);
v___x_1765_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_prog_1764_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1796_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1796_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1796_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
size_t v___x_1770_; size_t v___x_1771_; uint8_t v___x_1772_; 
v___x_1770_ = lean_ptr_addr(v_prog_1764_);
lean_dec_ref(v_prog_1764_);
v___x_1771_ = lean_ptr_addr(v_a_1766_);
v___x_1772_ = lean_usize_dec_eq(v___x_1770_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_del_object(v___x_1768_);
v___x_1773_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(v_rhs_1744_, v___x_1756_, v_n_1755_, v_a_1766_);
lean_dec(v_n_1755_);
v___x_1774_ = l_Lean_Meta_Sym_shareCommon(v___x_1773_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1783_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_a_1775_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1779_);
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1774_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1774_);
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
lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_dec(v_a_1766_);
lean_dec(v_n_1755_);
lean_dec_ref(v_rhs_1744_);
v___x_1792_ = lean_box(0);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1792_);
v___x_1794_ = v___x_1768_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
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
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v_prog_1764_);
lean_dec(v_n_1755_);
lean_dec_ref(v_rhs_1744_);
v_a_1797_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1765_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1765_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___boxed(lean_object* v_rhs_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_rhs_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f(lean_object* v_rhs_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_rhs_1818_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___boxed(lean_object* v_rhs_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f(v_rhs_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1846_, lean_object* v_a_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___y_1856_; lean_object* v___x_1859_; uint8_t v_debug_1860_; 
v___x_1859_ = lean_st_ref_get(v___y_1849_);
v_debug_1860_ = lean_ctor_get_uint8(v___x_1859_, sizeof(void*)*11);
lean_dec(v___x_1859_);
if (v_debug_1860_ == 0)
{
v___y_1856_ = v___y_1849_;
goto v___jp_1855_;
}
else
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1846_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref_known(v___x_1861_, 1);
v___x_1862_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_dec_ref_known(v___x_1862_, 1);
v___y_1856_ = v___y_1849_;
goto v___jp_1855_;
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v_a_1847_);
lean_dec_ref(v_f_1846_);
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v_a_1847_);
lean_dec_ref(v_f_1846_);
v_a_1871_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1861_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1861_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
v___jp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = l_Lean_Expr_app___override(v_f_1846_, v_a_1847_);
v___x_1858_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1857_, v___y_1856_);
return v___x_1858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1879_, lean_object* v_a_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_f_1879_, v_a_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0(lean_object* v_args_1889_, lean_object* v_endIdx_1890_, lean_object* v_b_1891_, lean_object* v_i_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
uint8_t v___x_1905_; 
v___x_1905_ = lean_nat_dec_le(v_endIdx_1890_, v_i_1892_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = l_Lean_instInhabitedExpr;
v___x_1907_ = lean_array_get_borrowed(v___x_1906_, v_args_1889_, v_i_1892_);
lean_inc(v___x_1907_);
v___x_1908_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_b_1891_, v___x_1907_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1910_ = lean_unsigned_to_nat(1u);
v___x_1911_ = lean_nat_add(v_i_1892_, v___x_1910_);
lean_dec(v_i_1892_);
v_b_1891_ = v_a_1909_;
v_i_1892_ = v___x_1911_;
goto _start;
}
else
{
lean_dec(v_i_1892_);
return v___x_1908_;
}
}
else
{
lean_object* v___x_1913_; 
lean_dec(v_i_1892_);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_b_1891_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0___boxed(lean_object* v_args_1914_, lean_object* v_endIdx_1915_, lean_object* v_b_1916_, lean_object* v_i_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0(v_args_1914_, v_endIdx_1915_, v_b_1916_, v_i_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v_endIdx_1915_);
lean_dec_ref(v_args_1914_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(lean_object* v_f_1931_, lean_object* v_args_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = lean_array_get_size(v_args_1932_);
v___x_1947_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0(v_args_1932_, v___x_1946_, v_f_1931_, v___x_1945_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0___boxed(lean_object* v_f_1948_, lean_object* v_args_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_f_1948_, v_args_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec_ref(v_args_1949_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(lean_object* v_goal_1963_, lean_object* v_target_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1980_ = l_Lean_Expr_cleanupAnnotations(v_target_1964_);
v___x_1981_ = l_Lean_Expr_isApp(v___x_1980_);
if (v___x_1981_ == 0)
{
lean_dec_ref(v___x_1980_);
lean_dec(v_goal_1963_);
goto v___jp_1977_;
}
else
{
lean_object* v_arg_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v_arg_1982_ = lean_ctor_get(v___x_1980_, 1);
lean_inc_ref(v_arg_1982_);
v___x_1983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1980_);
v___x_1984_ = l_Lean_Expr_isApp(v___x_1983_);
if (v___x_1984_ == 0)
{
lean_dec_ref(v___x_1983_);
lean_dec_ref(v_arg_1982_);
lean_dec(v_goal_1963_);
goto v___jp_1977_;
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
lean_dec_ref(v_arg_1982_);
lean_dec(v_goal_1963_);
goto v___jp_1977_;
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
lean_dec_ref(v_arg_1982_);
lean_dec(v_goal_1963_);
goto v___jp_1977_;
}
else
{
lean_object* v_arg_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_arg_1991_ = lean_ctor_get(v___x_1989_, 1);
lean_inc_ref(v_arg_1991_);
v___x_1992_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1989_);
v___x_1993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10));
v___x_1994_ = l_Lean_Expr_isConstOf(v___x_1992_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec_ref(v_arg_1982_);
lean_dec(v_goal_1963_);
goto v___jp_1977_;
}
else
{
lean_object* v___x_1995_; 
lean_inc_ref(v_arg_1991_);
v___x_1995_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1991_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1997_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1995_, 1);
lean_inc_ref(v_arg_1985_);
v___x_1997_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1985_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_1999_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
lean_inc_ref(v_arg_1982_);
v___x_1999_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1982_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc_n(v_a_2000_, 2);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_a_2000_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2061_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2061_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2061_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___y_2007_; lean_object* v___y_2043_; uint8_t v___y_2044_; lean_object* v___y_2053_; 
if (lean_obj_tag(v_a_2002_) == 0)
{
v___y_2053_ = v_a_2000_;
goto v___jp_2052_;
}
else
{
lean_object* v_val_2060_; 
lean_dec(v_a_2000_);
v_val_2060_ = lean_ctor_get(v_a_2002_, 0);
lean_inc(v_val_2060_);
lean_dec_ref_known(v_a_2002_, 1);
v___y_2053_ = v_val_2060_;
goto v___jp_2052_;
}
v___jp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2008_ = lean_unsigned_to_nat(4u);
v___x_2009_ = lean_mk_empty_array_with_capacity(v___x_2008_);
v___x_2010_ = lean_array_push(v___x_2009_, v_a_1996_);
v___x_2011_ = lean_array_push(v___x_2010_, v_arg_1988_);
v___x_2012_ = lean_array_push(v___x_2011_, v_a_1998_);
v___x_2013_ = lean_array_push(v___x_2012_, v___y_2007_);
v___x_2014_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v___x_1992_, v___x_2013_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec_ref(v___x_2013_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___x_2016_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_1963_, v_a_2015_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2025_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_a_2017_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2021_);
v___x_2023_ = v___x_2019_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
v_a_2026_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2016_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2016_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec(v_goal_1963_);
v_a_2034_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2014_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2014_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
v___jp_2042_:
{
if (v___y_2044_ == 0)
{
lean_del_object(v___x_2004_);
lean_dec_ref(v_arg_1982_);
v___y_2007_ = v___y_2043_;
goto v___jp_2006_;
}
else
{
size_t v___x_2045_; size_t v___x_2046_; uint8_t v___x_2047_; 
v___x_2045_ = lean_ptr_addr(v_arg_1982_);
lean_dec_ref(v_arg_1982_);
v___x_2046_ = lean_ptr_addr(v___y_2043_);
v___x_2047_ = lean_usize_dec_eq(v___x_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_del_object(v___x_2004_);
v___y_2007_ = v___y_2043_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
lean_dec_ref(v___y_2043_);
lean_dec(v_a_1998_);
lean_dec(v_a_1996_);
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1988_);
lean_dec(v_goal_1963_);
v___x_2048_ = lean_box(0);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2048_);
v___x_2050_ = v___x_2004_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
v___jp_2052_:
{
size_t v___x_2054_; size_t v___x_2055_; uint8_t v___x_2056_; 
v___x_2054_ = lean_ptr_addr(v_arg_1991_);
lean_dec_ref(v_arg_1991_);
v___x_2055_ = lean_ptr_addr(v_a_1996_);
v___x_2056_ = lean_usize_dec_eq(v___x_2054_, v___x_2055_);
if (v___x_2056_ == 0)
{
lean_dec_ref(v_arg_1985_);
v___y_2043_ = v___y_2053_;
v___y_2044_ = v___x_2056_;
goto v___jp_2042_;
}
else
{
size_t v___x_2057_; size_t v___x_2058_; uint8_t v___x_2059_; 
v___x_2057_ = lean_ptr_addr(v_arg_1985_);
lean_dec_ref(v_arg_1985_);
v___x_2058_ = lean_ptr_addr(v_a_1998_);
v___x_2059_ = lean_usize_dec_eq(v___x_2057_, v___x_2058_);
v___y_2043_ = v___y_2053_;
v___y_2044_ = v___x_2059_;
goto v___jp_2042_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_a_2000_);
lean_dec(v_a_1998_);
lean_dec(v_a_1996_);
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec_ref(v_arg_1982_);
lean_dec(v_goal_1963_);
v_a_2062_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2001_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2001_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_a_1998_);
lean_dec(v_a_1996_);
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec_ref(v_arg_1982_);
lean_dec(v_goal_1963_);
v_a_2070_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_1999_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_1999_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_a_1996_);
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec_ref(v_arg_1982_);
lean_dec(v_goal_1963_);
v_a_2078_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_1997_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_1997_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
lean_dec_ref(v_arg_1982_);
lean_dec(v_goal_1963_);
v_a_2086_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_1995_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_1995_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
}
}
}
v___jp_1977_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_box(0);
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f___boxed(lean_object* v_goal_2094_, lean_object* v_target_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(v_goal_2094_, v_target_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1(lean_object* v_f_2109_, lean_object* v_a_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_f_2109_, v_a_2110_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2124_, lean_object* v_a_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1(v_f_2124_, v_a_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2138_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__2));
v___x_2146_ = l_Lean_stringToMessageData(v___x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(lean_object* v_goal_2147_, lean_object* v_pre_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = l_Lean_Expr_cleanupAnnotations(v_pre_2148_);
v___x_2165_ = l_Lean_Expr_isApp(v___x_2164_);
if (v___x_2165_ == 0)
{
lean_dec_ref(v___x_2164_);
lean_dec(v_goal_2147_);
goto v___jp_2161_;
}
else
{
lean_object* v_arg_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v_arg_2166_ = lean_ctor_get(v___x_2164_, 1);
lean_inc_ref(v_arg_2166_);
v___x_2167_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2164_);
v___x_2168_ = l_Lean_Expr_isApp(v___x_2167_);
if (v___x_2168_ == 0)
{
lean_dec_ref(v___x_2167_);
lean_dec_ref(v_arg_2166_);
lean_dec(v_goal_2147_);
goto v___jp_2161_;
}
else
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2167_);
v___x_2170_ = l_Lean_Expr_isApp(v___x_2169_);
if (v___x_2170_ == 0)
{
lean_dec_ref(v___x_2169_);
lean_dec_ref(v_arg_2166_);
lean_dec(v_goal_2147_);
goto v___jp_2161_;
}
else
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2169_);
v___x_2172_ = l_Lean_Expr_isApp(v___x_2171_);
if (v___x_2172_ == 0)
{
lean_dec_ref(v___x_2171_);
lean_dec_ref(v_arg_2166_);
lean_dec(v_goal_2147_);
goto v___jp_2161_;
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2173_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2171_);
v___x_2174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_2175_ = l_Lean_Expr_isConstOf(v___x_2173_, v___x_2174_);
lean_dec_ref(v___x_2173_);
if (v___x_2175_ == 0)
{
lean_dec_ref(v_arg_2166_);
lean_dec(v_goal_2147_);
goto v___jp_2161_;
}
else
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3));
v___x_2177_ = l_Lean_Expr_isAppOf(v_arg_2166_, v___x_2176_);
lean_dec_ref(v_arg_2166_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_dec(v_goal_2147_);
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
return v___x_2179_;
}
else
{
lean_object* v_backwardRules_2180_; lean_object* v_meetTop_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_backwardRules_2180_ = lean_ctor_get(v_a_2149_, 0);
v_meetTop_2181_ = lean_ctor_get(v_backwardRules_2180_, 10);
v___x_2182_ = lean_box(0);
lean_inc(v_goal_2147_);
lean_inc_ref(v_meetTop_2181_);
v___x_2183_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_meetTop_2181_, v_goal_2147_, v___x_2182_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2210_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2210_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2210_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; 
if (lean_obj_tag(v_a_2184_) == 1)
{
lean_object* v_mvarIds_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2209_; 
v_mvarIds_2197_ = lean_ctor_get(v_a_2184_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_a_2184_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2199_ = v_a_2184_;
v_isShared_2200_ = v_isSharedCheck_2209_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_mvarIds_2197_);
lean_dec(v_a_2184_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2209_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
if (lean_obj_tag(v_mvarIds_2197_) == 1)
{
lean_object* v_tail_2201_; 
v_tail_2201_ = lean_ctor_get(v_mvarIds_2197_, 1);
if (lean_obj_tag(v_tail_2201_) == 0)
{
lean_object* v_head_2202_; lean_object* v___x_2204_; 
lean_dec(v_goal_2147_);
v_head_2202_ = lean_ctor_get(v_mvarIds_2197_, 0);
lean_inc(v_head_2202_);
lean_dec_ref_known(v_mvarIds_2197_, 2);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v_head_2202_);
v___x_2204_ = v___x_2199_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_head_2202_);
v___x_2204_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2206_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2204_);
v___x_2206_ = v___x_2186_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2197_, 2);
lean_del_object(v___x_2199_);
lean_del_object(v___x_2186_);
v___y_2189_ = v_a_2156_;
v___y_2190_ = v_a_2157_;
v___y_2191_ = v_a_2158_;
v___y_2192_ = v_a_2159_;
goto v___jp_2188_;
}
}
else
{
lean_del_object(v___x_2199_);
lean_dec(v_mvarIds_2197_);
lean_del_object(v___x_2186_);
v___y_2189_ = v_a_2156_;
v___y_2190_ = v_a_2157_;
v___y_2191_ = v_a_2158_;
v___y_2192_ = v_a_2159_;
goto v___jp_2188_;
}
}
}
else
{
lean_del_object(v___x_2186_);
lean_dec(v_a_2184_);
v___y_2189_ = v_a_2156_;
v___y_2190_ = v_a_2157_;
v___y_2191_ = v_a_2158_;
v___y_2192_ = v_a_2159_;
goto v___jp_2188_;
}
v___jp_2188_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2193_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3);
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v_goal_2147_);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2193_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2195_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
return v___x_2196_;
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_goal_2147_);
v_a_2211_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2183_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2183_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
}
}
}
}
v___jp_2161_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_box(0);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___boxed(lean_object* v_goal_2219_, lean_object* v_pre_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(v_goal_2219_, v_pre_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(lean_object* v_goal_2241_, lean_object* v_pre_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v___x_2258_; uint8_t v___x_2259_; 
v___x_2258_ = l_Lean_Expr_cleanupAnnotations(v_pre_2242_);
v___x_2259_ = l_Lean_Expr_isApp(v___x_2258_);
if (v___x_2259_ == 0)
{
lean_dec_ref(v___x_2258_);
lean_dec(v_goal_2241_);
goto v___jp_2255_;
}
else
{
lean_object* v_arg_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v_arg_2260_ = lean_ctor_get(v___x_2258_, 1);
lean_inc_ref(v_arg_2260_);
v___x_2261_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2258_);
v___x_2262_ = l_Lean_Expr_isApp(v___x_2261_);
if (v___x_2262_ == 0)
{
lean_dec_ref(v___x_2261_);
lean_dec_ref(v_arg_2260_);
lean_dec(v_goal_2241_);
goto v___jp_2255_;
}
else
{
lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2261_);
v___x_2264_ = l_Lean_Expr_isApp(v___x_2263_);
if (v___x_2264_ == 0)
{
lean_dec_ref(v___x_2263_);
lean_dec_ref(v_arg_2260_);
lean_dec(v_goal_2241_);
goto v___jp_2255_;
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2265_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2263_);
v___x_2266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_2267_ = l_Lean_Expr_isConstOf(v___x_2265_, v___x_2266_);
lean_dec_ref(v___x_2265_);
if (v___x_2267_ == 0)
{
lean_dec_ref(v_arg_2260_);
lean_dec(v_goal_2241_);
goto v___jp_2255_;
}
else
{
uint8_t v___x_2268_; 
v___x_2268_ = l_Lean_Expr_isTrue(v_arg_2260_);
if (v___x_2268_ == 0)
{
lean_object* v_backwardRules_2269_; lean_object* v_ofPropPreIntro_2270_; lean_object* v___x_2271_; 
v_backwardRules_2269_ = lean_ctor_get(v_a_2243_, 0);
v_ofPropPreIntro_2270_ = lean_ctor_get(v_backwardRules_2269_, 3);
lean_inc_ref(v_ofPropPreIntro_2270_);
v___x_2271_ = l_Lean_Elab_Tactic_VCGen_introPre(v_ofPropPreIntro_2270_, v_goal_2241_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2280_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2276_, 0, v_a_2272_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_a_2281_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2271_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2271_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec(v_goal_2241_);
v___x_2289_ = lean_box(0);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
return v___x_2290_;
}
}
}
}
}
v___jp_2255_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_box(0);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
return v___x_2257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___boxed(lean_object* v_goal_2291_, lean_object* v_pre_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(v_goal_2291_, v_pre_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(lean_object* v_goal_2306_, lean_object* v_pre_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = l_Lean_Expr_cleanupAnnotations(v_pre_2307_);
v___x_2327_ = l_Lean_Expr_isApp(v___x_2326_);
if (v___x_2327_ == 0)
{
lean_dec_ref(v___x_2326_);
lean_dec(v_goal_2306_);
goto v___jp_2320_;
}
else
{
lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2326_);
v___x_2329_ = l_Lean_Expr_isApp(v___x_2328_);
if (v___x_2329_ == 0)
{
lean_dec_ref(v___x_2328_);
lean_dec(v_goal_2306_);
goto v___jp_2320_;
}
else
{
lean_object* v_arg_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v_arg_2330_ = lean_ctor_get(v___x_2328_, 1);
lean_inc_ref(v_arg_2330_);
v___x_2331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2328_);
v___x_2332_ = l_Lean_Expr_isApp(v___x_2331_);
if (v___x_2332_ == 0)
{
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_arg_2330_);
lean_dec(v_goal_2306_);
goto v___jp_2320_;
}
else
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2331_);
v___x_2334_ = l_Lean_Expr_isApp(v___x_2333_);
if (v___x_2334_ == 0)
{
lean_dec_ref(v___x_2333_);
lean_dec_ref(v_arg_2330_);
lean_dec(v_goal_2306_);
goto v___jp_2320_;
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2333_);
v___x_2336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_2337_ = l_Lean_Expr_isConstOf(v___x_2335_, v___x_2336_);
lean_dec_ref(v___x_2335_);
if (v___x_2337_ == 0)
{
lean_dec_ref(v_arg_2330_);
lean_dec(v_goal_2306_);
goto v___jp_2320_;
}
else
{
lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = l_Lean_Expr_cleanupAnnotations(v_arg_2330_);
v___x_2339_ = l_Lean_Expr_isApp(v___x_2338_);
if (v___x_2339_ == 0)
{
lean_dec_ref(v___x_2338_);
lean_dec(v_goal_2306_);
goto v___jp_2323_;
}
else
{
lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2338_);
v___x_2341_ = l_Lean_Expr_isApp(v___x_2340_);
if (v___x_2341_ == 0)
{
lean_dec_ref(v___x_2340_);
lean_dec(v_goal_2306_);
goto v___jp_2323_;
}
else
{
lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2340_);
v___x_2343_ = l_Lean_Expr_isApp(v___x_2342_);
if (v___x_2343_ == 0)
{
lean_dec_ref(v___x_2342_);
lean_dec(v_goal_2306_);
goto v___jp_2323_;
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2342_);
v___x_2345_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_2346_ = l_Lean_Expr_isConstOf(v___x_2344_, v___x_2345_);
lean_dec_ref(v___x_2344_);
if (v___x_2346_ == 0)
{
lean_dec(v_goal_2306_);
goto v___jp_2323_;
}
else
{
lean_object* v_backwardRules_2347_; lean_object* v_ofPropMeetPreIntro_2348_; lean_object* v___x_2349_; 
v_backwardRules_2347_ = lean_ctor_get(v_a_2308_, 0);
v_ofPropMeetPreIntro_2348_ = lean_ctor_get(v_backwardRules_2347_, 4);
lean_inc_ref(v_ofPropMeetPreIntro_2348_);
v___x_2349_ = l_Lean_Elab_Tactic_VCGen_introPre(v_ofPropMeetPreIntro_2348_, v_goal_2306_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2358_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2358_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2358_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2354_, 0, v_a_2350_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2354_);
v___x_2356_ = v___x_2352_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
v_a_2359_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2349_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2349_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
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
v___jp_2320_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_box(0);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
v___jp_2323_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_box(0);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
return v___x_2325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f___boxed(lean_object* v_goal_2367_, lean_object* v_pre_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(v_goal_2367_, v_pre_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
return v_res_2381_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__2));
v___x_2389_ = l_Lean_stringToMessageData(v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(lean_object* v_goal_2390_, lean_object* v_pre_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2404_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1));
v___x_2405_ = lean_unsigned_to_nat(4u);
v___x_2406_ = l_Lean_Expr_isAppOfArity(v_pre_2391_, v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_dec(v_goal_2390_);
v___x_2407_ = lean_box(0);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
return v___x_2408_;
}
else
{
lean_object* v_backwardRules_2409_; lean_object* v_iSupPreIntro_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v_backwardRules_2409_ = lean_ctor_get(v_a_2392_, 0);
v_iSupPreIntro_2410_ = lean_ctor_get(v_backwardRules_2409_, 5);
v___x_2411_ = lean_box(0);
lean_inc(v_goal_2390_);
lean_inc_ref(v_iSupPreIntro_2410_);
v___x_2412_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_iSupPreIntro_2410_, v_goal_2390_, v___x_2411_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2439_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2439_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2439_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; 
if (lean_obj_tag(v_a_2413_) == 1)
{
lean_object* v_mvarIds_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2438_; 
v_mvarIds_2426_ = lean_ctor_get(v_a_2413_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_a_2413_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2428_ = v_a_2413_;
v_isShared_2429_ = v_isSharedCheck_2438_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_mvarIds_2426_);
lean_dec(v_a_2413_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2438_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
if (lean_obj_tag(v_mvarIds_2426_) == 1)
{
lean_object* v_tail_2430_; 
v_tail_2430_ = lean_ctor_get(v_mvarIds_2426_, 1);
if (lean_obj_tag(v_tail_2430_) == 0)
{
lean_object* v_head_2431_; lean_object* v___x_2433_; 
lean_dec(v_goal_2390_);
v_head_2431_ = lean_ctor_get(v_mvarIds_2426_, 0);
lean_inc(v_head_2431_);
lean_dec_ref_known(v_mvarIds_2426_, 2);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v_head_2431_);
v___x_2433_ = v___x_2428_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_head_2431_);
v___x_2433_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2435_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v___x_2433_);
v___x_2435_ = v___x_2415_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2426_, 2);
lean_del_object(v___x_2428_);
lean_del_object(v___x_2415_);
v___y_2418_ = v_a_2399_;
v___y_2419_ = v_a_2400_;
v___y_2420_ = v_a_2401_;
v___y_2421_ = v_a_2402_;
goto v___jp_2417_;
}
}
else
{
lean_del_object(v___x_2428_);
lean_dec(v_mvarIds_2426_);
lean_del_object(v___x_2415_);
v___y_2418_ = v_a_2399_;
v___y_2419_ = v_a_2400_;
v___y_2420_ = v_a_2401_;
v___y_2421_ = v_a_2402_;
goto v___jp_2417_;
}
}
}
else
{
lean_del_object(v___x_2415_);
lean_dec(v_a_2413_);
v___y_2418_ = v_a_2399_;
v___y_2419_ = v_a_2400_;
v___y_2420_ = v_a_2401_;
v___y_2421_ = v_a_2402_;
goto v___jp_2417_;
}
v___jp_2417_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2422_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3);
v___x_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2423_, 0, v_goal_2390_);
v___x_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2424_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2425_;
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v_goal_2390_);
v_a_2440_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2412_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2412_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___boxed(lean_object* v_goal_2448_, lean_object* v_pre_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(v_goal_2448_, v_pre_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec_ref(v_pre_2449_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(lean_object* v_goal_2463_, lean_object* v_00_u03b1_2464_, lean_object* v_pre_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
uint8_t v___x_2478_; 
v___x_2478_ = l_Lean_Expr_isProp(v_00_u03b1_2464_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec(v_goal_2463_);
v___x_2479_ = lean_box(0);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__3));
v___x_2482_ = l_Lean_Expr_isAppOf(v_pre_2465_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v_backwardRules_2483_; lean_object* v_propPreIntro_2484_; lean_object* v___x_2485_; 
v_backwardRules_2483_ = lean_ctor_get(v_a_2466_, 0);
v_propPreIntro_2484_ = lean_ctor_get(v_backwardRules_2483_, 2);
lean_inc_ref(v_propPreIntro_2484_);
v___x_2485_ = l_Lean_Elab_Tactic_VCGen_introPre(v_propPreIntro_2484_, v_goal_2463_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2494_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2494_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2494_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_a_2486_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v___x_2490_);
v___x_2492_ = v___x_2488_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
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
v_a_2495_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2485_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2485_);
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
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec(v_goal_2463_);
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f___boxed(lean_object* v_goal_2505_, lean_object* v_00_u03b1_2506_, lean_object* v_pre_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(v_goal_2505_, v_00_u03b1_2506_, v_pre_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec_ref(v_pre_2507_);
lean_dec_ref(v_00_u03b1_2506_);
return v_res_2520_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__0));
v___x_2523_ = l_Lean_stringToMessageData(v___x_2522_);
return v___x_2523_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4(void){
_start:
{
uint8_t v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = 0;
v___x_2530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3));
v___x_2531_ = l_Lean_MessageData_ofConstName(v___x_2530_, v___x_2529_);
return v___x_2531_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4);
v___x_2533_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1);
v___x_2534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
lean_ctor_set(v___x_2534_, 1, v___x_2532_);
return v___x_2534_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__6));
v___x_2537_ = l_Lean_stringToMessageData(v___x_2536_);
return v___x_2537_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7);
v___x_2539_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5);
v___x_2540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
lean_ctor_set(v___x_2540_, 1, v___x_2538_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(lean_object* v_goal_2541_, lean_object* v_pre_2542_, lean_object* v_target_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; uint8_t v___x_2594_; 
lean_inc_ref(v_pre_2542_);
v___x_2594_ = l_Lean_Expr_isTrue(v_pre_2542_);
if (v___x_2594_ == 0)
{
v___y_2557_ = v_a_2549_;
v___y_2558_ = v_a_2550_;
v___y_2559_ = v_a_2551_;
v___y_2560_ = v_a_2552_;
v___y_2561_ = v_a_2553_;
v___y_2562_ = v_a_2554_;
goto v___jp_2556_;
}
else
{
lean_object* v_backwardRules_2595_; lean_object* v_truePreIntro_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec_ref(v_pre_2542_);
v_backwardRules_2595_ = lean_ctor_get(v_a_2544_, 0);
v_truePreIntro_2596_ = lean_ctor_get(v_backwardRules_2595_, 6);
v___x_2597_ = lean_box(0);
lean_inc_ref(v_truePreIntro_2596_);
v___x_2598_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_truePreIntro_2596_, v_goal_2541_, v___x_2597_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2634_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2634_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2634_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; 
if (lean_obj_tag(v_a_2599_) == 1)
{
lean_object* v_mvarIds_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2633_; 
v_mvarIds_2622_ = lean_ctor_get(v_a_2599_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_a_2599_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2624_ = v_a_2599_;
v_isShared_2625_ = v_isSharedCheck_2633_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_mvarIds_2622_);
lean_dec(v_a_2599_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2633_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
if (lean_obj_tag(v_mvarIds_2622_) == 1)
{
lean_object* v_tail_2626_; 
v_tail_2626_ = lean_ctor_get(v_mvarIds_2622_, 1);
if (lean_obj_tag(v_tail_2626_) == 0)
{
lean_object* v___x_2628_; 
lean_dec_ref(v_target_2543_);
if (v_isShared_2625_ == 0)
{
v___x_2628_ = v___x_2624_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_mvarIds_2622_);
v___x_2628_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2630_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v___x_2628_);
v___x_2630_ = v___x_2601_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2622_, 2);
lean_del_object(v___x_2624_);
lean_del_object(v___x_2601_);
v___y_2604_ = v_a_2549_;
v___y_2605_ = v_a_2550_;
v___y_2606_ = v_a_2551_;
v___y_2607_ = v_a_2552_;
v___y_2608_ = v_a_2553_;
v___y_2609_ = v_a_2554_;
goto v___jp_2603_;
}
}
else
{
lean_del_object(v___x_2624_);
lean_dec(v_mvarIds_2622_);
lean_del_object(v___x_2601_);
v___y_2604_ = v_a_2549_;
v___y_2605_ = v_a_2550_;
v___y_2606_ = v_a_2551_;
v___y_2607_ = v_a_2552_;
v___y_2608_ = v_a_2553_;
v___y_2609_ = v_a_2554_;
goto v___jp_2603_;
}
}
}
else
{
lean_del_object(v___x_2601_);
lean_dec(v_a_2599_);
v___y_2604_ = v_a_2549_;
v___y_2605_ = v_a_2550_;
v___y_2606_ = v_a_2551_;
v___y_2607_ = v_a_2552_;
v___y_2608_ = v_a_2553_;
v___y_2609_ = v_a_2554_;
goto v___jp_2603_;
}
v___jp_2603_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
v___x_2610_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8);
v___x_2611_ = l_Lean_indentExpr(v_target_2543_);
v___x_2612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2610_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2612_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec_ref(v_target_2543_);
v_a_2635_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2598_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2598_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
v___jp_2556_:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(v_goal_2541_, v_target_2543_, v_pre_2542_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2585_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2585_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2585_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
if (lean_obj_tag(v_a_2564_) == 1)
{
lean_object* v_val_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2580_; 
v_val_2568_ = lean_ctor_get(v_a_2564_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_a_2564_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2570_ = v_a_2564_;
v_isShared_2571_ = v_isSharedCheck_2580_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_val_2568_);
lean_dec(v_a_2564_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2580_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2573_, 0, v_val_2568_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2573_);
v___x_2575_ = v___x_2570_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2577_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2575_);
v___x_2577_ = v___x_2566_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
else
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
lean_dec(v_a_2564_);
v___x_2581_ = lean_box(0);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2581_);
v___x_2583_ = v___x_2566_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
v_a_2586_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2563_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2563_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___boxed(lean_object* v_goal_2643_, lean_object* v_pre_2644_, lean_object* v_target_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(v_goal_2643_, v_pre_2644_, v_target_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(lean_object* v_scope_2659_, lean_object* v_goal_2660_, lean_object* v_00_u03b1_2661_, lean_object* v_pre_2662_, lean_object* v_target_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v_g_2677_; lean_object* v_g_2684_; lean_object* v_h_2685_; lean_object* v___x_2703_; 
lean_inc_ref(v_pre_2662_);
lean_inc(v_goal_2660_);
v___x_2703_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(v_goal_2660_, v_pre_2662_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
if (lean_obj_tag(v_a_2704_) == 1)
{
lean_object* v_val_2705_; 
lean_dec_ref(v_target_2663_);
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
v_val_2705_ = lean_ctor_get(v_a_2704_, 0);
lean_inc(v_val_2705_);
lean_dec_ref_known(v_a_2704_, 1);
v_g_2677_ = v_val_2705_;
goto v___jp_2676_;
}
else
{
lean_object* v___x_2706_; 
lean_dec(v_a_2704_);
lean_inc_ref(v_pre_2662_);
lean_inc(v_goal_2660_);
v___x_2706_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(v_goal_2660_, v_pre_2662_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2706_, 1);
if (lean_obj_tag(v_a_2707_) == 1)
{
lean_object* v_val_2708_; lean_object* v_fst_2709_; lean_object* v_snd_2710_; 
lean_dec_ref(v_target_2663_);
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
v_val_2708_ = lean_ctor_get(v_a_2707_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v_a_2707_, 1);
v_fst_2709_ = lean_ctor_get(v_val_2708_, 0);
lean_inc(v_fst_2709_);
v_snd_2710_ = lean_ctor_get(v_val_2708_, 1);
lean_inc(v_snd_2710_);
lean_dec(v_val_2708_);
v_g_2684_ = v_fst_2709_;
v_h_2685_ = v_snd_2710_;
goto v___jp_2683_;
}
else
{
lean_object* v___x_2711_; 
lean_dec(v_a_2707_);
lean_inc_ref(v_pre_2662_);
lean_inc(v_goal_2660_);
v___x_2711_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(v_goal_2660_, v_pre_2662_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
if (lean_obj_tag(v_a_2712_) == 1)
{
lean_object* v_val_2713_; lean_object* v_fst_2714_; lean_object* v_snd_2715_; 
lean_dec_ref(v_target_2663_);
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
v_val_2713_ = lean_ctor_get(v_a_2712_, 0);
lean_inc(v_val_2713_);
lean_dec_ref_known(v_a_2712_, 1);
v_fst_2714_ = lean_ctor_get(v_val_2713_, 0);
lean_inc(v_fst_2714_);
v_snd_2715_ = lean_ctor_get(v_val_2713_, 1);
lean_inc(v_snd_2715_);
lean_dec(v_val_2713_);
v_g_2684_ = v_fst_2714_;
v_h_2685_ = v_snd_2715_;
goto v___jp_2683_;
}
else
{
lean_object* v___x_2716_; 
lean_dec(v_a_2712_);
lean_inc(v_goal_2660_);
v___x_2716_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(v_goal_2660_, v_pre_2662_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
if (lean_obj_tag(v_a_2717_) == 1)
{
lean_object* v_val_2718_; 
lean_dec_ref(v_target_2663_);
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
v_val_2718_ = lean_ctor_get(v_a_2717_, 0);
lean_inc(v_val_2718_);
lean_dec_ref_known(v_a_2717_, 1);
v_g_2677_ = v_val_2718_;
goto v___jp_2676_;
}
else
{
lean_object* v___x_2719_; 
lean_dec(v_a_2717_);
lean_inc(v_goal_2660_);
v___x_2719_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_goal_2660_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
if (lean_obj_tag(v_a_2720_) == 1)
{
lean_object* v_val_2721_; 
lean_dec_ref(v_target_2663_);
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
v_val_2721_ = lean_ctor_get(v_a_2720_, 0);
lean_inc(v_val_2721_);
lean_dec_ref_known(v_a_2720_, 1);
v_g_2677_ = v_val_2721_;
goto v___jp_2676_;
}
else
{
lean_object* v___x_2722_; 
lean_dec(v_a_2720_);
lean_inc_ref(v_pre_2662_);
lean_inc(v_goal_2660_);
v___x_2722_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(v_goal_2660_, v_pre_2662_, v_target_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2760_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2760_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2760_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
if (lean_obj_tag(v_a_2723_) == 1)
{
lean_object* v_val_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2738_; 
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
v_val_2727_ = lean_ctor_get(v_a_2723_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_a_2723_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2729_ = v_a_2723_;
v_isShared_2730_ = v_isSharedCheck_2738_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_val_2727_);
lean_dec(v_a_2723_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2738_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2731_, 0, v_scope_2659_);
lean_ctor_set(v___x_2731_, 1, v_val_2727_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2731_);
v___x_2733_ = v___x_2729_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2735_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2733_);
v___x_2735_ = v___x_2725_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v___x_2739_; 
lean_del_object(v___x_2725_);
lean_dec(v_a_2723_);
v___x_2739_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(v_goal_2660_, v_00_u03b1_2661_, v_pre_2662_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
lean_dec_ref(v_pre_2662_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2751_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2751_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2751_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
if (lean_obj_tag(v_a_2740_) == 1)
{
lean_object* v_val_2744_; lean_object* v_fst_2745_; lean_object* v_snd_2746_; 
lean_del_object(v___x_2742_);
v_val_2744_ = lean_ctor_get(v_a_2740_, 0);
lean_inc(v_val_2744_);
lean_dec_ref_known(v_a_2740_, 1);
v_fst_2745_ = lean_ctor_get(v_val_2744_, 0);
lean_inc(v_fst_2745_);
v_snd_2746_ = lean_ctor_get(v_val_2744_, 1);
lean_inc(v_snd_2746_);
lean_dec(v_val_2744_);
v_g_2684_ = v_fst_2745_;
v_h_2685_ = v_snd_2746_;
goto v___jp_2683_;
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
lean_dec(v_a_2740_);
lean_dec_ref(v_scope_2659_);
v___x_2747_ = lean_box(0);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2747_);
v___x_2749_ = v___x_2742_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref(v_scope_2659_);
v_a_2752_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2739_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2739_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
lean_dec_ref(v_scope_2659_);
v_a_2761_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2722_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2722_);
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
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec_ref(v_target_2663_);
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
lean_dec_ref(v_scope_2659_);
v_a_2769_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2719_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2719_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec_ref(v_target_2663_);
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
lean_dec_ref(v_scope_2659_);
v_a_2777_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2716_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2716_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec_ref(v_target_2663_);
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
lean_dec_ref(v_scope_2659_);
v_a_2785_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2711_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2711_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_dec_ref(v_target_2663_);
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
lean_dec_ref(v_scope_2659_);
v_a_2793_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2706_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2706_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec_ref(v_target_2663_);
lean_dec_ref(v_pre_2662_);
lean_dec(v_goal_2660_);
lean_dec_ref(v_scope_2659_);
v_a_2801_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2703_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2703_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
v___jp_2676_:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2678_ = lean_box(0);
v___x_2679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2679_, 0, v_g_2677_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2680_, 0, v_scope_2659_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
return v___x_2682_;
}
v___jp_2683_:
{
lean_object* v_specs_2686_; lean_object* v_jps_2687_; lean_object* v_nextDeclIdx_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2701_; 
v_specs_2686_ = lean_ctor_get(v_scope_2659_, 0);
v_jps_2687_ = lean_ctor_get(v_scope_2659_, 1);
v_nextDeclIdx_2688_ = lean_ctor_get(v_scope_2659_, 3);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_scope_2659_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; 
v_unused_2702_ = lean_ctor_get(v_scope_2659_, 2);
lean_dec(v_unused_2702_);
v___x_2690_ = v_scope_2659_;
v_isShared_2691_ = v_isSharedCheck_2701_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_nextDeclIdx_2688_);
lean_inc(v_jps_2687_);
lean_inc(v_specs_2686_);
lean_dec(v_scope_2659_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2701_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_h_2685_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 2, v___x_2692_);
v___x_2694_ = v___x_2690_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_specs_2686_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_jps_2687_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_nextDeclIdx_2688_);
v___x_2694_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2695_ = lean_box(0);
v___x_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2696_, 0, v_g_2684_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2694_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
return v___x_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f___boxed(lean_object** _args){
lean_object* v_scope_2809_ = _args[0];
lean_object* v_goal_2810_ = _args[1];
lean_object* v_00_u03b1_2811_ = _args[2];
lean_object* v_pre_2812_ = _args[3];
lean_object* v_target_2813_ = _args[4];
lean_object* v_a_2814_ = _args[5];
lean_object* v_a_2815_ = _args[6];
lean_object* v_a_2816_ = _args[7];
lean_object* v_a_2817_ = _args[8];
lean_object* v_a_2818_ = _args[9];
lean_object* v_a_2819_ = _args[10];
lean_object* v_a_2820_ = _args[11];
lean_object* v_a_2821_ = _args[12];
lean_object* v_a_2822_ = _args[13];
lean_object* v_a_2823_ = _args[14];
lean_object* v_a_2824_ = _args[15];
lean_object* v_a_2825_ = _args[16];
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(v_scope_2809_, v_goal_2810_, v_00_u03b1_2811_, v_pre_2812_, v_target_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec_ref(v_00_u03b1_2811_);
return v_res_2826_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0(void){
_start:
{
lean_object* v___x_2827_; lean_object* v_dummy_2828_; 
v___x_2827_ = lean_box(0);
v_dummy_2828_ = l_Lean_Expr_sort___override(v___x_2827_);
return v_dummy_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(lean_object* v_goal_2829_, lean_object* v_info_2830_, lean_object* v_prog_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v_head_2844_; lean_object* v_args_2845_; lean_object* v_excessArgs_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_head_2844_ = lean_ctor_get(v_info_2830_, 0);
lean_inc_ref(v_head_2844_);
v_args_2845_ = lean_ctor_get(v_info_2830_, 1);
lean_inc_ref(v_args_2845_);
v_excessArgs_2846_ = lean_ctor_get(v_info_2830_, 2);
lean_inc_ref(v_excessArgs_2846_);
lean_dec_ref(v_info_2830_);
v___x_2847_ = lean_unsigned_to_nat(7u);
v___x_2848_ = lean_array_set(v_args_2845_, v___x_2847_, v_prog_2831_);
v___x_2849_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_head_2844_, v___x_2848_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
lean_dec_ref(v___x_2848_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_a_2850_, v_excessArgs_2846_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
lean_dec_ref(v_excessArgs_2846_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2853_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref_known(v___x_2851_, 1);
lean_inc(v_goal_2829_);
v___x_2853_ = l_Lean_MVarId_getType(v_goal_2829_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v_dummy_2855_; lean_object* v_nargs_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc_n(v_a_2854_, 2);
lean_dec_ref_known(v___x_2853_, 1);
v_dummy_2855_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0);
v_nargs_2856_ = l_Lean_Expr_getAppNumArgs(v_a_2854_);
lean_inc(v_nargs_2856_);
v___x_2857_ = lean_mk_array(v_nargs_2856_, v_dummy_2855_);
v___x_2858_ = lean_unsigned_to_nat(1u);
v___x_2859_ = lean_nat_sub(v_nargs_2856_, v___x_2858_);
lean_dec(v_nargs_2856_);
v___x_2860_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2854_, v___x_2857_, v___x_2859_);
v___x_2861_ = l_Lean_Expr_getAppFn(v_a_2854_);
lean_dec(v_a_2854_);
v___x_2862_ = lean_array_get_size(v___x_2860_);
v___x_2863_ = lean_nat_sub(v___x_2862_, v___x_2858_);
v___x_2864_ = lean_array_set(v___x_2860_, v___x_2863_, v_a_2852_);
lean_dec(v___x_2863_);
v___x_2865_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v___x_2861_, v___x_2864_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
lean_dec_ref(v___x_2864_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2867_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2867_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2829_, v_a_2866_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
return v___x_2867_;
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec(v_goal_2829_);
v_a_2868_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2865_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2865_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec(v_a_2852_);
lean_dec(v_goal_2829_);
v_a_2876_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2853_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2853_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_goal_2829_);
v_a_2884_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2851_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2851_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec_ref(v_excessArgs_2846_);
lean_dec(v_goal_2829_);
v_a_2892_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2849_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2849_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___boxed(lean_object* v_goal_2900_, lean_object* v_info_2901_, lean_object* v_prog_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_2900_, v_info_2901_, v_prog_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(lean_object* v_goal_2916_, lean_object* v_info_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_2917_);
if (lean_obj_tag(v___x_2930_) == 10)
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = l_Lean_Expr_consumeMData(v___x_2930_);
lean_dec_ref_known(v___x_2930_, 2);
v___x_2932_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_2916_, v_info_2917_, v___x_2931_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2941_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2941_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2941_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_a_2933_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v___x_2937_);
v___x_2939_ = v___x_2935_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
v_a_2942_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2932_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2932_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
lean_dec_ref(v___x_2930_);
lean_dec_ref(v_info_2917_);
lean_dec(v_goal_2916_);
v___x_2950_ = lean_box(0);
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
return v___x_2951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f___boxed(lean_object* v_goal_2952_, lean_object* v_info_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(v_goal_2952_, v_info_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec(v_a_2955_);
lean_dec_ref(v_a_2954_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object* v_revArgs_2967_, lean_object* v_start_2968_, lean_object* v_b_2969_, lean_object* v_i_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
uint8_t v___x_2978_; 
v___x_2978_ = lean_nat_dec_le(v_i_2970_, v_start_2968_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v_i_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2979_ = lean_unsigned_to_nat(1u);
v_i_2980_ = lean_nat_sub(v_i_2970_, v___x_2979_);
lean_dec(v_i_2970_);
v___x_2981_ = l_Lean_instInhabitedExpr;
v___x_2982_ = lean_array_get_borrowed(v___x_2981_, v_revArgs_2967_, v_i_2980_);
lean_inc(v___x_2982_);
v___x_2983_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_b_2969_, v___x_2982_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v_b_2969_ = v_a_2984_;
v_i_2970_ = v_i_2980_;
goto _start;
}
else
{
lean_dec(v_i_2980_);
return v___x_2983_;
}
}
else
{
lean_object* v___x_2986_; 
lean_dec(v_i_2970_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_b_2969_);
return v___x_2986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_revArgs_2987_, lean_object* v_start_2988_, lean_object* v_b_2989_, lean_object* v_i_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2987_, v_start_2988_, v_b_2989_, v_i_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v_start_2988_);
lean_dec_ref(v_revArgs_2987_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(lean_object* v_f_2999_, lean_object* v_revArgs_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = lean_array_get_size(v_revArgs_3000_);
v___x_3015_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_3000_, v___x_3013_, v_f_2999_, v___x_3014_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0___boxed(lean_object* v_f_3016_, lean_object* v_revArgs_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_f_3016_, v_revArgs_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec_ref(v_revArgs_3017_);
return v_res_3030_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__0));
v___x_3033_ = l_Lean_stringToMessageData(v___x_3032_);
return v___x_3033_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__2));
v___x_3036_ = l_Lean_stringToMessageData(v___x_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(lean_object* v_goal_3037_, lean_object* v_info_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3038_);
v___x_3052_ = l_Lean_Expr_getAppFn(v___x_3051_);
if (lean_obj_tag(v___x_3052_) == 8)
{
lean_object* v_declName_3053_; lean_object* v_type_3054_; lean_object* v_value_3055_; lean_object* v_body_3056_; uint8_t v_nondep_3057_; lean_object* v___x_3058_; 
v_declName_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc_n(v_declName_3053_, 2);
v_type_3054_ = lean_ctor_get(v___x_3052_, 1);
lean_inc_ref(v_type_3054_);
v_value_3055_ = lean_ctor_get(v___x_3052_, 2);
lean_inc_ref(v_value_3055_);
v_body_3056_ = lean_ctor_get(v___x_3052_, 3);
lean_inc_ref(v_body_3056_);
v_nondep_3057_ = lean_ctor_get_uint8(v___x_3052_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v___x_3052_, 4);
v___x_3058_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_throwIfUnsupportedJP___redArg(v_declName_3053_, v_value_3055_, v_a_3039_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v_appArgs_3061_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; uint8_t v___x_3115_; 
lean_dec_ref_known(v___x_3058_, 1);
v___x_3059_ = l_Lean_Expr_getAppNumArgs(v___x_3051_);
v___x_3060_ = lean_mk_empty_array_with_capacity(v___x_3059_);
lean_dec(v___x_3059_);
v_appArgs_3061_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3051_, v___x_3060_);
v___x_3115_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable(v_value_3055_);
if (v___x_3115_ == 0)
{
lean_object* v_options_3116_; lean_object* v_inheritedTraceOptions_3117_; uint8_t v_hasTrace_3118_; uint8_t v___x_3119_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; 
v_options_3116_ = lean_ctor_get(v_a_3048_, 2);
v_inheritedTraceOptions_3117_ = lean_ctor_get(v_a_3048_, 13);
v_hasTrace_3118_ = lean_ctor_get_uint8(v_options_3116_, sizeof(void*)*1);
v___x_3119_ = 1;
if (v_hasTrace_3118_ == 0)
{
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
v___y_3131_ = v_a_3049_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3230_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_3231_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_3232_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3117_, v_options_3116_, v___x_3231_);
if (v___x_3232_ == 0)
{
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
v___y_3131_ = v_a_3049_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3233_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3);
lean_inc(v_declName_3053_);
v___x_3234_ = l_Lean_MessageData_ofName(v_declName_3053_);
v___x_3235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3233_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3230_, v___x_3235_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_dec_ref_known(v___x_3236_, 1);
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
v___y_3131_ = v_a_3049_;
goto v___jp_3120_;
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec_ref(v_appArgs_3061_);
lean_dec_ref(v_body_3056_);
lean_dec_ref(v_value_3055_);
lean_dec_ref(v_type_3054_);
lean_dec(v_declName_3053_);
lean_dec_ref(v_info_3038_);
lean_dec(v_goal_3037_);
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
}
v___jp_3120_:
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_body_3056_, v_appArgs_3061_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec_ref(v_appArgs_3061_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v_head_3134_; lean_object* v_args_3135_; lean_object* v_excessArgs_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
v_head_3134_ = lean_ctor_get(v_info_3038_, 0);
lean_inc_ref(v_head_3134_);
v_args_3135_ = lean_ctor_get(v_info_3038_, 1);
lean_inc_ref(v_args_3135_);
v_excessArgs_3136_ = lean_ctor_get(v_info_3038_, 2);
lean_inc_ref(v_excessArgs_3136_);
lean_dec_ref(v_info_3038_);
v___x_3137_ = lean_unsigned_to_nat(7u);
v___x_3138_ = lean_array_set(v_args_3135_, v___x_3137_, v_a_3133_);
v___x_3139_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_head_3134_, v___x_3138_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec_ref(v___x_3138_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v___x_3141_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v_a_3140_, v_excessArgs_3136_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec_ref(v_excessArgs_3136_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3143_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref_known(v___x_3141_, 1);
lean_inc(v_goal_3037_);
v___x_3143_ = l_Lean_MVarId_getType(v_goal_3037_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v_dummy_3145_; lean_object* v_nargs_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc_n(v_a_3144_, 2);
lean_dec_ref_known(v___x_3143_, 1);
v_dummy_3145_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0);
v_nargs_3146_ = l_Lean_Expr_getAppNumArgs(v_a_3144_);
lean_inc(v_nargs_3146_);
v___x_3147_ = lean_mk_array(v_nargs_3146_, v_dummy_3145_);
v___x_3148_ = lean_unsigned_to_nat(1u);
v___x_3149_ = lean_nat_sub(v_nargs_3146_, v___x_3148_);
lean_dec(v_nargs_3146_);
v___x_3150_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3144_, v___x_3147_, v___x_3149_);
v___x_3151_ = l_Lean_Expr_getAppFn(v_a_3144_);
lean_dec(v_a_3144_);
v___x_3152_ = lean_array_get_size(v___x_3150_);
v___x_3153_ = lean_nat_sub(v___x_3152_, v___x_3148_);
v___x_3154_ = lean_array_set(v___x_3150_, v___x_3153_, v_a_3142_);
lean_dec(v___x_3153_);
v___x_3155_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f_spec__0(v___x_3151_, v___x_3154_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec_ref(v___x_3154_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3155_, 1);
v___x_3157_ = l_Lean_Expr_letE___override(v_declName_3053_, v_type_3054_, v_value_3055_, v_a_3156_, v_nondep_3057_);
v___x_3158_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_3037_, v___x_3157_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3160_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0));
v___x_3161_ = l_Lean_Meta_Sym_intros(v_a_3159_, v___x_3160_, v___x_3119_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3173_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3173_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3173_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
if (lean_obj_tag(v_a_3162_) == 1)
{
lean_object* v_mvarId_3166_; lean_object* v___x_3167_; lean_object* v___x_3169_; 
v_mvarId_3166_ = lean_ctor_get(v_a_3162_, 1);
lean_inc(v_mvarId_3166_);
lean_dec_ref_known(v_a_3162_, 2);
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v_mvarId_3166_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v___x_3167_);
v___x_3169_ = v___x_3164_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_del_object(v___x_3164_);
lean_dec(v_a_3162_);
v___x_3171_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1);
v___x_3172_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3171_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
return v___x_3172_;
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
v_a_3174_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3161_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3161_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
v_a_3182_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3158_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3158_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v_value_3055_);
lean_dec_ref(v_type_3054_);
lean_dec(v_declName_3053_);
lean_dec(v_goal_3037_);
v_a_3190_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3155_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3155_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec(v_a_3142_);
lean_dec_ref(v_value_3055_);
lean_dec_ref(v_type_3054_);
lean_dec(v_declName_3053_);
lean_dec(v_goal_3037_);
v_a_3198_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3143_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3143_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec_ref(v_value_3055_);
lean_dec_ref(v_type_3054_);
lean_dec(v_declName_3053_);
lean_dec(v_goal_3037_);
v_a_3206_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3141_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3141_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref(v_excessArgs_3136_);
lean_dec_ref(v_value_3055_);
lean_dec_ref(v_type_3054_);
lean_dec(v_declName_3053_);
lean_dec(v_goal_3037_);
v_a_3214_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3139_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3139_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec_ref(v_value_3055_);
lean_dec_ref(v_type_3054_);
lean_dec(v_declName_3053_);
lean_dec_ref(v_info_3038_);
lean_dec(v_goal_3037_);
v_a_3222_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3132_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3132_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
}
else
{
lean_object* v_options_3245_; uint8_t v_hasTrace_3246_; 
lean_dec_ref(v_type_3054_);
v_options_3245_ = lean_ctor_get(v_a_3048_, 2);
v_hasTrace_3246_ = lean_ctor_get_uint8(v_options_3245_, sizeof(void*)*1);
if (v_hasTrace_3246_ == 0)
{
lean_dec(v_declName_3053_);
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
v___y_3073_ = v_a_3049_;
goto v___jp_3062_;
}
else
{
lean_object* v_inheritedTraceOptions_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v_inheritedTraceOptions_3247_ = lean_ctor_get(v_a_3048_, 13);
v___x_3248_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_3249_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_3250_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3247_, v_options_3245_, v___x_3249_);
if (v___x_3250_ == 0)
{
lean_dec(v_declName_3053_);
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
v___y_3073_ = v_a_3049_;
goto v___jp_3062_;
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3251_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11);
v___x_3252_ = l_Lean_MessageData_ofName(v_declName_3053_);
v___x_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3248_, v___x_3253_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_dec_ref_known(v___x_3254_, 1);
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
v___y_3073_ = v_a_3049_;
goto v___jp_3062_;
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v_appArgs_3061_);
lean_dec_ref(v_body_3056_);
lean_dec_ref(v_value_3055_);
lean_dec_ref(v_info_3038_);
lean_dec(v_goal_3037_);
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
}
v___jp_3062_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3074_ = lean_unsigned_to_nat(1u);
v___x_3075_ = lean_mk_empty_array_with_capacity(v___x_3074_);
v___x_3076_ = lean_array_push(v___x_3075_, v_value_3055_);
v___x_3077_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_3056_, v___x_3076_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3079_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3079_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_a_3078_, v_appArgs_3061_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec_ref(v_appArgs_3061_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3081_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v___x_3081_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3037_, v_info_3038_, v_a_3080_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3090_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3086_, 0, v_a_3082_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3086_);
v___x_3088_ = v___x_3084_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
v_a_3091_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3081_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3081_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref(v_info_3038_);
lean_dec(v_goal_3037_);
v_a_3099_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3079_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3079_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec_ref(v_appArgs_3061_);
lean_dec_ref(v_info_3038_);
lean_dec(v_goal_3037_);
v_a_3107_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3077_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3077_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
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
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref(v_body_3056_);
lean_dec_ref(v_value_3055_);
lean_dec_ref(v_type_3054_);
lean_dec(v_declName_3053_);
lean_dec_ref(v___x_3051_);
lean_dec_ref(v_info_3038_);
lean_dec(v_goal_3037_);
v_a_3263_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3058_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3058_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_dec_ref(v___x_3052_);
lean_dec_ref(v___x_3051_);
lean_dec_ref(v_info_3038_);
lean_dec(v_goal_3037_);
v___x_3271_ = lean_box(0);
v___x_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
return v___x_3272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___boxed(lean_object* v_goal_3273_, lean_object* v_info_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(v_goal_3273_, v_info_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
lean_dec(v_a_3285_);
lean_dec_ref(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_a_3282_);
lean_dec(v_a_3281_);
lean_dec_ref(v_a_3280_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
lean_dec(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0(lean_object* v_revArgs_3288_, lean_object* v_start_3289_, lean_object* v_b_3290_, lean_object* v_i_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_3288_, v_start_3289_, v_b_3290_, v_i_3291_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___boxed(lean_object* v_revArgs_3305_, lean_object* v_start_3306_, lean_object* v_b_3307_, lean_object* v_i_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0(v_revArgs_3305_, v_start_3306_, v_b_3307_, v_i_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v_start_3306_);
lean_dec_ref(v_revArgs_3305_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0(lean_object* v_arg_3322_, lean_object* v___x_3323_, lean_object* v___x_3324_, uint8_t v___x_3325_, lean_object* v_a_3326_, lean_object* v_fn_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v___x_3338_; 
lean_inc_ref(v_arg_3322_);
v___x_3338_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_arg_3322_, v___x_3323_, v___x_3324_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v___x_3340_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3340_, 0, v___x_3325_);
lean_ctor_set_uint8(v___x_3340_, 1, v___x_3325_);
v___x_3341_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_a_3326_, v_fn_3327_, v_arg_3322_, v___x_3340_, v_a_3339_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
return v___x_3341_;
}
else
{
lean_dec_ref(v_fn_3327_);
lean_dec_ref(v_a_3326_);
lean_dec_ref(v_arg_3322_);
return v___x_3338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0___boxed(lean_object* v_arg_3342_, lean_object* v___x_3343_, lean_object* v___x_3344_, lean_object* v___x_3345_, lean_object* v_a_3346_, lean_object* v_fn_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
uint8_t v___x_23412__boxed_3358_; lean_object* v_res_3359_; 
v___x_23412__boxed_3358_ = lean_unbox(v___x_3345_);
v_res_3359_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0(v_arg_3342_, v___x_3343_, v___x_3344_, v___x_23412__boxed_3358_, v_a_3346_, v_fn_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec(v___x_3344_);
lean_dec(v___x_3343_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1(uint8_t v___x_3363_, lean_object* v_goal_3364_, lean_object* v_args_3365_, lean_object* v_excessArgs_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
if (v___x_3363_ == 0)
{
lean_object* v_hypSimpMethods_3379_; 
v_hypSimpMethods_3379_ = lean_ctor_get(v___y_3367_, 2);
if (lean_obj_tag(v_hypSimpMethods_3379_) == 1)
{
lean_object* v_val_3380_; lean_object* v___x_3381_; 
v_val_3380_ = lean_ctor_get(v_hypSimpMethods_3379_, 0);
lean_inc(v_goal_3364_);
v___x_3381_ = l_Lean_MVarId_getType(v_goal_3364_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3472_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3472_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3472_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
if (lean_obj_tag(v_a_3382_) == 5)
{
lean_object* v_fn_3386_; lean_object* v_arg_3387_; lean_object* v___x_3388_; lean_object* v_simpState_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___f_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
lean_del_object(v___x_3384_);
v_fn_3386_ = lean_ctor_get(v_a_3382_, 0);
lean_inc_ref(v_fn_3386_);
v_arg_3387_ = lean_ctor_get(v_a_3382_, 1);
lean_inc_ref(v_arg_3387_);
v___x_3388_ = lean_st_ref_get(v___y_3368_);
v_simpState_3389_ = lean_ctor_get(v___x_3388_, 7);
lean_inc_ref(v_simpState_3389_);
lean_dec(v___x_3388_);
v___x_3390_ = lean_array_get_size(v_args_3365_);
v___x_3391_ = lean_array_get_size(v_excessArgs_3366_);
v___x_3392_ = lean_nat_add(v___x_3390_, v___x_3391_);
v___x_3393_ = lean_box(v___x_3363_);
v___f_3394_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3394_, 0, v_arg_3387_);
lean_closure_set(v___f_3394_, 1, v___x_3390_);
lean_closure_set(v___f_3394_, 2, v___x_3392_);
lean_closure_set(v___f_3394_, 3, v___x_3393_);
lean_closure_set(v___f_3394_, 4, v_a_3382_);
lean_closure_set(v___f_3394_, 5, v_fn_3386_);
v___x_3395_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___closed__0));
lean_inc(v_val_3380_);
v___x_3396_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___f_3394_, v_val_3380_, v___x_3395_, v_simpState_3389_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v_fst_3398_; lean_object* v_snd_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3459_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3396_, 1);
v_fst_3398_ = lean_ctor_get(v_a_3397_, 0);
v_snd_3399_ = lean_ctor_get(v_a_3397_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_a_3397_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3401_ = v_a_3397_;
v_isShared_3402_ = v_isSharedCheck_3459_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_snd_3399_);
lean_inc(v_fst_3398_);
lean_dec(v_a_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3459_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v_specBackwardRuleCache_3404_; lean_object* v_splitBackwardRuleCache_3405_; lean_object* v_latticeBackwardRuleCache_3406_; lean_object* v_frameBackwardRuleCache_3407_; lean_object* v_frameDB_3408_; lean_object* v_invariants_3409_; lean_object* v_vcs_3410_; lean_object* v_fuel_3411_; lean_object* v_inlineHandledInvariants_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3457_; 
v___x_3403_ = lean_st_ref_take(v___y_3368_);
v_specBackwardRuleCache_3404_ = lean_ctor_get(v___x_3403_, 0);
v_splitBackwardRuleCache_3405_ = lean_ctor_get(v___x_3403_, 1);
v_latticeBackwardRuleCache_3406_ = lean_ctor_get(v___x_3403_, 2);
v_frameBackwardRuleCache_3407_ = lean_ctor_get(v___x_3403_, 3);
v_frameDB_3408_ = lean_ctor_get(v___x_3403_, 4);
v_invariants_3409_ = lean_ctor_get(v___x_3403_, 5);
v_vcs_3410_ = lean_ctor_get(v___x_3403_, 6);
v_fuel_3411_ = lean_ctor_get(v___x_3403_, 8);
v_inlineHandledInvariants_3412_ = lean_ctor_get(v___x_3403_, 9);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3457_ == 0)
{
lean_object* v_unused_3458_; 
v_unused_3458_ = lean_ctor_get(v___x_3403_, 7);
lean_dec(v_unused_3458_);
v___x_3414_ = v___x_3403_;
v_isShared_3415_ = v_isSharedCheck_3457_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_inlineHandledInvariants_3412_);
lean_inc(v_fuel_3411_);
lean_inc(v_vcs_3410_);
lean_inc(v_invariants_3409_);
lean_inc(v_frameDB_3408_);
lean_inc(v_frameBackwardRuleCache_3407_);
lean_inc(v_latticeBackwardRuleCache_3406_);
lean_inc(v_splitBackwardRuleCache_3405_);
lean_inc(v_specBackwardRuleCache_3404_);
lean_dec(v___x_3403_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3457_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 7, v_snd_3399_);
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_specBackwardRuleCache_3404_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_splitBackwardRuleCache_3405_);
lean_ctor_set(v_reuseFailAlloc_3456_, 2, v_latticeBackwardRuleCache_3406_);
lean_ctor_set(v_reuseFailAlloc_3456_, 3, v_frameBackwardRuleCache_3407_);
lean_ctor_set(v_reuseFailAlloc_3456_, 4, v_frameDB_3408_);
lean_ctor_set(v_reuseFailAlloc_3456_, 5, v_invariants_3409_);
lean_ctor_set(v_reuseFailAlloc_3456_, 6, v_vcs_3410_);
lean_ctor_set(v_reuseFailAlloc_3456_, 7, v_snd_3399_);
lean_ctor_set(v_reuseFailAlloc_3456_, 8, v_fuel_3411_);
lean_ctor_set(v_reuseFailAlloc_3456_, 9, v_inlineHandledInvariants_3412_);
v___x_3417_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = lean_st_ref_put(v___y_3368_, v___x_3417_);
v___x_3419_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_3398_, v_goal_3364_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3447_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3422_ = v___x_3419_;
v_isShared_3423_ = v_isSharedCheck_3447_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3447_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
switch(lean_obj_tag(v_a_3420_))
{
case 0:
{
lean_object* v___x_3424_; lean_object* v___x_3426_; 
lean_del_object(v___x_3401_);
v___x_3424_ = lean_box(0);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3424_);
v___x_3426_ = v___x_3422_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
case 1:
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
lean_del_object(v___x_3401_);
v___x_3428_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3428_);
v___x_3430_ = v___x_3422_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
default: 
{
lean_object* v_mvarId_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3446_; 
v_mvarId_3432_ = lean_ctor_get(v_a_3420_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_a_3420_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3434_ = v_a_3420_;
v_isShared_3435_ = v_isSharedCheck_3446_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_mvarId_3432_);
lean_dec(v_a_3420_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3446_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3436_ = lean_box(0);
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 1);
lean_ctor_set(v___x_3401_, 1, v___x_3436_);
lean_ctor_set(v___x_3401_, 0, v_mvarId_3432_);
v___x_3438_ = v___x_3401_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_mvarId_3432_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3440_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 1);
lean_ctor_set(v___x_3434_, 0, v___x_3438_);
v___x_3440_ = v___x_3434_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3442_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3440_);
v___x_3442_ = v___x_3422_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
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
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_del_object(v___x_3401_);
v_a_3448_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3419_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3419_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
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
}
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec(v_goal_3364_);
v_a_3460_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3396_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3396_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3470_; 
lean_dec(v_a_3382_);
lean_dec(v_goal_3364_);
v___x_3468_ = lean_box(0);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3468_);
v___x_3470_ = v___x_3384_;
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
lean_dec(v_goal_3364_);
v_a_3473_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3381_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3381_);
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
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
lean_dec(v_goal_3364_);
v___x_3481_ = lean_box(0);
v___x_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
return v___x_3482_;
}
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_dec(v_goal_3364_);
v___x_3483_ = lean_box(0);
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
return v___x_3484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___boxed(lean_object* v___x_3485_, lean_object* v_goal_3486_, lean_object* v_args_3487_, lean_object* v_excessArgs_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
uint8_t v___x_23474__boxed_3501_; lean_object* v_res_3502_; 
v___x_23474__boxed_3501_ = lean_unbox(v___x_3485_);
v_res_3502_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1(v___x_23474__boxed_3501_, v_goal_3486_, v_args_3487_, v_excessArgs_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec_ref(v_excessArgs_3488_);
lean_dec_ref(v_args_3487_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(lean_object* v_goal_3503_, lean_object* v_info_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v_args_3517_; lean_object* v_excessArgs_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___y_3523_; lean_object* v___x_3524_; 
v_args_3517_ = lean_ctor_get(v_info_3504_, 1);
lean_inc_ref(v_args_3517_);
v_excessArgs_3518_ = lean_ctor_get(v_info_3504_, 2);
lean_inc_ref(v_excessArgs_3518_);
lean_dec_ref(v_info_3504_);
v___x_3519_ = lean_array_get_size(v_excessArgs_3518_);
v___x_3520_ = lean_unsigned_to_nat(0u);
v___x_3521_ = lean_nat_dec_eq(v___x_3519_, v___x_3520_);
v___x_3522_ = lean_box(v___x_3521_);
lean_inc(v_goal_3503_);
v___y_3523_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___boxed), 16, 4);
lean_closure_set(v___y_3523_, 0, v___x_3522_);
lean_closure_set(v___y_3523_, 1, v_goal_3503_);
lean_closure_set(v___y_3523_, 2, v_args_3517_);
lean_closure_set(v___y_3523_, 3, v_excessArgs_3518_);
v___x_3524_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_3503_, v___y_3523_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___boxed(lean_object* v_goal_3525_, lean_object* v_info_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(v_goal_3525_, v_info_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(lean_object* v_as_x27_3540_, lean_object* v_b_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
if (lean_obj_tag(v_as_x27_3540_) == 0)
{
lean_object* v___x_3551_; 
v___x_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3551_, 0, v_b_3541_);
return v___x_3551_;
}
else
{
lean_object* v_head_3552_; lean_object* v_tail_3553_; lean_object* v___x_3554_; 
v_head_3552_ = lean_ctor_get(v_as_x27_3540_, 0);
v_tail_3553_ = lean_ctor_get(v_as_x27_3540_, 1);
lean_inc(v_head_3552_);
v___x_3554_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_head_3552_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3554_, 1);
switch(lean_obj_tag(v_a_3555_))
{
case 0:
{
lean_object* v___x_3556_; 
lean_inc(v_head_3552_);
v___x_3556_ = lean_array_push(v_b_3541_, v_head_3552_);
v_as_x27_3540_ = v_tail_3553_;
v_b_3541_ = v___x_3556_;
goto _start;
}
case 1:
{
v_as_x27_3540_ = v_tail_3553_;
goto _start;
}
default: 
{
lean_object* v_mvarId_3559_; lean_object* v___x_3560_; 
v_mvarId_3559_ = lean_ctor_get(v_a_3555_, 0);
lean_inc(v_mvarId_3559_);
lean_dec_ref_known(v_a_3555_, 1);
v___x_3560_ = lean_array_push(v_b_3541_, v_mvarId_3559_);
v_as_x27_3540_ = v_tail_3553_;
v_b_3541_ = v___x_3560_;
goto _start;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec_ref(v_b_3541_);
v_a_3562_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3554_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3554_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg___boxed(lean_object* v_as_x27_3570_, lean_object* v_b_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3570_, v_b_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v_as_x27_3570_);
return v_res_3581_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__0));
v___x_3584_ = l_Lean_stringToMessageData(v___x_3583_);
return v___x_3584_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__2));
v___x_3587_ = l_Lean_stringToMessageData(v___x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(lean_object* v_goal_3588_, lean_object* v_info_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3589_);
lean_inc_ref(v___x_3602_);
v___x_3603_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v___x_3602_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3746_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3606_ = v___x_3603_;
v_isShared_3607_ = v_isSharedCheck_3746_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3603_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3746_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
if (lean_obj_tag(v_a_3604_) == 1)
{
lean_object* v_val_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3741_; 
lean_del_object(v___x_3606_);
v_val_3608_ = lean_ctor_get(v_a_3604_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v_a_3604_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3610_ = v_a_3604_;
v_isShared_3611_ = v_isSharedCheck_3741_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_val_3608_);
lean_dec(v_a_3604_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3741_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; 
if (lean_obj_tag(v_val_3608_) == 3)
{
lean_object* v_keyedConfig_3680_; uint8_t v_trackZetaDelta_3681_; lean_object* v_zetaDeltaSet_3682_; lean_object* v_lctx_3683_; lean_object* v_localInstances_3684_; lean_object* v_defEqCtx_x3f_3685_; lean_object* v_synthPendingDepth_3686_; lean_object* v_customCanUnfoldPredicate_x3f_3687_; uint8_t v_univApprox_3688_; uint8_t v_inTypeClassResolution_3689_; uint8_t v_cacheInferType_3690_; uint8_t v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_keyedConfig_3680_ = lean_ctor_get(v_a_3597_, 0);
v_trackZetaDelta_3681_ = lean_ctor_get_uint8(v_a_3597_, sizeof(void*)*7);
v_zetaDeltaSet_3682_ = lean_ctor_get(v_a_3597_, 1);
v_lctx_3683_ = lean_ctor_get(v_a_3597_, 2);
v_localInstances_3684_ = lean_ctor_get(v_a_3597_, 3);
v_defEqCtx_x3f_3685_ = lean_ctor_get(v_a_3597_, 4);
v_synthPendingDepth_3686_ = lean_ctor_get(v_a_3597_, 5);
v_customCanUnfoldPredicate_x3f_3687_ = lean_ctor_get(v_a_3597_, 6);
v_univApprox_3688_ = lean_ctor_get_uint8(v_a_3597_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3689_ = lean_ctor_get_uint8(v_a_3597_, sizeof(void*)*7 + 2);
v_cacheInferType_3690_ = lean_ctor_get_uint8(v_a_3597_, sizeof(void*)*7 + 3);
v___x_3691_ = 2;
lean_inc_ref(v_keyedConfig_3680_);
v___x_3692_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3691_, v_keyedConfig_3680_);
lean_inc(v_customCanUnfoldPredicate_x3f_3687_);
lean_inc(v_synthPendingDepth_3686_);
lean_inc(v_defEqCtx_x3f_3685_);
lean_inc_ref(v_localInstances_3684_);
lean_inc_ref(v_lctx_3683_);
lean_inc(v_zetaDeltaSet_3682_);
v___x_3693_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
lean_ctor_set(v___x_3693_, 1, v_zetaDeltaSet_3682_);
lean_ctor_set(v___x_3693_, 2, v_lctx_3683_);
lean_ctor_set(v___x_3693_, 3, v_localInstances_3684_);
lean_ctor_set(v___x_3693_, 4, v_defEqCtx_x3f_3685_);
lean_ctor_set(v___x_3693_, 5, v_synthPendingDepth_3686_);
lean_ctor_set(v___x_3693_, 6, v_customCanUnfoldPredicate_x3f_3687_);
lean_ctor_set_uint8(v___x_3693_, sizeof(void*)*7, v_trackZetaDelta_3681_);
lean_ctor_set_uint8(v___x_3693_, sizeof(void*)*7 + 1, v_univApprox_3688_);
lean_ctor_set_uint8(v___x_3693_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3689_);
lean_ctor_set_uint8(v___x_3693_, sizeof(void*)*7 + 3, v_cacheInferType_3690_);
v___x_3694_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_3602_, v___x_3693_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec_ref_known(v___x_3693_, 7);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3694_, 1);
if (lean_obj_tag(v_a_3695_) == 1)
{
lean_object* v_val_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3732_; 
lean_dec_ref_known(v_val_3608_, 1);
lean_del_object(v___x_3610_);
lean_dec_ref(v___x_3602_);
v_val_3696_ = lean_ctor_get(v_a_3695_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v_a_3695_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3698_ = v_a_3695_;
v_isShared_3699_ = v_isSharedCheck_3732_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_val_3696_);
lean_dec(v_a_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3732_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_Meta_Sym_shareCommonInc(v_val_3696_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3702_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
v___x_3702_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3588_, v_info_3589_, v_a_3701_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3715_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3705_ = v___x_3702_;
v_isShared_3706_ = v_isSharedCheck_3715_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3702_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3715_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3710_; 
v___x_3707_ = lean_box(0);
v___x_3708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3708_, 0, v_a_3703_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3708_);
v___x_3710_ = v___x_3698_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3712_; 
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v___x_3710_);
v___x_3712_ = v___x_3705_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3710_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_del_object(v___x_3698_);
v_a_3716_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3702_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3702_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_del_object(v___x_3698_);
lean_dec_ref(v_info_3589_);
lean_dec(v_goal_3588_);
v_a_3724_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3700_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3700_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
else
{
lean_dec(v_a_3695_);
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
v___y_3623_ = v_a_3600_;
goto v___jp_3612_;
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec_ref_known(v_val_3608_, 1);
lean_del_object(v___x_3610_);
lean_dec_ref(v___x_3602_);
lean_dec_ref(v_info_3589_);
lean_dec(v_goal_3588_);
v_a_3733_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3694_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3694_);
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
else
{
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
v___y_3623_ = v_a_3600_;
goto v___jp_3612_;
}
v___jp_3612_:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_val_3608_, v_info_3589_, v___y_3614_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3630_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
v___x_3626_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1);
v___x_3627_ = l_Lean_indentExpr(v___x_3602_);
lean_inc_ref(v___x_3627_);
v___x_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3626_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3628_);
v___x_3630_ = v___x_3610_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_3625_, v_goal_3588_, v___x_3630_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_a_3632_);
lean_dec_ref_known(v___x_3631_, 1);
if (lean_obj_tag(v_a_3632_) == 1)
{
lean_object* v_mvarIds_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3659_; 
lean_dec_ref(v___x_3627_);
v_mvarIds_3633_ = lean_ctor_get(v_a_3632_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_a_3632_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3635_ = v_a_3632_;
v_isShared_3636_ = v_isSharedCheck_3659_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_mvarIds_3633_);
lean_dec(v_a_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3659_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0));
v___x_3638_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_mvarIds_3633_, v___x_3637_, v___y_3613_, v___y_3614_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
lean_dec(v_mvarIds_3633_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3650_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3650_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3650_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; lean_object* v___x_3645_; 
v___x_3643_ = lean_array_to_list(v_a_3639_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3643_);
v___x_3645_ = v___x_3635_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3647_; 
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3645_);
v___x_3647_ = v___x_3641_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
lean_del_object(v___x_3635_);
v_a_3651_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3638_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3638_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
}
else
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
lean_dec(v_a_3632_);
v___x_3660_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3);
v___x_3661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v___x_3627_);
v___x_3662_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3661_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
return v___x_3662_;
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec_ref(v___x_3627_);
v_a_3663_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3631_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3631_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_del_object(v___x_3610_);
lean_dec_ref(v___x_3602_);
lean_dec(v_goal_3588_);
v_a_3672_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3624_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3624_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
}
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3744_; 
lean_dec(v_a_3604_);
lean_dec_ref(v___x_3602_);
lean_dec_ref(v_info_3589_);
lean_dec(v_goal_3588_);
v___x_3742_ = lean_box(0);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v___x_3742_);
v___x_3744_ = v___x_3606_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3742_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec_ref(v___x_3602_);
lean_dec_ref(v_info_3589_);
lean_dec(v_goal_3588_);
v_a_3747_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3603_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3603_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___boxed(lean_object* v_goal_3755_, lean_object* v_info_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(v_goal_3755_, v_info_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec(v_a_3763_);
lean_dec_ref(v_a_3762_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
lean_dec(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0(lean_object* v_as_3770_, lean_object* v_as_x27_3771_, lean_object* v_b_3772_, lean_object* v_a_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3771_, v_b_3772_, v___y_3774_, v___y_3775_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___boxed(lean_object* v_as_3787_, lean_object* v_as_x27_3788_, lean_object* v_b_3789_, lean_object* v_a_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0(v_as_3787_, v_as_x27_3788_, v_b_3789_, v_a_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v_as_x27_3788_);
lean_dec(v_as_3787_);
return v_res_3803_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1(void){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__0));
v___x_3806_ = l_Lean_stringToMessageData(v___x_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(lean_object* v_goal_3807_, lean_object* v_info_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v___x_3821_; lean_object* v_f_3822_; lean_object* v___x_3823_; 
v___x_3821_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3808_);
v_f_3822_ = l_Lean_Expr_getAppFn(v___x_3821_);
v___x_3823_ = l_Lean_Expr_fvarId_x3f(v_f_3822_);
lean_dec_ref(v_f_3822_);
if (lean_obj_tag(v___x_3823_) == 1)
{
lean_object* v_val_3824_; uint8_t v___x_3825_; lean_object* v___x_3826_; 
v_val_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc_n(v_val_3824_, 2);
lean_dec_ref_known(v___x_3823_, 1);
v___x_3825_ = 0;
v___x_3826_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_3824_, v___x_3825_, v_a_3816_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3914_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3829_ = v___x_3826_;
v_isShared_3830_ = v_isSharedCheck_3914_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3826_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3914_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
if (lean_obj_tag(v_a_3827_) == 1)
{
lean_object* v_val_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3909_; 
lean_del_object(v___x_3829_);
v_val_3831_ = lean_ctor_get(v_a_3827_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_a_3827_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3833_ = v_a_3827_;
v_isShared_3834_ = v_isSharedCheck_3909_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_val_3831_);
lean_dec(v_a_3827_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3909_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v_options_3881_; uint8_t v_hasTrace_3882_; 
v_options_3881_ = lean_ctor_get(v_a_3818_, 2);
v_hasTrace_3882_ = lean_ctor_get_uint8(v_options_3881_, sizeof(void*)*1);
if (v_hasTrace_3882_ == 0)
{
lean_dec(v_val_3824_);
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
v___y_3846_ = v_a_3819_;
goto v___jp_3835_;
}
else
{
lean_object* v_inheritedTraceOptions_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; uint8_t v___x_3886_; 
v_inheritedTraceOptions_3883_ = lean_ctor_get(v_a_3818_, 13);
v___x_3884_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_3885_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_3886_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3883_, v_options_3881_, v___x_3885_);
if (v___x_3886_ == 0)
{
lean_dec(v_val_3824_);
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
v___y_3846_ = v_a_3819_;
goto v___jp_3835_;
}
else
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Lean_FVarId_getUserName___redArg(v_val_3824_, v_a_3816_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
v___x_3889_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1);
v___x_3890_ = l_Lean_MessageData_ofName(v_a_3888_);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3884_, v___x_3891_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_dec_ref_known(v___x_3892_, 1);
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
v___y_3846_ = v_a_3819_;
goto v___jp_3835_;
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_del_object(v___x_3833_);
lean_dec(v_val_3831_);
lean_dec_ref(v___x_3821_);
lean_dec_ref(v_info_3808_);
lean_dec(v_goal_3807_);
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_del_object(v___x_3833_);
lean_dec(v_val_3831_);
lean_dec_ref(v___x_3821_);
lean_dec_ref(v_info_3808_);
lean_dec(v_goal_3807_);
v_a_3901_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3887_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3887_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
v___jp_3835_:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3847_ = l_Lean_Expr_getAppNumArgs(v___x_3821_);
v___x_3848_ = lean_mk_empty_array_with_capacity(v___x_3847_);
lean_dec(v___x_3847_);
v___x_3849_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3821_, v___x_3848_);
v___x_3850_ = l_Lean_Expr_betaRev(v_val_3831_, v___x_3849_, v___x_3825_, v___x_3825_);
lean_dec_ref(v___x_3849_);
v___x_3851_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3850_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3853_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3851_, 1);
v___x_3853_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3807_, v_info_3808_, v_a_3852_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3864_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3856_ = v___x_3853_;
v_isShared_3857_ = v_isSharedCheck_3864_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3853_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3864_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v_a_3854_);
v___x_3859_ = v___x_3833_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3861_; 
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v___x_3859_);
v___x_3861_ = v___x_3856_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
lean_del_object(v___x_3833_);
v_a_3865_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3853_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3853_);
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
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_del_object(v___x_3833_);
lean_dec_ref(v_info_3808_);
lean_dec(v_goal_3807_);
v_a_3873_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3851_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3851_);
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
}
else
{
lean_object* v___x_3910_; lean_object* v___x_3912_; 
lean_dec(v_a_3827_);
lean_dec(v_val_3824_);
lean_dec_ref(v___x_3821_);
lean_dec_ref(v_info_3808_);
lean_dec(v_goal_3807_);
v___x_3910_ = lean_box(0);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 0, v___x_3910_);
v___x_3912_ = v___x_3829_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v_val_3824_);
lean_dec_ref(v___x_3821_);
lean_dec_ref(v_info_3808_);
lean_dec(v_goal_3807_);
v_a_3915_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3826_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3826_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
else
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
lean_dec(v___x_3823_);
lean_dec_ref(v___x_3821_);
lean_dec_ref(v_info_3808_);
lean_dec(v_goal_3807_);
v___x_3923_ = lean_box(0);
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___boxed(lean_object* v_goal_3925_, lean_object* v_info_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(v_goal_3925_, v_info_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_);
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3936_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f(lean_object* v_goal_3940_, lean_object* v_info_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v___x_3954_; lean_object* v_a_3956_; lean_object* v_f_4017_; 
v___x_3954_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3941_);
v_f_4017_ = l_Lean_Expr_getAppFn(v___x_3954_);
if (lean_obj_tag(v_f_4017_) == 11)
{
lean_object* v_keyedConfig_4018_; uint8_t v_trackZetaDelta_4019_; lean_object* v_zetaDeltaSet_4020_; lean_object* v_lctx_4021_; lean_object* v_localInstances_4022_; lean_object* v_defEqCtx_x3f_4023_; lean_object* v_synthPendingDepth_4024_; lean_object* v_customCanUnfoldPredicate_x3f_4025_; uint8_t v_univApprox_4026_; uint8_t v_inTypeClassResolution_4027_; uint8_t v_cacheInferType_4028_; uint8_t v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_keyedConfig_4018_ = lean_ctor_get(v_a_3949_, 0);
v_trackZetaDelta_4019_ = lean_ctor_get_uint8(v_a_3949_, sizeof(void*)*7);
v_zetaDeltaSet_4020_ = lean_ctor_get(v_a_3949_, 1);
v_lctx_4021_ = lean_ctor_get(v_a_3949_, 2);
v_localInstances_4022_ = lean_ctor_get(v_a_3949_, 3);
v_defEqCtx_x3f_4023_ = lean_ctor_get(v_a_3949_, 4);
v_synthPendingDepth_4024_ = lean_ctor_get(v_a_3949_, 5);
v_customCanUnfoldPredicate_x3f_4025_ = lean_ctor_get(v_a_3949_, 6);
v_univApprox_4026_ = lean_ctor_get_uint8(v_a_3949_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4027_ = lean_ctor_get_uint8(v_a_3949_, sizeof(void*)*7 + 2);
v_cacheInferType_4028_ = lean_ctor_get_uint8(v_a_3949_, sizeof(void*)*7 + 3);
v___x_4029_ = 3;
lean_inc_ref(v_keyedConfig_4018_);
v___x_4030_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4029_, v_keyedConfig_4018_);
lean_inc(v_customCanUnfoldPredicate_x3f_4025_);
lean_inc(v_synthPendingDepth_4024_);
lean_inc(v_defEqCtx_x3f_4023_);
lean_inc_ref(v_localInstances_4022_);
lean_inc_ref(v_lctx_4021_);
lean_inc(v_zetaDeltaSet_4020_);
v___x_4031_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
lean_ctor_set(v___x_4031_, 1, v_zetaDeltaSet_4020_);
lean_ctor_set(v___x_4031_, 2, v_lctx_4021_);
lean_ctor_set(v___x_4031_, 3, v_localInstances_4022_);
lean_ctor_set(v___x_4031_, 4, v_defEqCtx_x3f_4023_);
lean_ctor_set(v___x_4031_, 5, v_synthPendingDepth_4024_);
lean_ctor_set(v___x_4031_, 6, v_customCanUnfoldPredicate_x3f_4025_);
lean_ctor_set_uint8(v___x_4031_, sizeof(void*)*7, v_trackZetaDelta_4019_);
lean_ctor_set_uint8(v___x_4031_, sizeof(void*)*7 + 1, v_univApprox_4026_);
lean_ctor_set_uint8(v___x_4031_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4027_);
lean_ctor_set_uint8(v___x_4031_, sizeof(void*)*7 + 3, v_cacheInferType_4028_);
v___x_4032_ = l_Lean_Meta_reduceProj_x3f(v_f_4017_, v___x_4031_, v_a_3950_, v_a_3951_, v_a_3952_);
lean_dec_ref_known(v___x_4031_, 7);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4032_, 1);
v_a_3956_ = v_a_4033_;
goto v___jp_3955_;
}
else
{
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4034_; 
v_a_4034_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4032_, 1);
v_a_3956_ = v_a_4034_;
goto v___jp_3955_;
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
lean_dec_ref(v___x_3954_);
lean_dec_ref(v_info_3941_);
lean_dec(v_goal_3940_);
v_a_4035_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4032_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4032_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
}
else
{
lean_object* v___x_4043_; lean_object* v___x_4044_; 
lean_dec_ref(v_f_4017_);
lean_dec_ref(v___x_3954_);
lean_dec_ref(v_info_3941_);
lean_dec(v_goal_3940_);
v___x_4043_ = lean_box(0);
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
return v___x_4044_;
}
v___jp_3955_:
{
if (lean_obj_tag(v_a_3956_) == 1)
{
lean_object* v_val_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_4014_; 
v_val_3957_ = lean_ctor_get(v_a_3956_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_a_3956_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_3959_ = v_a_3956_;
v_isShared_3960_ = v_isSharedCheck_4014_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_val_3957_);
lean_dec(v_a_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_4014_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3961_; 
v___x_3961_ = l_Lean_Meta_Sym_unfoldReducible(v_val_3957_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v___x_3963_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3961_, 1);
v___x_3963_ = l_Lean_Meta_Sym_shareCommon(v_a_3962_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3965_ = l_Lean_Expr_getAppNumArgs(v___x_3954_);
v___x_3966_ = lean_mk_empty_array_with_capacity(v___x_3965_);
lean_dec(v___x_3965_);
v___x_3967_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3954_, v___x_3966_);
v___x_3968_ = l_Lean_Meta_Sym_betaRevS(v_a_3964_, v___x_3967_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3970_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref_known(v___x_3968_, 1);
v___x_3970_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3940_, v_info_3941_, v_a_3969_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3981_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3973_ = v___x_3970_;
v_isShared_3974_ = v_isSharedCheck_3981_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3981_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v_a_3971_);
v___x_3976_ = v___x_3959_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3978_; 
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 0, v___x_3976_);
v___x_3978_ = v___x_3973_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_del_object(v___x_3959_);
v_a_3982_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3970_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3970_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_del_object(v___x_3959_);
lean_dec_ref(v_info_3941_);
lean_dec(v_goal_3940_);
v_a_3990_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3968_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3968_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_del_object(v___x_3959_);
lean_dec_ref(v___x_3954_);
lean_dec_ref(v_info_3941_);
lean_dec(v_goal_3940_);
v_a_3998_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3963_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3963_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_del_object(v___x_3959_);
lean_dec_ref(v___x_3954_);
lean_dec_ref(v_info_3941_);
lean_dec(v_goal_3940_);
v_a_4006_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3961_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3961_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
else
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_dec(v_a_3956_);
lean_dec_ref(v___x_3954_);
lean_dec_ref(v_info_3941_);
lean_dec(v_goal_3940_);
v___x_4015_ = lean_box(0);
v___x_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
return v___x_4016_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f___boxed(lean_object* v_goal_4045_, lean_object* v_info_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f(v_goal_4045_, v_info_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
return v_res_4059_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0));
v___x_4062_ = l_Lean_stringToMessageData(v___x_4061_);
return v___x_4062_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3(void){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2));
v___x_4065_ = l_Lean_stringToMessageData(v___x_4064_);
return v___x_4065_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4067_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4));
v___x_4068_ = l_Lean_stringToMessageData(v___x_4067_);
return v___x_4068_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6));
v___x_4071_ = l_Lean_stringToMessageData(v___x_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
if (lean_obj_tag(v_a_4072_) == 0)
{
lean_object* v___x_4074_; 
v___x_4074_ = l_List_reverse___redArg(v_a_4073_);
return v___x_4074_;
}
else
{
lean_object* v_head_4075_; lean_object* v_tail_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4104_; 
v_head_4075_ = lean_ctor_get(v_a_4072_, 0);
v_tail_4076_ = lean_ctor_get(v_a_4072_, 1);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_a_4072_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4078_ = v_a_4072_;
v_isShared_4079_ = v_isSharedCheck_4104_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_tail_4076_);
lean_inc(v_head_4075_);
lean_dec(v_a_4072_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4104_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___y_4081_; 
switch(lean_obj_tag(v_head_4075_))
{
case 0:
{
lean_object* v_declName_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v_declName_4086_ = lean_ctor_get(v_head_4075_, 0);
lean_inc(v_declName_4086_);
lean_dec_ref_known(v_head_4075_, 1);
v___x_4087_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_4088_ = l_Lean_MessageData_ofName(v_declName_4086_);
v___x_4089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4087_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___y_4081_ = v___x_4089_;
goto v___jp_4080_;
}
case 1:
{
lean_object* v_fvarId_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_fvarId_4090_ = lean_ctor_get(v_head_4075_, 0);
lean_inc(v_fvarId_4090_);
lean_dec_ref_known(v_head_4075_, 1);
v___x_4091_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_4092_ = l_Lean_mkFVar(v_fvarId_4090_);
v___x_4093_ = l_Lean_MessageData_ofExpr(v___x_4092_);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4091_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___y_4081_ = v___x_4094_;
goto v___jp_4080_;
}
default: 
{
lean_object* v_ref_4095_; lean_object* v_proof_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v_ref_4095_ = lean_ctor_get(v_head_4075_, 1);
lean_inc(v_ref_4095_);
v_proof_4096_ = lean_ctor_get(v_head_4075_, 2);
lean_inc_ref(v_proof_4096_);
lean_dec_ref_known(v_head_4075_, 3);
v___x_4097_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_4098_ = l_Lean_MessageData_ofSyntax(v_ref_4095_);
v___x_4099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4097_);
lean_ctor_set(v___x_4099_, 1, v___x_4098_);
v___x_4100_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_4101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4099_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = l_Lean_MessageData_ofExpr(v_proof_4096_);
v___x_4103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4101_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
v___y_4081_ = v___x_4103_;
goto v___jp_4080_;
}
}
v___jp_4080_:
{
lean_object* v___x_4083_; 
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 1, v_a_4073_);
lean_ctor_set(v___x_4078_, 0, v___y_4081_);
v___x_4083_ = v___x_4078_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___y_4081_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_a_4073_);
v___x_4083_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
v_a_4072_ = v_tail_4076_;
v_a_4073_ = v___x_4083_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t v_sz_4105_, size_t v_i_4106_, lean_object* v_bs_4107_){
_start:
{
uint8_t v___x_4108_; 
v___x_4108_ = lean_usize_dec_lt(v_i_4106_, v_sz_4105_);
if (v___x_4108_ == 0)
{
return v_bs_4107_;
}
else
{
lean_object* v_v_4109_; lean_object* v_proof_4110_; lean_object* v___x_4111_; lean_object* v_bs_x27_4112_; size_t v___x_4113_; size_t v___x_4114_; lean_object* v___x_4115_; 
v_v_4109_ = lean_array_uget_borrowed(v_bs_4107_, v_i_4106_);
v_proof_4110_ = lean_ctor_get(v_v_4109_, 1);
lean_inc_ref(v_proof_4110_);
v___x_4111_ = lean_unsigned_to_nat(0u);
v_bs_x27_4112_ = lean_array_uset(v_bs_4107_, v_i_4106_, v___x_4111_);
v___x_4113_ = ((size_t)1ULL);
v___x_4114_ = lean_usize_add(v_i_4106_, v___x_4113_);
v___x_4115_ = lean_array_uset(v_bs_x27_4112_, v_i_4106_, v_proof_4110_);
v_i_4106_ = v___x_4114_;
v_bs_4107_ = v___x_4115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object* v_sz_4117_, lean_object* v_i_4118_, lean_object* v_bs_4119_){
_start:
{
size_t v_sz_boxed_4120_; size_t v_i_boxed_4121_; lean_object* v_res_4122_; 
v_sz_boxed_4120_ = lean_unbox_usize(v_sz_4117_);
lean_dec(v_sz_4117_);
v_i_boxed_4121_ = lean_unbox_usize(v_i_4118_);
lean_dec(v_i_4118_);
v_res_4122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_boxed_4120_, v_i_boxed_4121_, v_bs_4119_);
return v_res_4122_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1(void){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0));
v___x_4125_ = l_Lean_stringToMessageData(v___x_4124_);
return v___x_4125_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3(void){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2));
v___x_4128_ = l_Lean_stringToMessageData(v___x_4127_);
return v___x_4128_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4));
v___x_4131_ = l_Lean_stringToMessageData(v___x_4130_);
return v___x_4131_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4133_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6));
v___x_4134_ = l_Lean_stringToMessageData(v___x_4133_);
return v___x_4134_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8));
v___x_4137_ = l_Lean_stringToMessageData(v___x_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object* v_prog_4138_, lean_object* v_monad_4139_, lean_object* v_thms_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
uint8_t v_errorOnMissingSpec_4147_; 
v_errorOnMissingSpec_4147_ = lean_ctor_get_uint8(v_a_4141_, sizeof(void*)*5 + 2);
if (v_errorOnMissingSpec_4147_ == 0)
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4148_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_4148_, 0, v_prog_4138_);
lean_ctor_set(v___x_4148_, 1, v_monad_4139_);
lean_ctor_set(v___x_4148_, 2, v_thms_4140_);
v___x_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
return v___x_4150_;
}
else
{
lean_object* v___x_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
v___x_4151_ = lean_array_get_size(v_thms_4140_);
v___x_4152_ = lean_unsigned_to_nat(0u);
v___x_4153_ = lean_nat_dec_eq(v___x_4151_, v___x_4152_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; size_t v_sz_4163_; size_t v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4154_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1);
v___x_4155_ = l_Lean_MessageData_ofExpr(v_prog_4138_);
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3);
v___x_4158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = l_Lean_MessageData_ofExpr(v_monad_4139_);
v___x_4160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4158_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
v___x_4161_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5);
v___x_4162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4160_);
lean_ctor_set(v___x_4162_, 1, v___x_4161_);
v_sz_4163_ = lean_array_size(v_thms_4140_);
v___x_4164_ = ((size_t)0ULL);
v___x_4165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_4163_, v___x_4164_, v_thms_4140_);
v___x_4166_ = lean_array_to_list(v___x_4165_);
v___x_4167_ = lean_box(0);
v___x_4168_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1(v___x_4166_, v___x_4167_);
v___x_4169_ = l_Lean_MessageData_ofList(v___x_4168_);
v___x_4170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4162_);
lean_ctor_set(v___x_4170_, 1, v___x_4169_);
v___x_4171_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_4172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4170_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
v___x_4173_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_4172_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
return v___x_4173_;
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
lean_dec_ref(v_thms_4140_);
lean_dec_ref(v_monad_4139_);
v___x_4174_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9);
v___x_4175_ = l_Lean_MessageData_ofExpr(v_prog_4138_);
v___x_4176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4174_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_4178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4176_);
lean_ctor_set(v___x_4178_, 1, v___x_4177_);
v___x_4179_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_4178_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
return v___x_4179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object* v_prog_4180_, lean_object* v_monad_4181_, lean_object* v_thms_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_4180_, v_monad_4181_, v_thms_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_);
lean_dec(v_a_4187_);
lean_dec_ref(v_a_4186_);
lean_dec(v_a_4185_);
lean_dec_ref(v_a_4184_);
lean_dec_ref(v_a_4183_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec(lean_object* v_prog_4190_, lean_object* v_monad_4191_, lean_object* v_thms_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_4190_, v_monad_4191_, v_thms_4192_, v_a_4193_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object* v_prog_4206_, lean_object* v_monad_4207_, lean_object* v_thms_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec(v_prog_4206_, v_monad_4207_, v_thms_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec(v_a_4210_);
lean_dec_ref(v_a_4209_);
return v_res_4221_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1(void){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__0));
v___x_4224_ = l_Lean_stringToMessageData(v___x_4223_);
return v___x_4224_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3(void){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__2));
v___x_4227_ = l_Lean_stringToMessageData(v___x_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(lean_object* v_prog_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_){
_start:
{
lean_object* v_untilPat_x3f_4237_; 
v_untilPat_x3f_4237_ = lean_ctor_get(v_a_4229_, 4);
if (lean_obj_tag(v_untilPat_x3f_4237_) == 1)
{
lean_object* v_val_4238_; uint8_t v___x_4239_; lean_object* v___x_4240_; 
v_val_4238_ = lean_ctor_get(v_untilPat_x3f_4237_, 0);
v___x_4239_ = 1;
lean_inc_ref(v_prog_4228_);
lean_inc(v_val_4238_);
v___x_4240_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_val_4238_, v_prog_4228_, v___x_4239_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4287_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4243_ = v___x_4240_;
v_isShared_4244_ = v_isSharedCheck_4287_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4240_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4287_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
if (lean_obj_tag(v_a_4241_) == 0)
{
uint8_t v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4248_; 
lean_dec_ref(v_prog_4228_);
v___x_4245_ = 0;
v___x_4246_ = lean_box(v___x_4245_);
if (v_isShared_4244_ == 0)
{
lean_ctor_set(v___x_4243_, 0, v___x_4246_);
v___x_4248_ = v___x_4243_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4246_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
else
{
lean_object* v_options_4250_; uint8_t v_hasTrace_4251_; 
lean_dec_ref_known(v_a_4241_, 1);
v_options_4250_ = lean_ctor_get(v_a_4234_, 2);
v_hasTrace_4251_ = lean_ctor_get_uint8(v_options_4250_, sizeof(void*)*1);
if (v_hasTrace_4251_ == 0)
{
lean_object* v___x_4252_; lean_object* v___x_4254_; 
lean_dec_ref(v_prog_4228_);
v___x_4252_ = lean_box(v___x_4239_);
if (v_isShared_4244_ == 0)
{
lean_ctor_set(v___x_4243_, 0, v___x_4252_);
v___x_4254_ = v___x_4243_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4252_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
else
{
lean_object* v_inheritedTraceOptions_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; 
v_inheritedTraceOptions_4256_ = lean_ctor_get(v_a_4234_, 13);
v___x_4257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_4258_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_4259_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4256_, v_options_4250_, v___x_4258_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4260_; lean_object* v___x_4262_; 
lean_dec_ref(v_prog_4228_);
v___x_4260_ = lean_box(v___x_4239_);
if (v_isShared_4244_ == 0)
{
lean_ctor_set(v___x_4243_, 0, v___x_4260_);
v___x_4262_ = v___x_4243_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
else
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
lean_del_object(v___x_4243_);
v___x_4264_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1);
v___x_4265_ = l_Lean_MessageData_ofExpr(v_prog_4228_);
v___x_4266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4264_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3);
v___x_4268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4266_);
lean_ctor_set(v___x_4268_, 1, v___x_4267_);
v___x_4269_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4257_, v___x_4268_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4277_; 
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4277_ == 0)
{
lean_object* v_unused_4278_; 
v_unused_4278_ = lean_ctor_get(v___x_4269_, 0);
lean_dec(v_unused_4278_);
v___x_4271_ = v___x_4269_;
v_isShared_4272_ = v_isSharedCheck_4277_;
goto v_resetjp_4270_;
}
else
{
lean_dec(v___x_4269_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4277_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4273_; lean_object* v___x_4275_; 
v___x_4273_ = lean_box(v___x_4239_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v___x_4273_);
v___x_4275_ = v___x_4271_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4273_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
v_a_4279_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4269_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4269_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
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
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec_ref(v_prog_4228_);
v_a_4288_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4240_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4240_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
else
{
uint8_t v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
lean_dec_ref(v_prog_4228_);
v___x_4296_ = 0;
v___x_4297_ = lean_box(v___x_4296_);
v___x_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
return v___x_4298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___boxed(lean_object* v_prog_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v_prog_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_);
lean_dec(v_a_4306_);
lean_dec_ref(v_a_4305_);
lean_dec(v_a_4304_);
lean_dec_ref(v_a_4303_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
lean_dec_ref(v_a_4300_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern(lean_object* v_prog_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v_prog_4309_, v_a_4310_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___boxed(lean_object* v_prog_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern(v_prog_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
lean_dec(v_a_4332_);
lean_dec_ref(v_a_4331_);
lean_dec(v_a_4330_);
lean_dec_ref(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
lean_dec(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(lean_object* v_k_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v_b_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v___x_4351_; 
lean_inc(v___y_4349_);
lean_inc_ref(v___y_4348_);
lean_inc(v___y_4347_);
lean_inc_ref(v___y_4346_);
lean_inc(v___y_4344_);
lean_inc_ref(v___y_4343_);
lean_inc(v___y_4342_);
lean_inc_ref(v___y_4341_);
lean_inc(v___y_4340_);
lean_inc(v___y_4339_);
lean_inc_ref(v___y_4338_);
v___x_4351_ = lean_apply_13(v_k_4337_, v_b_4345_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, lean_box(0));
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v_b_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(v_k_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v_b_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(lean_object* v_name_4367_, lean_object* v_type_4368_, lean_object* v_val_4369_, lean_object* v_k_4370_, uint8_t v_nondep_4371_, uint8_t v_kind_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v___f_4385_; lean_object* v___x_4386_; 
lean_inc(v___y_4379_);
lean_inc_ref(v___y_4378_);
lean_inc(v___y_4377_);
lean_inc_ref(v___y_4376_);
lean_inc(v___y_4375_);
lean_inc(v___y_4374_);
lean_inc_ref(v___y_4373_);
v___f_4385_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_4385_, 0, v_k_4370_);
lean_closure_set(v___f_4385_, 1, v___y_4373_);
lean_closure_set(v___f_4385_, 2, v___y_4374_);
lean_closure_set(v___f_4385_, 3, v___y_4375_);
lean_closure_set(v___f_4385_, 4, v___y_4376_);
lean_closure_set(v___f_4385_, 5, v___y_4377_);
lean_closure_set(v___f_4385_, 6, v___y_4378_);
lean_closure_set(v___f_4385_, 7, v___y_4379_);
v___x_4386_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_4367_, v_type_4368_, v_val_4369_, v___f_4385_, v_nondep_4371_, v_kind_4372_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4386_) == 0)
{
return v___x_4386_;
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v___x_4386_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4386_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_name_4395_ = _args[0];
lean_object* v_type_4396_ = _args[1];
lean_object* v_val_4397_ = _args[2];
lean_object* v_k_4398_ = _args[3];
lean_object* v_nondep_4399_ = _args[4];
lean_object* v_kind_4400_ = _args[5];
lean_object* v___y_4401_ = _args[6];
lean_object* v___y_4402_ = _args[7];
lean_object* v___y_4403_ = _args[8];
lean_object* v___y_4404_ = _args[9];
lean_object* v___y_4405_ = _args[10];
lean_object* v___y_4406_ = _args[11];
lean_object* v___y_4407_ = _args[12];
lean_object* v___y_4408_ = _args[13];
lean_object* v___y_4409_ = _args[14];
lean_object* v___y_4410_ = _args[15];
lean_object* v___y_4411_ = _args[16];
lean_object* v___y_4412_ = _args[17];
_start:
{
uint8_t v_nondep_boxed_4413_; uint8_t v_kind_boxed_4414_; lean_object* v_res_4415_; 
v_nondep_boxed_4413_ = lean_unbox(v_nondep_4399_);
v_kind_boxed_4414_ = lean_unbox(v_kind_4400_);
v_res_4415_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4395_, v_type_4396_, v_val_4397_, v_k_4398_, v_nondep_boxed_4413_, v_kind_boxed_4414_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0(lean_object* v_00_u03b1_4416_, lean_object* v_name_4417_, lean_object* v_type_4418_, lean_object* v_val_4419_, lean_object* v_k_4420_, uint8_t v_nondep_4421_, uint8_t v_kind_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4417_, v_type_4418_, v_val_4419_, v_k_4420_, v_nondep_4421_, v_kind_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_4436_ = _args[0];
lean_object* v_name_4437_ = _args[1];
lean_object* v_type_4438_ = _args[2];
lean_object* v_val_4439_ = _args[3];
lean_object* v_k_4440_ = _args[4];
lean_object* v_nondep_4441_ = _args[5];
lean_object* v_kind_4442_ = _args[6];
lean_object* v___y_4443_ = _args[7];
lean_object* v___y_4444_ = _args[8];
lean_object* v___y_4445_ = _args[9];
lean_object* v___y_4446_ = _args[10];
lean_object* v___y_4447_ = _args[11];
lean_object* v___y_4448_ = _args[12];
lean_object* v___y_4449_ = _args[13];
lean_object* v___y_4450_ = _args[14];
lean_object* v___y_4451_ = _args[15];
lean_object* v___y_4452_ = _args[16];
lean_object* v___y_4453_ = _args[17];
lean_object* v___y_4454_ = _args[18];
_start:
{
uint8_t v_nondep_boxed_4455_; uint8_t v_kind_boxed_4456_; lean_object* v_res_4457_; 
v_nondep_boxed_4455_ = lean_unbox(v_nondep_4441_);
v_kind_boxed_4456_ = lean_unbox(v_kind_4442_);
v_res_4457_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0(v_00_u03b1_4436_, v_name_4437_, v_type_4438_, v_val_4439_, v_k_4440_, v_nondep_boxed_4455_, v_kind_boxed_4456_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0___boxed(lean_object* v_acc_4458_, lean_object* v_declInfos_4459_, lean_object* v_k_4460_, lean_object* v_fv_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0(v_acc_4458_, v_declInfos_4459_, v_k_4460_, v_fv_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(lean_object* v_declInfos_4475_, lean_object* v_k_4476_, lean_object* v_acc_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; uint8_t v___x_4492_; 
v___x_4490_ = lean_array_get_size(v_acc_4477_);
v___x_4491_ = lean_array_get_size(v_declInfos_4475_);
v___x_4492_ = lean_nat_dec_lt(v___x_4490_, v___x_4491_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; 
lean_dec_ref(v_declInfos_4475_);
lean_inc(v_a_4488_);
lean_inc_ref(v_a_4487_);
lean_inc(v_a_4486_);
lean_inc_ref(v_a_4485_);
lean_inc(v_a_4484_);
lean_inc_ref(v_a_4483_);
lean_inc(v_a_4482_);
lean_inc_ref(v_a_4481_);
lean_inc(v_a_4480_);
lean_inc(v_a_4479_);
lean_inc_ref(v_a_4478_);
v___x_4493_ = lean_apply_13(v_k_4476_, v_acc_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, lean_box(0));
return v___x_4493_;
}
else
{
lean_object* v___x_4494_; lean_object* v_snd_4495_; lean_object* v_fst_4496_; lean_object* v_fst_4497_; lean_object* v_snd_4498_; lean_object* v___f_4499_; uint8_t v___x_4500_; uint8_t v___x_4501_; lean_object* v___x_4502_; 
v___x_4494_ = lean_array_fget_borrowed(v_declInfos_4475_, v___x_4490_);
v_snd_4495_ = lean_ctor_get(v___x_4494_, 1);
v_fst_4496_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_fst_4496_);
v_fst_4497_ = lean_ctor_get(v_snd_4495_, 0);
lean_inc(v_fst_4497_);
v_snd_4498_ = lean_ctor_get(v_snd_4495_, 1);
lean_inc(v_snd_4498_);
v___f_4499_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4499_, 0, v_acc_4477_);
lean_closure_set(v___f_4499_, 1, v_declInfos_4475_);
lean_closure_set(v___f_4499_, 2, v_k_4476_);
v___x_4500_ = 0;
v___x_4501_ = 0;
v___x_4502_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_fst_4496_, v_fst_4497_, v_snd_4498_, v___f_4499_, v___x_4500_, v___x_4501_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_);
return v___x_4502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0(lean_object* v_acc_4503_, lean_object* v_declInfos_4504_, lean_object* v_k_4505_, lean_object* v_fv_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4519_ = lean_array_push(v_acc_4503_, v_fv_4506_);
v___x_4520_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4504_, v_k_4505_, v___x_4519_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___boxed(lean_object* v_declInfos_4521_, lean_object* v_k_4522_, lean_object* v_acc_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4521_, v_k_4522_, v_acc_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_match__1_splitter___redArg(lean_object* v_x_4537_, lean_object* v_h__1_4538_){
_start:
{
lean_object* v_snd_4539_; lean_object* v_fst_4540_; lean_object* v_fst_4541_; lean_object* v_snd_4542_; lean_object* v___x_4543_; 
v_snd_4539_ = lean_ctor_get(v_x_4537_, 1);
lean_inc(v_snd_4539_);
v_fst_4540_ = lean_ctor_get(v_x_4537_, 0);
lean_inc(v_fst_4540_);
lean_dec_ref(v_x_4537_);
v_fst_4541_ = lean_ctor_get(v_snd_4539_, 0);
lean_inc(v_fst_4541_);
v_snd_4542_ = lean_ctor_get(v_snd_4539_, 1);
lean_inc(v_snd_4542_);
lean_dec(v_snd_4539_);
v___x_4543_ = lean_apply_3(v_h__1_4538_, v_fst_4540_, v_fst_4541_, v_snd_4542_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_match__1_splitter(lean_object* v_motive_4544_, lean_object* v_x_4545_, lean_object* v_h__1_4546_){
_start:
{
lean_object* v_snd_4547_; lean_object* v_fst_4548_; lean_object* v_fst_4549_; lean_object* v_snd_4550_; lean_object* v___x_4551_; 
v_snd_4547_ = lean_ctor_get(v_x_4545_, 1);
lean_inc(v_snd_4547_);
v_fst_4548_ = lean_ctor_get(v_x_4545_, 0);
lean_inc(v_fst_4548_);
lean_dec_ref(v_x_4545_);
v_fst_4549_ = lean_ctor_get(v_snd_4547_, 0);
lean_inc(v_fst_4549_);
v_snd_4550_ = lean_ctor_get(v_snd_4547_, 1);
lean_inc(v_snd_4550_);
lean_dec(v_snd_4547_);
v___x_4551_ = lean_apply_3(v_h__1_4546_, v_fst_4548_, v_fst_4549_, v_snd_4550_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND(lean_object* v_declInfos_4554_, lean_object* v_k_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___closed__0));
v___x_4569_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4554_, v_k_4555_, v___x_4568_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___boxed(lean_object* v_declInfos_4570_, lean_object* v_k_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND(v_declInfos_4570_, v_k_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
lean_dec(v_a_4582_);
lean_dec_ref(v_a_4581_);
lean_dec(v_a_4580_);
lean_dec_ref(v_a_4579_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
lean_dec(v_a_4574_);
lean_dec(v_a_4573_);
lean_dec_ref(v_a_4572_);
return v_res_4584_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0(lean_object* v_x_4585_){
_start:
{
uint8_t v___x_4586_; 
v___x_4586_ = 0;
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0___boxed(lean_object* v_x_4587_){
_start:
{
uint8_t v_res_4588_; lean_object* v_r_4589_; 
v_res_4588_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0(v_x_4587_);
lean_dec(v_x_4587_);
v_r_4589_ = lean_box(v_res_4588_);
return v_r_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1(lean_object* v_frameStx_4590_, lean_object* v___x_4591_, uint8_t v___x_4592_, lean_object* v___x_4593_, lean_object* v_fvs_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v___x_4602_; 
v___x_4602_ = l_Lean_Elab_Term_elabTermEnsuringType(v_frameStx_4590_, v___x_4591_, v___x_4592_, v___x_4592_, v___x_4593_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; uint8_t v___x_4604_; lean_object* v___x_4605_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
lean_inc(v_a_4603_);
lean_dec_ref_known(v___x_4602_, 1);
v___x_4604_ = 0;
v___x_4605_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4604_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
if (lean_obj_tag(v___x_4605_) == 0)
{
uint8_t v___x_4606_; lean_object* v___x_4607_; 
lean_dec_ref_known(v___x_4605_, 1);
v___x_4606_ = 1;
v___x_4607_ = l_Lean_Meta_mkLetFVars(v_fvs_4594_, v_a_4603_, v___x_4592_, v___x_4592_, v___x_4606_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
return v___x_4607_;
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
lean_dec(v_a_4603_);
v_a_4608_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4605_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4605_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
else
{
return v___x_4602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1___boxed(lean_object* v_frameStx_4616_, lean_object* v___x_4617_, lean_object* v___x_4618_, lean_object* v___x_4619_, lean_object* v_fvs_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_){
_start:
{
uint8_t v___x_12406__boxed_4628_; lean_object* v_res_4629_; 
v___x_12406__boxed_4628_ = lean_unbox(v___x_4618_);
v_res_4629_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1(v_frameStx_4616_, v___x_4617_, v___x_12406__boxed_4628_, v___x_4619_, v_fvs_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec_ref(v_fvs_4620_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2(lean_object* v_resourceTy_4635_, lean_object* v_frameStx_4636_, lean_object* v___f_4637_, lean_object* v_fvs_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v___x_4651_; uint8_t v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___f_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; uint8_t v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4651_, 0, v_resourceTy_4635_);
v___x_4652_ = 1;
v___x_4653_ = lean_box(0);
v___x_4654_ = lean_box(v___x_4652_);
v___f_4655_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4655_, 0, v_frameStx_4636_);
lean_closure_set(v___f_4655_, 1, v___x_4651_);
lean_closure_set(v___f_4655_, 2, v___x_4654_);
lean_closure_set(v___f_4655_, 3, v___x_4653_);
lean_closure_set(v___f_4655_, 4, v_fvs_4638_);
v___x_4656_ = lean_box(0);
v___x_4657_ = lean_box(1);
v___x_4658_ = 0;
v___x_4659_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__0));
v___x_4660_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_4660_, 0, v___x_4653_);
lean_ctor_set(v___x_4660_, 1, v___x_4656_);
lean_ctor_set(v___x_4660_, 2, v___x_4653_);
lean_ctor_set(v___x_4660_, 3, v___f_4637_);
lean_ctor_set(v___x_4660_, 4, v___x_4657_);
lean_ctor_set(v___x_4660_, 5, v___x_4657_);
lean_ctor_set(v___x_4660_, 6, v___x_4653_);
lean_ctor_set(v___x_4660_, 7, v___x_4659_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*8, v___x_4652_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*8 + 1, v___x_4652_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*8 + 2, v___x_4652_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*8 + 3, v___x_4652_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*8 + 4, v___x_4658_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*8 + 5, v___x_4658_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*8 + 6, v___x_4658_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*8 + 7, v___x_4658_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*8 + 8, v___x_4652_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*8 + 9, v___x_4658_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*8 + 10, v___x_4652_);
v___x_4661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__1));
v___x_4662_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_4655_, v___x_4660_, v___x_4661_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v_fst_4664_; lean_object* v___x_4665_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4663_);
lean_dec_ref_known(v___x_4662_, 1);
v_fst_4664_ = lean_ctor_get(v_a_4663_, 0);
lean_inc(v_fst_4664_);
lean_dec(v_a_4663_);
v___x_4665_ = l_Lean_Meta_Sym_instantiateMVarsS(v_fst_4664_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
return v___x_4665_;
}
else
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
v_a_4666_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4668_ = v___x_4662_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4662_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___boxed(lean_object* v_resourceTy_4674_, lean_object* v_frameStx_4675_, lean_object* v___f_4676_, lean_object* v_fvs_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2(v_resourceTy_4674_, v_frameStx_4675_, v___f_4676_, v_fvs_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec(v___y_4680_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(lean_object* v_as_4691_, size_t v_sz_4692_, size_t v_i_4693_, lean_object* v_b_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v_a_4701_; uint8_t v___x_4705_; 
v___x_4705_ = lean_usize_dec_lt(v_i_4693_, v_sz_4692_);
if (v___x_4705_ == 0)
{
lean_object* v___x_4706_; 
v___x_4706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4706_, 0, v_b_4694_);
return v___x_4706_;
}
else
{
lean_object* v_snd_4707_; lean_object* v_fst_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4754_; 
v_snd_4707_ = lean_ctor_get(v_b_4694_, 1);
v_fst_4708_ = lean_ctor_get(v_b_4694_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v_b_4694_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4710_ = v_b_4694_;
v_isShared_4711_ = v_isSharedCheck_4754_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_snd_4707_);
lean_inc(v_fst_4708_);
lean_dec(v_b_4694_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4754_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v_array_4712_; lean_object* v_start_4713_; lean_object* v_stop_4714_; uint8_t v___x_4715_; 
v_array_4712_ = lean_ctor_get(v_snd_4707_, 0);
v_start_4713_ = lean_ctor_get(v_snd_4707_, 1);
v_stop_4714_ = lean_ctor_get(v_snd_4707_, 2);
v___x_4715_ = lean_nat_dec_lt(v_start_4713_, v_stop_4714_);
if (v___x_4715_ == 0)
{
lean_object* v___x_4717_; 
if (v_isShared_4711_ == 0)
{
v___x_4717_ = v___x_4710_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_fst_4708_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v_snd_4707_);
v___x_4717_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4718_; 
v___x_4718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4717_);
return v___x_4718_;
}
}
else
{
lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4750_; 
lean_inc(v_stop_4714_);
lean_inc(v_start_4713_);
lean_inc_ref(v_array_4712_);
v_isSharedCheck_4750_ = !lean_is_exclusive(v_snd_4707_);
if (v_isSharedCheck_4750_ == 0)
{
lean_object* v_unused_4751_; lean_object* v_unused_4752_; lean_object* v_unused_4753_; 
v_unused_4751_ = lean_ctor_get(v_snd_4707_, 2);
lean_dec(v_unused_4751_);
v_unused_4752_ = lean_ctor_get(v_snd_4707_, 1);
lean_dec(v_unused_4752_);
v_unused_4753_ = lean_ctor_get(v_snd_4707_, 0);
lean_dec(v_unused_4753_);
v___x_4721_ = v_snd_4707_;
v_isShared_4722_ = v_isSharedCheck_4750_;
goto v_resetjp_4720_;
}
else
{
lean_dec(v_snd_4707_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4750_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v_a_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4728_; 
v_a_4723_ = lean_array_uget_borrowed(v_as_4691_, v_i_4693_);
v___x_4724_ = lean_array_fget(v_array_4712_, v_start_4713_);
v___x_4725_ = lean_unsigned_to_nat(1u);
v___x_4726_ = lean_nat_add(v_start_4713_, v___x_4725_);
lean_dec(v_start_4713_);
if (v_isShared_4722_ == 0)
{
lean_ctor_set(v___x_4721_, 1, v___x_4726_);
v___x_4728_ = v___x_4721_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_array_4712_);
lean_ctor_set(v_reuseFailAlloc_4749_, 1, v___x_4726_);
lean_ctor_set(v_reuseFailAlloc_4749_, 2, v_stop_4714_);
v___x_4728_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
if (lean_obj_tag(v_a_4723_) == 1)
{
lean_object* v_val_4729_; lean_object* v___x_4730_; 
v_val_4729_ = lean_ctor_get(v_a_4723_, 0);
lean_inc(v___y_4698_);
lean_inc_ref(v___y_4697_);
lean_inc(v___y_4696_);
lean_inc_ref(v___y_4695_);
lean_inc(v___x_4724_);
v___x_4730_ = lean_infer_type(v___x_4724_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4733_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v___x_4730_, 1);
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 1, v___x_4724_);
lean_ctor_set(v___x_4710_, 0, v_a_4731_);
v___x_4733_ = v___x_4710_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
lean_ctor_set(v_reuseFailAlloc_4737_, 1, v___x_4724_);
v___x_4733_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
lean_inc(v_val_4729_);
v___x_4734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4734_, 0, v_val_4729_);
lean_ctor_set(v___x_4734_, 1, v___x_4733_);
v___x_4735_ = lean_array_push(v_fst_4708_, v___x_4734_);
v___x_4736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4736_, 0, v___x_4735_);
lean_ctor_set(v___x_4736_, 1, v___x_4728_);
v_a_4701_ = v___x_4736_;
goto v___jp_4700_;
}
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
lean_dec_ref(v___x_4728_);
lean_dec(v___x_4724_);
lean_del_object(v___x_4710_);
lean_dec(v_fst_4708_);
v_a_4738_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___x_4730_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4730_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
else
{
lean_object* v___x_4747_; 
lean_dec(v___x_4724_);
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 1, v___x_4728_);
v___x_4747_ = v___x_4710_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_fst_4708_);
lean_ctor_set(v_reuseFailAlloc_4748_, 1, v___x_4728_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
v_a_4701_ = v___x_4747_;
goto v___jp_4700_;
}
}
}
}
}
}
}
v___jp_4700_:
{
size_t v___x_4702_; size_t v___x_4703_; 
v___x_4702_ = ((size_t)1ULL);
v___x_4703_ = lean_usize_add(v_i_4693_, v___x_4702_);
v_i_4693_ = v___x_4703_;
v_b_4694_ = v_a_4701_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg___boxed(lean_object* v_as_4755_, lean_object* v_sz_4756_, lean_object* v_i_4757_, lean_object* v_b_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
size_t v_sz_boxed_4764_; size_t v_i_boxed_4765_; lean_object* v_res_4766_; 
v_sz_boxed_4764_ = lean_unbox_usize(v_sz_4756_);
lean_dec(v_sz_4756_);
v_i_boxed_4765_ = lean_unbox_usize(v_i_4757_);
lean_dec(v_i_4757_);
v_res_4766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_as_4755_, v_sz_boxed_4764_, v_i_boxed_4765_, v_b_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec_ref(v_as_4755_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(lean_object* v_resourceTy_4770_, lean_object* v_entry_4771_, lean_object* v_res_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v_args_4785_; lean_object* v_varNames_4786_; lean_object* v_frameStx_4787_; lean_object* v___x_4788_; lean_object* v_decls_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; size_t v_sz_4793_; size_t v___x_4794_; lean_object* v___x_4795_; 
v_args_4785_ = lean_ctor_get(v_res_4772_, 1);
lean_inc_ref(v_args_4785_);
lean_dec_ref(v_res_4772_);
v_varNames_4786_ = lean_ctor_get(v_entry_4771_, 1);
lean_inc_ref(v_varNames_4786_);
v_frameStx_4787_ = lean_ctor_get(v_entry_4771_, 2);
lean_inc(v_frameStx_4787_);
lean_dec_ref(v_entry_4771_);
v___x_4788_ = lean_unsigned_to_nat(0u);
v_decls_4789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__0));
v___x_4790_ = lean_array_get_size(v_args_4785_);
v___x_4791_ = l_Array_toSubarray___redArg(v_args_4785_, v___x_4788_, v___x_4790_);
v___x_4792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4792_, 0, v_decls_4789_);
lean_ctor_set(v___x_4792_, 1, v___x_4791_);
v_sz_4793_ = lean_array_size(v_varNames_4786_);
v___x_4794_ = ((size_t)0ULL);
v___x_4795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_varNames_4786_, v_sz_4793_, v___x_4794_, v___x_4792_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
lean_dec_ref(v_varNames_4786_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v_a_4796_; lean_object* v_fst_4797_; lean_object* v_keyedConfig_4798_; uint8_t v_trackZetaDelta_4799_; lean_object* v_zetaDeltaSet_4800_; lean_object* v_lctx_4801_; lean_object* v_localInstances_4802_; lean_object* v_defEqCtx_x3f_4803_; lean_object* v_synthPendingDepth_4804_; lean_object* v_customCanUnfoldPredicate_x3f_4805_; uint8_t v_univApprox_4806_; uint8_t v_inTypeClassResolution_4807_; uint8_t v_cacheInferType_4808_; lean_object* v___f_4809_; lean_object* v___f_4810_; uint8_t v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_a_4796_);
lean_dec_ref_known(v___x_4795_, 1);
v_fst_4797_ = lean_ctor_get(v_a_4796_, 0);
lean_inc(v_fst_4797_);
lean_dec(v_a_4796_);
v_keyedConfig_4798_ = lean_ctor_get(v_a_4780_, 0);
v_trackZetaDelta_4799_ = lean_ctor_get_uint8(v_a_4780_, sizeof(void*)*7);
v_zetaDeltaSet_4800_ = lean_ctor_get(v_a_4780_, 1);
v_lctx_4801_ = lean_ctor_get(v_a_4780_, 2);
v_localInstances_4802_ = lean_ctor_get(v_a_4780_, 3);
v_defEqCtx_x3f_4803_ = lean_ctor_get(v_a_4780_, 4);
v_synthPendingDepth_4804_ = lean_ctor_get(v_a_4780_, 5);
v_customCanUnfoldPredicate_x3f_4805_ = lean_ctor_get(v_a_4780_, 6);
v_univApprox_4806_ = lean_ctor_get_uint8(v_a_4780_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4807_ = lean_ctor_get_uint8(v_a_4780_, sizeof(void*)*7 + 2);
v_cacheInferType_4808_ = lean_ctor_get_uint8(v_a_4780_, sizeof(void*)*7 + 3);
v___f_4809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__1));
v___f_4810_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___boxed), 16, 3);
lean_closure_set(v___f_4810_, 0, v_resourceTy_4770_);
lean_closure_set(v___f_4810_, 1, v_frameStx_4787_);
lean_closure_set(v___f_4810_, 2, v___f_4809_);
v___x_4811_ = 1;
lean_inc_ref(v_keyedConfig_4798_);
v___x_4812_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4811_, v_keyedConfig_4798_);
lean_inc(v_customCanUnfoldPredicate_x3f_4805_);
lean_inc(v_synthPendingDepth_4804_);
lean_inc(v_defEqCtx_x3f_4803_);
lean_inc_ref(v_localInstances_4802_);
lean_inc_ref(v_lctx_4801_);
lean_inc(v_zetaDeltaSet_4800_);
v___x_4813_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4813_, 0, v___x_4812_);
lean_ctor_set(v___x_4813_, 1, v_zetaDeltaSet_4800_);
lean_ctor_set(v___x_4813_, 2, v_lctx_4801_);
lean_ctor_set(v___x_4813_, 3, v_localInstances_4802_);
lean_ctor_set(v___x_4813_, 4, v_defEqCtx_x3f_4803_);
lean_ctor_set(v___x_4813_, 5, v_synthPendingDepth_4804_);
lean_ctor_set(v___x_4813_, 6, v_customCanUnfoldPredicate_x3f_4805_);
lean_ctor_set_uint8(v___x_4813_, sizeof(void*)*7, v_trackZetaDelta_4799_);
lean_ctor_set_uint8(v___x_4813_, sizeof(void*)*7 + 1, v_univApprox_4806_);
lean_ctor_set_uint8(v___x_4813_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4807_);
lean_ctor_set_uint8(v___x_4813_, sizeof(void*)*7 + 3, v_cacheInferType_4808_);
v___x_4814_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_fst_4797_, v___f_4810_, v_decls_4789_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v___x_4813_, v_a_4781_, v_a_4782_, v_a_4783_);
lean_dec_ref_known(v___x_4813_, 7);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4822_; 
v_a_4815_ = lean_ctor_get(v___x_4814_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4814_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4817_ = v___x_4814_;
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v___x_4814_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v___x_4820_; 
if (v_isShared_4818_ == 0)
{
v___x_4820_ = v___x_4817_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_a_4815_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
else
{
return v___x_4814_;
}
}
else
{
lean_object* v_a_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4830_; 
lean_dec(v_frameStx_4787_);
lean_dec_ref(v_resourceTy_4770_);
v_a_4823_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4825_ = v___x_4795_;
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_a_4823_);
lean_dec(v___x_4795_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4828_; 
if (v_isShared_4826_ == 0)
{
v___x_4828_ = v___x_4825_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_a_4823_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___boxed(lean_object* v_resourceTy_4831_, lean_object* v_entry_4832_, lean_object* v_res_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(v_resourceTy_4831_, v_entry_4832_, v_res_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_);
lean_dec(v_a_4844_);
lean_dec_ref(v_a_4843_);
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
lean_dec(v_a_4836_);
lean_dec(v_a_4835_);
lean_dec_ref(v_a_4834_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0(lean_object* v_as_4847_, size_t v_sz_4848_, size_t v_i_4849_, lean_object* v_b_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_){
_start:
{
lean_object* v___x_4863_; 
v___x_4863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_as_4847_, v_sz_4848_, v_i_4849_, v_b_4850_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___boxed(lean_object* v_as_4864_, lean_object* v_sz_4865_, lean_object* v_i_4866_, lean_object* v_b_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
size_t v_sz_boxed_4880_; size_t v_i_boxed_4881_; lean_object* v_res_4882_; 
v_sz_boxed_4880_ = lean_unbox_usize(v_sz_4865_);
lean_dec(v_sz_4865_);
v_i_boxed_4881_ = lean_unbox_usize(v_i_4866_);
lean_dec(v_i_4866_);
v_res_4882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0(v_as_4864_, v_sz_boxed_4880_, v_i_boxed_4881_, v_b_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec_ref(v_as_4864_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(lean_object* v___x_4883_, lean_object* v___x_4884_, lean_object* v_as_4885_, size_t v_sz_4886_, size_t v_i_4887_, lean_object* v_b_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
lean_object* v_a_4897_; uint8_t v___x_4901_; 
v___x_4901_ = lean_usize_dec_lt(v_i_4887_, v_sz_4886_);
if (v___x_4901_ == 0)
{
lean_object* v___x_4902_; 
lean_dec_ref(v___x_4884_);
v___x_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4902_, 0, v_b_4888_);
return v___x_4902_;
}
else
{
lean_object* v_a_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; uint8_t v_retired_4906_; 
v_a_4903_ = lean_array_uget_borrowed(v_as_4885_, v_i_4887_);
v___x_4904_ = l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default;
v___x_4905_ = lean_array_get_borrowed(v___x_4904_, v___x_4883_, v_a_4903_);
v_retired_4906_ = lean_ctor_get_uint8(v___x_4905_, sizeof(void*)*4);
if (v_retired_4906_ == 0)
{
lean_object* v_pat_4907_; lean_object* v_srcIdx_4908_; lean_object* v___x_4909_; 
v_pat_4907_ = lean_ctor_get(v___x_4905_, 0);
v_srcIdx_4908_ = lean_ctor_get(v___x_4905_, 3);
lean_inc_ref(v___x_4884_);
lean_inc_ref(v_pat_4907_);
v___x_4909_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pat_4907_, v___x_4884_, v___x_4901_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
lean_inc(v_a_4910_);
lean_dec_ref_known(v___x_4909_, 1);
if (lean_obj_tag(v_a_4910_) == 1)
{
if (lean_obj_tag(v_b_4888_) == 0)
{
lean_object* v_val_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4919_; 
v_val_4911_ = lean_ctor_get(v_a_4910_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v_a_4910_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4913_ = v_a_4910_;
v_isShared_4914_ = v_isSharedCheck_4919_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_val_4911_);
lean_dec(v_a_4910_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4919_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4915_; lean_object* v___x_4917_; 
lean_inc(v___x_4905_);
v___x_4915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4905_);
lean_ctor_set(v___x_4915_, 1, v_val_4911_);
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 0, v___x_4915_);
v___x_4917_ = v___x_4913_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v___x_4915_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
v_a_4897_ = v___x_4917_;
goto v___jp_4896_;
}
}
}
else
{
lean_object* v_val_4920_; lean_object* v_fst_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4939_; 
v_val_4920_ = lean_ctor_get(v_b_4888_, 0);
lean_inc(v_val_4920_);
v_fst_4921_ = lean_ctor_get(v_val_4920_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v_val_4920_);
if (v_isSharedCheck_4939_ == 0)
{
lean_object* v_unused_4940_; 
v_unused_4940_ = lean_ctor_get(v_val_4920_, 1);
lean_dec(v_unused_4940_);
v___x_4923_ = v_val_4920_;
v_isShared_4924_ = v_isSharedCheck_4939_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_fst_4921_);
lean_dec(v_val_4920_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4939_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v_val_4925_; lean_object* v_srcIdx_4926_; uint8_t v___x_4927_; 
v_val_4925_ = lean_ctor_get(v_a_4910_, 0);
lean_inc(v_val_4925_);
lean_dec_ref_known(v_a_4910_, 1);
v_srcIdx_4926_ = lean_ctor_get(v_fst_4921_, 3);
lean_inc(v_srcIdx_4926_);
lean_dec(v_fst_4921_);
v___x_4927_ = lean_nat_dec_lt(v_srcIdx_4908_, v_srcIdx_4926_);
lean_dec(v_srcIdx_4926_);
if (v___x_4927_ == 0)
{
lean_dec(v_val_4925_);
lean_del_object(v___x_4923_);
v_a_4897_ = v_b_4888_;
goto v___jp_4896_;
}
else
{
lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4937_; 
v_isSharedCheck_4937_ = !lean_is_exclusive(v_b_4888_);
if (v_isSharedCheck_4937_ == 0)
{
lean_object* v_unused_4938_; 
v_unused_4938_ = lean_ctor_get(v_b_4888_, 0);
lean_dec(v_unused_4938_);
v___x_4929_ = v_b_4888_;
v_isShared_4930_ = v_isSharedCheck_4937_;
goto v_resetjp_4928_;
}
else
{
lean_dec(v_b_4888_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4937_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4932_; 
lean_inc(v___x_4905_);
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 1, v_val_4925_);
lean_ctor_set(v___x_4923_, 0, v___x_4905_);
v___x_4932_ = v___x_4923_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4905_);
lean_ctor_set(v_reuseFailAlloc_4936_, 1, v_val_4925_);
v___x_4932_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
lean_object* v___x_4934_; 
if (v_isShared_4930_ == 0)
{
lean_ctor_set(v___x_4929_, 0, v___x_4932_);
v___x_4934_ = v___x_4929_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4932_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
v_a_4897_ = v___x_4934_;
goto v___jp_4896_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_4910_);
v_a_4897_ = v_b_4888_;
goto v___jp_4896_;
}
}
else
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
lean_dec(v_b_4888_);
lean_dec_ref(v___x_4884_);
v_a_4941_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4909_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4909_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
else
{
v_a_4897_ = v_b_4888_;
goto v___jp_4896_;
}
}
v___jp_4896_:
{
size_t v___x_4898_; size_t v___x_4899_; 
v___x_4898_ = ((size_t)1ULL);
v___x_4899_ = lean_usize_add(v_i_4887_, v___x_4898_);
v_i_4887_ = v___x_4899_;
v_b_4888_ = v_a_4897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object* v___x_4949_, lean_object* v___x_4950_, lean_object* v_as_4951_, lean_object* v_sz_4952_, lean_object* v_i_4953_, lean_object* v_b_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_){
_start:
{
size_t v_sz_boxed_4962_; size_t v_i_boxed_4963_; lean_object* v_res_4964_; 
v_sz_boxed_4962_ = lean_unbox_usize(v_sz_4952_);
lean_dec(v_sz_4952_);
v_i_boxed_4963_ = lean_unbox_usize(v_i_4953_);
lean_dec(v_i_4953_);
v_res_4964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v___x_4949_, v___x_4950_, v_as_4951_, v_sz_boxed_4962_, v_i_boxed_4963_, v_b_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_);
lean_dec(v___y_4960_);
lean_dec_ref(v___y_4959_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
lean_dec(v___y_4956_);
lean_dec_ref(v___y_4955_);
lean_dec_ref(v_as_4951_);
lean_dec_ref(v___x_4949_);
return v_res_4964_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1(void){
_start:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4966_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__0));
v___x_4967_ = l_Lean_stringToMessageData(v___x_4966_);
return v___x_4967_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3(void){
_start:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4969_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__2));
v___x_4970_ = l_Lean_stringToMessageData(v___x_4969_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(lean_object* v_fp_4971_, lean_object* v_info_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_){
_start:
{
lean_object* v___x_4985_; lean_object* v_frameDB_4986_; lean_object* v_tree_4987_; lean_object* v_entries_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_5125_; 
v___x_4985_ = lean_st_ref_get(v_a_4974_);
v_frameDB_4986_ = lean_ctor_get(v___x_4985_, 4);
lean_inc_ref(v_frameDB_4986_);
lean_dec(v___x_4985_);
v_tree_4987_ = lean_ctor_get(v_frameDB_4986_, 0);
v_entries_4988_ = lean_ctor_get(v_frameDB_4986_, 1);
v_isSharedCheck_5125_ = !lean_is_exclusive(v_frameDB_4986_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_4990_ = v_frameDB_4986_;
v_isShared_4991_ = v_isSharedCheck_5125_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_entries_4988_);
lean_inc(v_tree_4987_);
lean_dec(v_frameDB_4986_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_5125_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; uint8_t v___x_4994_; 
v___x_4992_ = lean_array_get_size(v_entries_4988_);
v___x_4993_ = lean_unsigned_to_nat(0u);
v___x_4994_ = lean_nat_dec_eq(v___x_4992_, v___x_4993_);
if (v___x_4994_ == 0)
{
lean_object* v___x_4995_; lean_object* v_mctx_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; size_t v_sz_5000_; size_t v___x_5001_; lean_object* v___x_5002_; 
v___x_4995_ = lean_st_ref_get(v_a_4981_);
v_mctx_4996_ = lean_ctor_get(v___x_4995_, 0);
lean_inc_ref(v_mctx_4996_);
lean_dec(v___x_4995_);
v___x_4997_ = lean_box(0);
v___x_4998_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_4972_);
v___x_4999_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_4996_, v_tree_4987_, v___x_4998_);
lean_dec_ref(v_tree_4987_);
lean_dec_ref(v_mctx_4996_);
v_sz_5000_ = lean_array_size(v___x_4999_);
v___x_5001_ = ((size_t)0ULL);
lean_inc_ref(v___x_4998_);
v___x_5002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v_entries_4988_, v___x_4998_, v___x_4999_, v_sz_5000_, v___x_5001_, v___x_4997_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
lean_dec_ref(v___x_4999_);
lean_dec_ref(v_entries_4988_);
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5114_; 
v_a_5003_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5005_ = v___x_5002_;
v_isShared_5006_ = v_isSharedCheck_5114_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_5002_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5114_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
if (lean_obj_tag(v_a_5003_) == 1)
{
lean_object* v_val_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5110_; 
lean_del_object(v___x_5005_);
v_val_5007_ = lean_ctor_get(v_a_5003_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v_a_5003_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5009_ = v_a_5003_;
v_isShared_5010_ = v_isSharedCheck_5110_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_val_5007_);
lean_dec(v_a_5003_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5110_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v_fst_5011_; lean_object* v_snd_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5109_; 
v_fst_5011_ = lean_ctor_get(v_val_5007_, 0);
v_snd_5012_ = lean_ctor_get(v_val_5007_, 1);
v_isSharedCheck_5109_ = !lean_is_exclusive(v_val_5007_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_5014_ = v_val_5007_;
v_isShared_5015_ = v_isSharedCheck_5109_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_snd_5012_);
lean_inc(v_fst_5011_);
lean_dec(v_val_5007_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5109_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5016_; lean_object* v_frameDB_5017_; lean_object* v_specBackwardRuleCache_5018_; lean_object* v_splitBackwardRuleCache_5019_; lean_object* v_latticeBackwardRuleCache_5020_; lean_object* v_frameBackwardRuleCache_5021_; lean_object* v_invariants_5022_; lean_object* v_vcs_5023_; lean_object* v_simpState_5024_; lean_object* v_fuel_5025_; lean_object* v_inlineHandledInvariants_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5108_; 
v___x_5016_ = lean_st_ref_take(v_a_4974_);
v_frameDB_5017_ = lean_ctor_get(v___x_5016_, 4);
v_specBackwardRuleCache_5018_ = lean_ctor_get(v___x_5016_, 0);
v_splitBackwardRuleCache_5019_ = lean_ctor_get(v___x_5016_, 1);
v_latticeBackwardRuleCache_5020_ = lean_ctor_get(v___x_5016_, 2);
v_frameBackwardRuleCache_5021_ = lean_ctor_get(v___x_5016_, 3);
v_invariants_5022_ = lean_ctor_get(v___x_5016_, 5);
v_vcs_5023_ = lean_ctor_get(v___x_5016_, 6);
v_simpState_5024_ = lean_ctor_get(v___x_5016_, 7);
v_fuel_5025_ = lean_ctor_get(v___x_5016_, 8);
v_inlineHandledInvariants_5026_ = lean_ctor_get(v___x_5016_, 9);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5028_ = v___x_5016_;
v_isShared_5029_ = v_isSharedCheck_5108_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_inlineHandledInvariants_5026_);
lean_inc(v_fuel_5025_);
lean_inc(v_simpState_5024_);
lean_inc(v_vcs_5023_);
lean_inc(v_invariants_5022_);
lean_inc(v_frameDB_5017_);
lean_inc(v_frameBackwardRuleCache_5021_);
lean_inc(v_latticeBackwardRuleCache_5020_);
lean_inc(v_splitBackwardRuleCache_5019_);
lean_inc(v_specBackwardRuleCache_5018_);
lean_dec(v___x_5016_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5108_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v_tree_5030_; lean_object* v_entries_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5107_; 
v_tree_5030_ = lean_ctor_get(v_frameDB_5017_, 0);
v_entries_5031_ = lean_ctor_get(v_frameDB_5017_, 1);
v_isSharedCheck_5107_ = !lean_is_exclusive(v_frameDB_5017_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5033_ = v_frameDB_5017_;
v_isShared_5034_ = v_isSharedCheck_5107_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_entries_5031_);
lean_inc(v_tree_5030_);
lean_dec(v_frameDB_5017_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5107_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v_pat_5035_; lean_object* v_varNames_5036_; lean_object* v_frameStx_5037_; lean_object* v_srcIdx_5038_; uint8_t v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5043_; 
v_pat_5035_ = lean_ctor_get(v_fst_5011_, 0);
v_varNames_5036_ = lean_ctor_get(v_fst_5011_, 1);
v_frameStx_5037_ = lean_ctor_get(v_fst_5011_, 2);
v_srcIdx_5038_ = lean_ctor_get(v_fst_5011_, 3);
v___x_5039_ = 1;
lean_inc(v_srcIdx_5038_);
lean_inc(v_frameStx_5037_);
lean_inc_ref(v_varNames_5036_);
lean_inc_ref(v_pat_5035_);
v___x_5040_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_5040_, 0, v_pat_5035_);
lean_ctor_set(v___x_5040_, 1, v_varNames_5036_);
lean_ctor_set(v___x_5040_, 2, v_frameStx_5037_);
lean_ctor_set(v___x_5040_, 3, v_srcIdx_5038_);
lean_ctor_set_uint8(v___x_5040_, sizeof(void*)*4, v___x_5039_);
v___x_5041_ = lean_array_set(v_entries_5031_, v_srcIdx_5038_, v___x_5040_);
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 1, v___x_5041_);
v___x_5043_ = v___x_5033_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_tree_5030_);
lean_ctor_set(v_reuseFailAlloc_5106_, 1, v___x_5041_);
v___x_5043_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
lean_object* v___x_5045_; 
if (v_isShared_5029_ == 0)
{
lean_ctor_set(v___x_5028_, 4, v___x_5043_);
v___x_5045_ = v___x_5028_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_specBackwardRuleCache_5018_);
lean_ctor_set(v_reuseFailAlloc_5105_, 1, v_splitBackwardRuleCache_5019_);
lean_ctor_set(v_reuseFailAlloc_5105_, 2, v_latticeBackwardRuleCache_5020_);
lean_ctor_set(v_reuseFailAlloc_5105_, 3, v_frameBackwardRuleCache_5021_);
lean_ctor_set(v_reuseFailAlloc_5105_, 4, v___x_5043_);
lean_ctor_set(v_reuseFailAlloc_5105_, 5, v_invariants_5022_);
lean_ctor_set(v_reuseFailAlloc_5105_, 6, v_vcs_5023_);
lean_ctor_set(v_reuseFailAlloc_5105_, 7, v_simpState_5024_);
lean_ctor_set(v_reuseFailAlloc_5105_, 8, v_fuel_5025_);
lean_ctor_set(v_reuseFailAlloc_5105_, 9, v_inlineHandledInvariants_5026_);
v___x_5045_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
lean_object* v___x_5046_; lean_object* v_mkResourceTy_5047_; lean_object* v___x_5048_; 
v___x_5046_ = lean_st_ref_put(v_a_4974_, v___x_5045_);
v_mkResourceTy_5047_ = lean_ctor_get(v_fp_4971_, 3);
lean_inc_ref(v_mkResourceTy_5047_);
lean_dec_ref(v_fp_4971_);
lean_inc(v_a_4983_);
lean_inc_ref(v_a_4982_);
lean_inc(v_a_4981_);
lean_inc_ref(v_a_4980_);
v___x_5048_ = lean_apply_6(v_mkResourceTy_5047_, v_info_4972_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, lean_box(0));
if (lean_obj_tag(v___x_5048_) == 0)
{
lean_object* v_a_5049_; lean_object* v___x_5050_; 
v_a_5049_ = lean_ctor_get(v___x_5048_, 0);
lean_inc(v_a_5049_);
lean_dec_ref_known(v___x_5048_, 1);
v___x_5050_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(v_a_5049_, v_fst_5011_, v_snd_5012_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_object* v_a_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5088_; 
v_a_5051_ = lean_ctor_get(v___x_5050_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5053_ = v___x_5050_;
v_isShared_5054_ = v_isSharedCheck_5088_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_a_5051_);
lean_dec(v___x_5050_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5088_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v_options_5062_; uint8_t v_hasTrace_5063_; 
v_options_5062_ = lean_ctor_get(v_a_4982_, 2);
v_hasTrace_5063_ = lean_ctor_get_uint8(v_options_5062_, sizeof(void*)*1);
if (v_hasTrace_5063_ == 0)
{
lean_del_object(v___x_5014_);
lean_dec_ref(v___x_4998_);
lean_del_object(v___x_4990_);
goto v___jp_5055_;
}
else
{
lean_object* v_inheritedTraceOptions_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; uint8_t v___x_5067_; 
v_inheritedTraceOptions_5064_ = lean_ctor_get(v_a_4982_, 13);
v___x_5065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5066_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5067_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5064_, v_options_5062_, v___x_5066_);
if (v___x_5067_ == 0)
{
lean_del_object(v___x_5014_);
lean_dec_ref(v___x_4998_);
lean_del_object(v___x_4990_);
goto v___jp_5055_;
}
else
{
lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5071_; 
v___x_5068_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1, &l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1);
v___x_5069_ = l_Lean_MessageData_ofExpr(v___x_4998_);
if (v_isShared_5015_ == 0)
{
lean_ctor_set_tag(v___x_5014_, 7);
lean_ctor_set(v___x_5014_, 1, v___x_5069_);
lean_ctor_set(v___x_5014_, 0, v___x_5068_);
v___x_5071_ = v___x_5014_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v___x_5068_);
lean_ctor_set(v_reuseFailAlloc_5087_, 1, v___x_5069_);
v___x_5071_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
lean_object* v___x_5072_; lean_object* v___x_5074_; 
v___x_5072_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3);
if (v_isShared_4991_ == 0)
{
lean_ctor_set_tag(v___x_4990_, 7);
lean_ctor_set(v___x_4990_, 1, v___x_5072_);
lean_ctor_set(v___x_4990_, 0, v___x_5071_);
v___x_5074_ = v___x_4990_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v___x_5071_);
lean_ctor_set(v_reuseFailAlloc_5086_, 1, v___x_5072_);
v___x_5074_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
lean_inc(v_a_5051_);
v___x_5075_ = l_Lean_indentExpr(v_a_5051_);
v___x_5076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5074_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5065_, v___x_5076_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_dec_ref_known(v___x_5077_, 1);
goto v___jp_5055_;
}
else
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5085_; 
lean_del_object(v___x_5053_);
lean_dec(v_a_5051_);
lean_del_object(v___x_5009_);
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5080_ = v___x_5077_;
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5077_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5083_; 
if (v_isShared_5081_ == 0)
{
v___x_5083_ = v___x_5080_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_a_5078_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
}
}
}
}
}
v___jp_5055_:
{
lean_object* v___x_5057_; 
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 0, v_a_5051_);
v___x_5057_ = v___x_5009_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_a_5051_);
v___x_5057_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
lean_object* v___x_5059_; 
if (v_isShared_5054_ == 0)
{
lean_ctor_set(v___x_5053_, 0, v___x_5057_);
v___x_5059_ = v___x_5053_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5057_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
}
}
}
else
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5096_; 
lean_del_object(v___x_5014_);
lean_del_object(v___x_5009_);
lean_dec_ref(v___x_4998_);
lean_del_object(v___x_4990_);
v_a_5089_ = lean_ctor_get(v___x_5050_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5091_ = v___x_5050_;
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5050_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
if (v_isShared_5092_ == 0)
{
v___x_5094_ = v___x_5091_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5089_);
v___x_5094_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
return v___x_5094_;
}
}
}
}
else
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5104_; 
lean_del_object(v___x_5014_);
lean_dec(v_snd_5012_);
lean_dec(v_fst_5011_);
lean_del_object(v___x_5009_);
lean_dec_ref(v___x_4998_);
lean_del_object(v___x_4990_);
v_a_5097_ = lean_ctor_get(v___x_5048_, 0);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5048_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5099_ = v___x_5048_;
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5048_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5102_; 
if (v_isShared_5100_ == 0)
{
v___x_5102_ = v___x_5099_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5097_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
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
lean_object* v___x_5112_; 
lean_dec(v_a_5003_);
lean_dec_ref(v___x_4998_);
lean_del_object(v___x_4990_);
lean_dec_ref(v_info_4972_);
lean_dec_ref(v_fp_4971_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 0, v___x_4997_);
v___x_5112_ = v___x_5005_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_4997_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
}
else
{
lean_object* v_a_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5122_; 
lean_dec_ref(v___x_4998_);
lean_del_object(v___x_4990_);
lean_dec_ref(v_info_4972_);
lean_dec_ref(v_fp_4971_);
v_a_5115_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5117_ = v___x_5002_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_5002_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5120_; 
if (v_isShared_5118_ == 0)
{
v___x_5120_ = v___x_5117_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
}
}
else
{
lean_object* v___x_5123_; lean_object* v___x_5124_; 
lean_del_object(v___x_4990_);
lean_dec_ref(v_entries_4988_);
lean_dec_ref(v_tree_4987_);
lean_dec_ref(v_info_4972_);
lean_dec_ref(v_fp_4971_);
v___x_5123_ = lean_box(0);
v___x_5124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5124_, 0, v___x_5123_);
return v___x_5124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___boxed(lean_object* v_fp_5126_, lean_object* v_info_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_){
_start:
{
lean_object* v_res_5140_; 
v_res_5140_ = l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(v_fp_5126_, v_info_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_);
lean_dec(v_a_5138_);
lean_dec_ref(v_a_5137_);
lean_dec(v_a_5136_);
lean_dec_ref(v_a_5135_);
lean_dec(v_a_5134_);
lean_dec_ref(v_a_5133_);
lean_dec(v_a_5132_);
lean_dec_ref(v_a_5131_);
lean_dec(v_a_5130_);
lean_dec(v_a_5129_);
lean_dec_ref(v_a_5128_);
return v_res_5140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0(lean_object* v___x_5141_, lean_object* v___x_5142_, lean_object* v_as_5143_, size_t v_sz_5144_, size_t v_i_5145_, lean_object* v_b_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
lean_object* v___x_5159_; 
v___x_5159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v___x_5141_, v___x_5142_, v_as_5143_, v_sz_5144_, v_i_5145_, v_b_5146_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_);
return v___x_5159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___boxed(lean_object** _args){
lean_object* v___x_5160_ = _args[0];
lean_object* v___x_5161_ = _args[1];
lean_object* v_as_5162_ = _args[2];
lean_object* v_sz_5163_ = _args[3];
lean_object* v_i_5164_ = _args[4];
lean_object* v_b_5165_ = _args[5];
lean_object* v___y_5166_ = _args[6];
lean_object* v___y_5167_ = _args[7];
lean_object* v___y_5168_ = _args[8];
lean_object* v___y_5169_ = _args[9];
lean_object* v___y_5170_ = _args[10];
lean_object* v___y_5171_ = _args[11];
lean_object* v___y_5172_ = _args[12];
lean_object* v___y_5173_ = _args[13];
lean_object* v___y_5174_ = _args[14];
lean_object* v___y_5175_ = _args[15];
lean_object* v___y_5176_ = _args[16];
lean_object* v___y_5177_ = _args[17];
_start:
{
size_t v_sz_boxed_5178_; size_t v_i_boxed_5179_; lean_object* v_res_5180_; 
v_sz_boxed_5178_ = lean_unbox_usize(v_sz_5163_);
lean_dec(v_sz_5163_);
v_i_boxed_5179_ = lean_unbox_usize(v_i_5164_);
lean_dec(v_i_5164_);
v_res_5180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0(v___x_5160_, v___x_5161_, v_as_5162_, v_sz_boxed_5178_, v_i_boxed_5179_, v_b_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
lean_dec(v___y_5174_);
lean_dec_ref(v___y_5173_);
lean_dec(v___y_5172_);
lean_dec_ref(v___y_5171_);
lean_dec(v___y_5170_);
lean_dec_ref(v___y_5169_);
lean_dec(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
lean_dec_ref(v_as_5162_);
lean_dec_ref(v___x_5160_);
return v_res_5180_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost(lean_object* v_post_5188_){
_start:
{
lean_object* v___y_5190_; uint8_t v___x_5195_; 
v___x_5195_ = l_Lean_Expr_isLambda(v_post_5188_);
if (v___x_5195_ == 0)
{
v___y_5190_ = v_post_5188_;
goto v___jp_5189_;
}
else
{
lean_object* v___x_5196_; 
v___x_5196_ = l_Lean_Expr_bindingBody_x21(v_post_5188_);
lean_dec_ref(v_post_5188_);
v___y_5190_ = v___x_5196_;
goto v___jp_5189_;
}
v___jp_5189_:
{
lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; uint8_t v___x_5194_; 
v___x_5191_ = l_Lean_Expr_consumeMData(v___y_5190_);
lean_dec_ref(v___y_5190_);
v___x_5192_ = l_Lean_Expr_getAppFn(v___x_5191_);
lean_dec_ref(v___x_5191_);
v___x_5193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___closed__2));
v___x_5194_ = l_Lean_Expr_isConstOf(v___x_5192_, v___x_5193_);
lean_dec_ref(v___x_5192_);
return v___x_5194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost___boxed(lean_object* v_post_5197_){
_start:
{
uint8_t v_res_5198_; lean_object* v_r_5199_; 
v_res_5198_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost(v_post_5197_);
v_r_5199_ = lean_box(v_res_5198_);
return v_r_5199_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1(void){
_start:
{
lean_object* v___x_5201_; lean_object* v___x_5202_; 
v___x_5201_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__0));
v___x_5202_ = l_Lean_stringToMessageData(v___x_5201_);
return v___x_5202_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3(void){
_start:
{
lean_object* v___x_5204_; lean_object* v___x_5205_; 
v___x_5204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__2));
v___x_5205_ = l_Lean_stringToMessageData(v___x_5204_);
return v___x_5205_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5(void){
_start:
{
lean_object* v___x_5207_; lean_object* v___x_5208_; 
v___x_5207_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__4));
v___x_5208_ = l_Lean_stringToMessageData(v___x_5207_);
return v___x_5208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule(lean_object* v_goal_5209_, lean_object* v_info_5210_, lean_object* v_fp_5211_, lean_object* v_split_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_){
_start:
{
lean_object* v___x_5225_; 
lean_inc_ref(v_info_5210_);
v___x_5225_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_5211_, v_info_5210_, v_a_5214_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v_a_5226_; lean_object* v_rule_5227_; lean_object* v_splitVCIdx_5228_; lean_object* v_frameIdx_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; 
v_a_5226_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_a_5226_);
lean_dec_ref_known(v___x_5225_, 1);
v_rule_5227_ = lean_ctor_get(v_a_5226_, 0);
lean_inc_ref(v_rule_5227_);
v_splitVCIdx_5228_ = lean_ctor_get(v_a_5226_, 1);
lean_inc(v_splitVCIdx_5228_);
v_frameIdx_5229_ = lean_ctor_get(v_a_5226_, 2);
lean_inc(v_frameIdx_5229_);
lean_dec(v_a_5226_);
v___x_5230_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__1);
v___x_5231_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5210_);
v___x_5232_ = l_Lean_indentExpr(v___x_5231_);
lean_inc_ref(v___x_5232_);
v___x_5233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5233_, 0, v___x_5230_);
lean_ctor_set(v___x_5233_, 1, v___x_5232_);
v___x_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5234_, 0, v___x_5233_);
v___x_5235_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_5227_, v_goal_5209_, v___x_5234_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
if (lean_obj_tag(v___x_5235_) == 0)
{
lean_object* v_a_5236_; 
v_a_5236_ = lean_ctor_get(v___x_5235_, 0);
lean_inc(v_a_5236_);
lean_dec_ref_known(v___x_5235_, 1);
if (lean_obj_tag(v_a_5236_) == 1)
{
lean_object* v_mvarIds_5237_; lean_object* v_frame_5238_; lean_object* v_residualPre_5239_; lean_object* v_splitVCProof_5240_; lean_object* v_subgoals_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; 
lean_dec_ref(v___x_5232_);
v_mvarIds_5237_ = lean_ctor_get(v_a_5236_, 0);
lean_inc(v_mvarIds_5237_);
lean_dec_ref_known(v_a_5236_, 1);
v_frame_5238_ = lean_ctor_get(v_split_5212_, 0);
lean_inc_ref(v_frame_5238_);
v_residualPre_5239_ = lean_ctor_get(v_split_5212_, 1);
lean_inc(v_residualPre_5239_);
v_splitVCProof_5240_ = lean_ctor_get(v_split_5212_, 2);
lean_inc_ref(v_splitVCProof_5240_);
v_subgoals_5241_ = lean_ctor_get(v_split_5212_, 3);
lean_inc(v_subgoals_5241_);
lean_dec_ref(v_split_5212_);
v___x_5242_ = lean_box(0);
v___x_5243_ = lean_array_mk(v_mvarIds_5237_);
v___x_5244_ = lean_array_get(v___x_5242_, v___x_5243_, v_frameIdx_5229_);
lean_dec(v_frameIdx_5229_);
v___x_5245_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v___x_5244_, v_frame_5238_, v_a_5221_);
lean_dec_ref(v___x_5245_);
v___x_5246_ = lean_array_get(v___x_5242_, v___x_5243_, v_splitVCIdx_5228_);
lean_dec(v_splitVCIdx_5228_);
lean_inc(v___x_5246_);
v___x_5247_ = l_Lean_MVarId_getType(v___x_5246_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
if (lean_obj_tag(v___x_5247_) == 0)
{
lean_object* v_a_5248_; lean_object* v___y_5250_; lean_object* v___y_5251_; lean_object* v___y_5252_; lean_object* v___y_5253_; lean_object* v___x_5258_; uint8_t v___x_5259_; 
v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
lean_inc_n(v_a_5248_, 2);
lean_dec_ref_known(v___x_5247_, 1);
v___x_5258_ = l_Lean_Expr_cleanupAnnotations(v_a_5248_);
v___x_5259_ = l_Lean_Expr_isApp(v___x_5258_);
if (v___x_5259_ == 0)
{
lean_dec_ref(v___x_5258_);
lean_dec(v___x_5246_);
lean_dec_ref(v___x_5243_);
lean_dec(v_subgoals_5241_);
lean_dec_ref(v_splitVCProof_5240_);
lean_dec(v_residualPre_5239_);
lean_dec_ref(v_info_5210_);
v___y_5250_ = v_a_5220_;
v___y_5251_ = v_a_5221_;
v___y_5252_ = v_a_5222_;
v___y_5253_ = v_a_5223_;
goto v___jp_5249_;
}
else
{
lean_object* v_arg_5260_; lean_object* v___x_5261_; uint8_t v___x_5262_; 
v_arg_5260_ = lean_ctor_get(v___x_5258_, 1);
lean_inc_ref(v_arg_5260_);
v___x_5261_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5258_);
v___x_5262_ = l_Lean_Expr_isApp(v___x_5261_);
if (v___x_5262_ == 0)
{
lean_dec_ref(v___x_5261_);
lean_dec_ref(v_arg_5260_);
lean_dec(v___x_5246_);
lean_dec_ref(v___x_5243_);
lean_dec(v_subgoals_5241_);
lean_dec_ref(v_splitVCProof_5240_);
lean_dec(v_residualPre_5239_);
lean_dec_ref(v_info_5210_);
v___y_5250_ = v_a_5220_;
v___y_5251_ = v_a_5221_;
v___y_5252_ = v_a_5222_;
v___y_5253_ = v_a_5223_;
goto v___jp_5249_;
}
else
{
lean_object* v___x_5263_; uint8_t v___x_5264_; 
v___x_5263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5261_);
v___x_5264_ = l_Lean_Expr_isApp(v___x_5263_);
if (v___x_5264_ == 0)
{
lean_dec_ref(v___x_5263_);
lean_dec_ref(v_arg_5260_);
lean_dec(v___x_5246_);
lean_dec_ref(v___x_5243_);
lean_dec(v_subgoals_5241_);
lean_dec_ref(v_splitVCProof_5240_);
lean_dec(v_residualPre_5239_);
lean_dec_ref(v_info_5210_);
v___y_5250_ = v_a_5220_;
v___y_5251_ = v_a_5221_;
v___y_5252_ = v_a_5222_;
v___y_5253_ = v_a_5223_;
goto v___jp_5249_;
}
else
{
lean_object* v___x_5265_; uint8_t v___x_5266_; 
v___x_5265_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5263_);
v___x_5266_ = l_Lean_Expr_isApp(v___x_5265_);
if (v___x_5266_ == 0)
{
lean_dec_ref(v___x_5265_);
lean_dec_ref(v_arg_5260_);
lean_dec(v___x_5246_);
lean_dec_ref(v___x_5243_);
lean_dec(v_subgoals_5241_);
lean_dec_ref(v_splitVCProof_5240_);
lean_dec(v_residualPre_5239_);
lean_dec_ref(v_info_5210_);
v___y_5250_ = v_a_5220_;
v___y_5251_ = v_a_5221_;
v___y_5252_ = v_a_5222_;
v___y_5253_ = v_a_5223_;
goto v___jp_5249_;
}
else
{
lean_object* v___x_5267_; lean_object* v___x_5268_; uint8_t v___x_5269_; 
v___x_5267_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5265_);
v___x_5268_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10));
v___x_5269_ = l_Lean_Expr_isConstOf(v___x_5267_, v___x_5268_);
lean_dec_ref(v___x_5267_);
if (v___x_5269_ == 0)
{
lean_dec_ref(v_arg_5260_);
lean_dec(v___x_5246_);
lean_dec_ref(v___x_5243_);
lean_dec(v_subgoals_5241_);
lean_dec_ref(v_splitVCProof_5240_);
lean_dec(v_residualPre_5239_);
lean_dec_ref(v_info_5210_);
v___y_5250_ = v_a_5220_;
v___y_5251_ = v_a_5221_;
v___y_5252_ = v_a_5222_;
v___y_5253_ = v_a_5223_;
goto v___jp_5249_;
}
else
{
lean_object* v_excessArgs_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5284_; 
lean_dec(v_a_5248_);
v_excessArgs_5270_ = lean_ctor_get(v_info_5210_, 2);
lean_inc_ref(v_excessArgs_5270_);
lean_dec_ref(v_info_5210_);
v___x_5271_ = lean_array_get_size(v_excessArgs_5270_);
lean_dec_ref(v_excessArgs_5270_);
v___x_5272_ = l_Lean_Expr_stripArgsN(v_arg_5260_, v___x_5271_);
lean_dec_ref(v_arg_5260_);
v___x_5273_ = l_Lean_Expr_appArg_x21(v___x_5272_);
lean_dec_ref(v___x_5272_);
v___x_5274_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v_residualPre_5239_, v___x_5273_, v_a_5221_);
lean_dec_ref(v___x_5274_);
v___x_5275_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f_spec__0___redArg(v___x_5246_, v_splitVCProof_5240_, v_a_5221_);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5275_);
if (v_isSharedCheck_5284_ == 0)
{
lean_object* v_unused_5285_; 
v_unused_5285_ = lean_ctor_get(v___x_5275_, 0);
lean_dec(v_unused_5285_);
v___x_5277_ = v___x_5275_;
v_isShared_5278_ = v_isSharedCheck_5284_;
goto v_resetjp_5276_;
}
else
{
lean_dec(v___x_5275_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5284_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5282_; 
v___x_5279_ = lean_array_to_list(v___x_5243_);
v___x_5280_ = l_List_appendTR___redArg(v___x_5279_, v_subgoals_5241_);
if (v_isShared_5278_ == 0)
{
lean_ctor_set(v___x_5277_, 0, v___x_5280_);
v___x_5282_ = v___x_5277_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5280_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
}
}
}
}
v___jp_5249_:
{
lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; 
v___x_5254_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__3);
v___x_5255_ = l_Lean_indentExpr(v_a_5248_);
v___x_5256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5256_, 0, v___x_5254_);
lean_ctor_set(v___x_5256_, 1, v___x_5255_);
v___x_5257_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5256_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_);
return v___x_5257_;
}
}
else
{
lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5293_; 
lean_dec(v___x_5246_);
lean_dec_ref(v___x_5243_);
lean_dec(v_subgoals_5241_);
lean_dec_ref(v_splitVCProof_5240_);
lean_dec(v_residualPre_5239_);
lean_dec_ref(v_info_5210_);
v_a_5286_ = lean_ctor_get(v___x_5247_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5247_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5288_ = v___x_5247_;
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___x_5247_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5291_; 
if (v_isShared_5289_ == 0)
{
v___x_5291_ = v___x_5288_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
}
else
{
lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
lean_dec(v_a_5236_);
lean_dec(v_frameIdx_5229_);
lean_dec(v_splitVCIdx_5228_);
lean_dec_ref(v_split_5212_);
lean_dec_ref(v_info_5210_);
v___x_5294_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___closed__5);
v___x_5295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5294_);
lean_ctor_set(v___x_5295_, 1, v___x_5232_);
v___x_5296_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5295_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
return v___x_5296_;
}
}
else
{
lean_object* v_a_5297_; lean_object* v___x_5299_; uint8_t v_isShared_5300_; uint8_t v_isSharedCheck_5304_; 
lean_dec_ref(v___x_5232_);
lean_dec(v_frameIdx_5229_);
lean_dec(v_splitVCIdx_5228_);
lean_dec_ref(v_split_5212_);
lean_dec_ref(v_info_5210_);
v_a_5297_ = lean_ctor_get(v___x_5235_, 0);
v_isSharedCheck_5304_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5299_ = v___x_5235_;
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
else
{
lean_inc(v_a_5297_);
lean_dec(v___x_5235_);
v___x_5299_ = lean_box(0);
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
v_resetjp_5298_:
{
lean_object* v___x_5302_; 
if (v_isShared_5300_ == 0)
{
v___x_5302_ = v___x_5299_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v_a_5297_);
v___x_5302_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
return v___x_5302_;
}
}
}
}
else
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5312_; 
lean_dec_ref(v_split_5212_);
lean_dec_ref(v_info_5210_);
lean_dec(v_goal_5209_);
v_a_5305_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5307_ = v___x_5225_;
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5225_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
if (v_isShared_5308_ == 0)
{
v___x_5310_ = v___x_5307_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
v___x_5310_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
return v___x_5310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule___boxed(lean_object* v_goal_5313_, lean_object* v_info_5314_, lean_object* v_fp_5315_, lean_object* v_split_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_){
_start:
{
lean_object* v_res_5329_; 
v_res_5329_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule(v_goal_5313_, v_info_5314_, v_fp_5315_, v_split_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_);
lean_dec(v_a_5327_);
lean_dec_ref(v_a_5326_);
lean_dec(v_a_5325_);
lean_dec_ref(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
lean_dec(v_a_5318_);
lean_dec_ref(v_a_5317_);
return v_res_5329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0(lean_object* v_mkOpAppM_5330_, lean_object* v_info_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_){
_start:
{
lean_object* v___x_5339_; 
lean_inc(v___y_5337_);
lean_inc_ref(v___y_5336_);
lean_inc(v___y_5335_);
lean_inc_ref(v___y_5334_);
v___x_5339_ = lean_apply_6(v_mkOpAppM_5330_, v_info_5331_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, lean_box(0));
if (lean_obj_tag(v___x_5339_) == 0)
{
lean_object* v_a_5340_; lean_object* v___x_5341_; 
v_a_5340_ = lean_ctor_get(v___x_5339_, 0);
lean_inc(v_a_5340_);
lean_dec_ref_known(v___x_5339_, 1);
v___x_5341_ = l_Lean_Meta_Sym_shareCommon(v_a_5340_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
return v___x_5341_;
}
else
{
return v___x_5339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0___boxed(lean_object* v_mkOpAppM_5342_, lean_object* v_info_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_){
_start:
{
lean_object* v_res_5351_; 
v_res_5351_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0(v_mkOpAppM_5342_, v_info_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
lean_dec(v___y_5349_);
lean_dec_ref(v___y_5348_);
lean_dec(v___y_5347_);
lean_dec_ref(v___y_5346_);
lean_dec(v___y_5345_);
lean_dec_ref(v___y_5344_);
return v_res_5351_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(lean_object* v_a_5352_, lean_object* v_a_5353_){
_start:
{
if (lean_obj_tag(v_a_5352_) == 0)
{
lean_object* v___x_5354_; 
v___x_5354_ = l_List_reverse___redArg(v_a_5353_);
return v___x_5354_;
}
else
{
lean_object* v_head_5355_; lean_object* v_tail_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5365_; 
v_head_5355_ = lean_ctor_get(v_a_5352_, 0);
v_tail_5356_ = lean_ctor_get(v_a_5352_, 1);
v_isSharedCheck_5365_ = !lean_is_exclusive(v_a_5352_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5358_ = v_a_5352_;
v_isShared_5359_ = v_isSharedCheck_5365_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_tail_5356_);
lean_inc(v_head_5355_);
lean_dec(v_a_5352_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5365_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5360_; lean_object* v___x_5362_; 
v___x_5360_ = l_Lean_MessageData_ofExpr(v_head_5355_);
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 1, v_a_5353_);
lean_ctor_set(v___x_5358_, 0, v___x_5360_);
v___x_5362_ = v___x_5358_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v___x_5360_);
lean_ctor_set(v_reuseFailAlloc_5364_, 1, v_a_5353_);
v___x_5362_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
v_a_5352_ = v_tail_5356_;
v_a_5353_ = v___x_5362_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(lean_object* v_a_5366_, lean_object* v_x_5367_){
_start:
{
if (lean_obj_tag(v_x_5367_) == 0)
{
lean_object* v___x_5368_; 
v___x_5368_ = lean_box(0);
return v___x_5368_;
}
else
{
lean_object* v_key_5369_; lean_object* v_value_5370_; lean_object* v_tail_5371_; uint8_t v___x_5372_; 
v_key_5369_ = lean_ctor_get(v_x_5367_, 0);
v_value_5370_ = lean_ctor_get(v_x_5367_, 1);
v_tail_5371_ = lean_ctor_get(v_x_5367_, 2);
v___x_5372_ = lean_name_eq(v_key_5369_, v_a_5366_);
if (v___x_5372_ == 0)
{
v_x_5367_ = v_tail_5371_;
goto _start;
}
else
{
lean_object* v___x_5374_; 
lean_inc(v_value_5370_);
v___x_5374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5374_, 0, v_value_5370_);
return v___x_5374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg___boxed(lean_object* v_a_5375_, lean_object* v_x_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(v_a_5375_, v_x_5376_);
lean_dec(v_x_5376_);
lean_dec(v_a_5375_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(lean_object* v_m_5378_, lean_object* v_a_5379_){
_start:
{
lean_object* v_buckets_5380_; lean_object* v___x_5381_; uint64_t v___y_5383_; 
v_buckets_5380_ = lean_ctor_get(v_m_5378_, 1);
v___x_5381_ = lean_array_get_size(v_buckets_5380_);
if (lean_obj_tag(v_a_5379_) == 0)
{
uint64_t v___x_5397_; 
v___x_5397_ = 1723ULL;
v___y_5383_ = v___x_5397_;
goto v___jp_5382_;
}
else
{
uint64_t v_hash_5398_; 
v_hash_5398_ = lean_ctor_get_uint64(v_a_5379_, sizeof(void*)*2);
v___y_5383_ = v_hash_5398_;
goto v___jp_5382_;
}
v___jp_5382_:
{
uint64_t v___x_5384_; uint64_t v___x_5385_; uint64_t v_fold_5386_; uint64_t v___x_5387_; uint64_t v___x_5388_; uint64_t v___x_5389_; size_t v___x_5390_; size_t v___x_5391_; size_t v___x_5392_; size_t v___x_5393_; size_t v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; 
v___x_5384_ = 32ULL;
v___x_5385_ = lean_uint64_shift_right(v___y_5383_, v___x_5384_);
v_fold_5386_ = lean_uint64_xor(v___y_5383_, v___x_5385_);
v___x_5387_ = 16ULL;
v___x_5388_ = lean_uint64_shift_right(v_fold_5386_, v___x_5387_);
v___x_5389_ = lean_uint64_xor(v_fold_5386_, v___x_5388_);
v___x_5390_ = lean_uint64_to_usize(v___x_5389_);
v___x_5391_ = lean_usize_of_nat(v___x_5381_);
v___x_5392_ = ((size_t)1ULL);
v___x_5393_ = lean_usize_sub(v___x_5391_, v___x_5392_);
v___x_5394_ = lean_usize_land(v___x_5390_, v___x_5393_);
v___x_5395_ = lean_array_uget_borrowed(v_buckets_5380_, v___x_5394_);
v___x_5396_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(v_a_5379_, v___x_5395_);
return v___x_5396_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg___boxed(lean_object* v_m_5399_, lean_object* v_a_5400_){
_start:
{
lean_object* v_res_5401_; 
v_res_5401_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(v_m_5399_, v_a_5400_);
lean_dec(v_a_5400_);
lean_dec_ref(v_m_5399_);
return v_res_5401_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1(void){
_start:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__0));
v___x_5404_ = l_Lean_stringToMessageData(v___x_5403_);
return v___x_5404_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3(void){
_start:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; 
v___x_5406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__2));
v___x_5407_ = l_Lean_stringToMessageData(v___x_5406_);
return v___x_5407_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5(void){
_start:
{
lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__4));
v___x_5410_ = l_Lean_stringToMessageData(v___x_5409_);
return v___x_5410_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7(void){
_start:
{
lean_object* v___x_5412_; lean_object* v___x_5413_; 
v___x_5412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__6));
v___x_5413_ = l_Lean_stringToMessageData(v___x_5412_);
return v___x_5413_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9(void){
_start:
{
lean_object* v___x_5415_; lean_object* v___x_5416_; 
v___x_5415_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__8));
v___x_5416_ = l_Lean_stringToMessageData(v___x_5415_);
return v___x_5416_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11(void){
_start:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__10));
v___x_5419_ = l_Lean_stringToMessageData(v___x_5418_);
return v___x_5419_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13(void){
_start:
{
lean_object* v___x_5421_; lean_object* v___x_5422_; 
v___x_5421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__12));
v___x_5422_ = l_Lean_stringToMessageData(v___x_5421_);
return v___x_5422_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15(void){
_start:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; 
v___x_5424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__14));
v___x_5425_ = l_Lean_stringToMessageData(v___x_5424_);
return v___x_5425_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17(void){
_start:
{
lean_object* v___x_5427_; lean_object* v___x_5428_; 
v___x_5427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__16));
v___x_5428_ = l_Lean_stringToMessageData(v___x_5427_);
return v___x_5428_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19(void){
_start:
{
lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__18));
v___x_5431_ = l_Lean_stringToMessageData(v___x_5430_);
return v___x_5431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(lean_object* v_scope_5432_, lean_object* v_goal_5433_, lean_object* v_info_5434_, lean_object* v_thm_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_){
_start:
{
lean_object* v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v___y_5455_; lean_object* v___y_5456_; lean_object* v___y_5457_; lean_object* v___y_5458_; lean_object* v___y_5459_; lean_object* v___y_5460_; lean_object* v___y_5497_; lean_object* v___y_5498_; lean_object* v___y_5499_; lean_object* v___y_5500_; lean_object* v___y_5501_; lean_object* v___y_5502_; lean_object* v___y_5503_; lean_object* v___y_5504_; lean_object* v___y_5505_; lean_object* v___y_5506_; lean_object* v___y_5507_; lean_object* v___y_5508_; lean_object* v___y_5509_; lean_object* v___y_5510_; lean_object* v___y_5511_; lean_object* v___y_5536_; lean_object* v___y_5537_; lean_object* v___y_5538_; lean_object* v___y_5539_; lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v___y_5542_; lean_object* v___y_5543_; lean_object* v___y_5544_; lean_object* v___y_5545_; lean_object* v___y_5546_; lean_object* v___y_5547_; lean_object* v___y_5575_; lean_object* v___y_5576_; lean_object* v___y_5577_; lean_object* v___y_5578_; lean_object* v___y_5579_; lean_object* v___y_5580_; lean_object* v___y_5581_; lean_object* v___y_5582_; lean_object* v___y_5583_; lean_object* v___y_5584_; lean_object* v___y_5585_; lean_object* v___y_5586_; lean_object* v___y_5587_; lean_object* v___y_5618_; lean_object* v___y_5619_; lean_object* v___y_5672_; lean_object* v___y_5675_; lean_object* v___x_5705_; 
lean_inc_ref(v_info_5434_);
lean_inc_ref(v_thm_5435_);
v___x_5705_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(v_thm_5435_, v_info_5434_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
if (lean_obj_tag(v___x_5705_) == 0)
{
v___y_5675_ = v___x_5705_;
goto v___jp_5674_;
}
else
{
lean_object* v_a_5706_; lean_object* v___y_5708_; lean_object* v___y_5709_; lean_object* v___y_5710_; uint8_t v___y_5740_; uint8_t v___x_5771_; 
v_a_5706_ = lean_ctor_get(v___x_5705_, 0);
lean_inc(v_a_5706_);
v___x_5771_ = l_Lean_Exception_isInterrupt(v_a_5706_);
if (v___x_5771_ == 0)
{
uint8_t v___x_5772_; 
lean_inc(v_a_5706_);
v___x_5772_ = l_Lean_Exception_isRuntime(v_a_5706_);
v___y_5740_ = v___x_5772_;
goto v___jp_5739_;
}
else
{
v___y_5740_ = v___x_5771_;
goto v___jp_5739_;
}
v___jp_5707_:
{
lean_object* v_excessArgs_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; 
v_excessArgs_5711_ = lean_ctor_get(v_info_5434_, 2);
lean_inc_ref(v___y_5709_);
v___x_5712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___y_5709_);
lean_ctor_set(v___x_5712_, 1, v___y_5710_);
v___x_5713_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_5714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5712_);
lean_ctor_set(v___x_5714_, 1, v___x_5713_);
v___x_5715_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5434_);
v___x_5716_ = l_Lean_indentExpr(v___x_5715_);
v___x_5717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5714_);
lean_ctor_set(v___x_5717_, 1, v___x_5716_);
v___x_5718_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11);
v___x_5719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5717_);
lean_ctor_set(v___x_5719_, 1, v___x_5718_);
v___x_5720_ = l_Lean_Exception_toMessageData(v_a_5706_);
v___x_5721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5719_);
lean_ctor_set(v___x_5721_, 1, v___x_5720_);
v___x_5722_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13);
v___x_5723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5723_, 0, v___x_5721_);
lean_ctor_set(v___x_5723_, 1, v___x_5722_);
v___x_5724_ = l_Lean_indentExpr(v___y_5708_);
v___x_5725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5725_, 0, v___x_5723_);
lean_ctor_set(v___x_5725_, 1, v___x_5724_);
v___x_5726_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15);
v___x_5727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5725_);
lean_ctor_set(v___x_5727_, 1, v___x_5726_);
v___x_5728_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_5434_);
v___x_5729_ = l_Lean_indentExpr(v___x_5728_);
v___x_5730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5727_);
lean_ctor_set(v___x_5730_, 1, v___x_5729_);
v___x_5731_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17);
v___x_5732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5730_);
lean_ctor_set(v___x_5732_, 1, v___x_5731_);
lean_inc_ref(v_excessArgs_5711_);
v___x_5733_ = lean_array_to_list(v_excessArgs_5711_);
v___x_5734_ = lean_box(0);
v___x_5735_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(v___x_5733_, v___x_5734_);
v___x_5736_ = l_Lean_MessageData_ofList(v___x_5735_);
v___x_5737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5732_);
lean_ctor_set(v___x_5737_, 1, v___x_5736_);
v___x_5738_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5737_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
v___y_5675_ = v___x_5738_;
goto v___jp_5674_;
}
v___jp_5739_:
{
if (v___y_5740_ == 0)
{
lean_object* v___x_5741_; 
lean_dec_ref_known(v___x_5705_, 1);
lean_inc(v_goal_5433_);
v___x_5741_ = l_Lean_MVarId_getType(v_goal_5433_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
if (lean_obj_tag(v___x_5741_) == 0)
{
lean_object* v_a_5742_; lean_object* v_proof_5743_; lean_object* v___x_5744_; 
v_a_5742_ = lean_ctor_get(v___x_5741_, 0);
lean_inc(v_a_5742_);
lean_dec_ref_known(v___x_5741_, 1);
v_proof_5743_ = lean_ctor_get(v_thm_5435_, 1);
v___x_5744_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19);
switch(lean_obj_tag(v_proof_5743_))
{
case 0:
{
lean_object* v_declName_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; 
v_declName_5745_ = lean_ctor_get(v_proof_5743_, 0);
v___x_5746_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_5745_);
v___x_5747_ = l_Lean_MessageData_ofName(v_declName_5745_);
v___x_5748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5746_);
lean_ctor_set(v___x_5748_, 1, v___x_5747_);
v___y_5708_ = v_a_5742_;
v___y_5709_ = v___x_5744_;
v___y_5710_ = v___x_5748_;
goto v___jp_5707_;
}
case 1:
{
lean_object* v_fvarId_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; 
v_fvarId_5749_ = lean_ctor_get(v_proof_5743_, 0);
v___x_5750_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_5749_);
v___x_5751_ = l_Lean_mkFVar(v_fvarId_5749_);
v___x_5752_ = l_Lean_MessageData_ofExpr(v___x_5751_);
v___x_5753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5750_);
lean_ctor_set(v___x_5753_, 1, v___x_5752_);
v___y_5708_ = v_a_5742_;
v___y_5709_ = v___x_5744_;
v___y_5710_ = v___x_5753_;
goto v___jp_5707_;
}
default: 
{
lean_object* v_ref_5754_; lean_object* v_proof_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; 
v_ref_5754_ = lean_ctor_get(v_proof_5743_, 1);
v_proof_5755_ = lean_ctor_get(v_proof_5743_, 2);
v___x_5756_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_5754_);
v___x_5757_ = l_Lean_MessageData_ofSyntax(v_ref_5754_);
v___x_5758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5758_, 0, v___x_5756_);
lean_ctor_set(v___x_5758_, 1, v___x_5757_);
v___x_5759_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_5760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5760_, 0, v___x_5758_);
lean_ctor_set(v___x_5760_, 1, v___x_5759_);
lean_inc_ref(v_proof_5755_);
v___x_5761_ = l_Lean_MessageData_ofExpr(v_proof_5755_);
v___x_5762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5760_);
lean_ctor_set(v___x_5762_, 1, v___x_5761_);
v___y_5708_ = v_a_5742_;
v___y_5709_ = v___x_5744_;
v___y_5710_ = v___x_5762_;
goto v___jp_5707_;
}
}
}
else
{
lean_object* v_a_5763_; lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5770_; 
lean_dec(v_a_5706_);
lean_dec_ref(v_thm_5435_);
lean_dec_ref(v_info_5434_);
lean_dec(v_goal_5433_);
lean_dec_ref(v_scope_5432_);
v_a_5763_ = lean_ctor_get(v___x_5741_, 0);
v_isSharedCheck_5770_ = !lean_is_exclusive(v___x_5741_);
if (v_isSharedCheck_5770_ == 0)
{
v___x_5765_ = v___x_5741_;
v_isShared_5766_ = v_isSharedCheck_5770_;
goto v_resetjp_5764_;
}
else
{
lean_inc(v_a_5763_);
lean_dec(v___x_5741_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5770_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
lean_object* v___x_5768_; 
if (v_isShared_5766_ == 0)
{
v___x_5768_ = v___x_5765_;
goto v_reusejp_5767_;
}
else
{
lean_object* v_reuseFailAlloc_5769_; 
v_reuseFailAlloc_5769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_a_5763_);
v___x_5768_ = v_reuseFailAlloc_5769_;
goto v_reusejp_5767_;
}
v_reusejp_5767_:
{
return v___x_5768_;
}
}
}
}
else
{
lean_dec(v_a_5706_);
v___y_5675_ = v___x_5705_;
goto v___jp_5674_;
}
}
}
v___jp_5448_:
{
lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; 
v___x_5461_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1);
v___x_5462_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5434_);
lean_dec_ref(v_info_5434_);
v___x_5463_ = l_Lean_indentExpr(v___x_5462_);
v___x_5464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5464_, 0, v___x_5461_);
lean_ctor_set(v___x_5464_, 1, v___x_5463_);
v___x_5465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5465_, 0, v___x_5464_);
v___x_5466_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v___y_5449_, v_goal_5433_, v___x_5465_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_);
if (lean_obj_tag(v___x_5466_) == 0)
{
lean_object* v_a_5467_; lean_object* v___x_5469_; uint8_t v_isShared_5470_; uint8_t v_isSharedCheck_5487_; 
v_a_5467_ = lean_ctor_get(v___x_5466_, 0);
v_isSharedCheck_5487_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5487_ == 0)
{
v___x_5469_ = v___x_5466_;
v_isShared_5470_ = v_isSharedCheck_5487_;
goto v_resetjp_5468_;
}
else
{
lean_inc(v_a_5467_);
lean_dec(v___x_5466_);
v___x_5469_ = lean_box(0);
v_isShared_5470_ = v_isSharedCheck_5487_;
goto v_resetjp_5468_;
}
v_resetjp_5468_:
{
if (lean_obj_tag(v_a_5467_) == 1)
{
lean_object* v_mvarIds_5471_; lean_object* v___x_5473_; uint8_t v_isShared_5474_; uint8_t v_isSharedCheck_5482_; 
v_mvarIds_5471_ = lean_ctor_get(v_a_5467_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v_a_5467_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5473_ = v_a_5467_;
v_isShared_5474_ = v_isSharedCheck_5482_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_mvarIds_5471_);
lean_dec(v_a_5467_);
v___x_5473_ = lean_box(0);
v_isShared_5474_ = v_isSharedCheck_5482_;
goto v_resetjp_5472_;
}
v_resetjp_5472_:
{
lean_object* v___x_5475_; lean_object* v___x_5477_; 
v___x_5475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5475_, 0, v_scope_5432_);
lean_ctor_set(v___x_5475_, 1, v_mvarIds_5471_);
if (v_isShared_5474_ == 0)
{
lean_ctor_set(v___x_5473_, 0, v___x_5475_);
v___x_5477_ = v___x_5473_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v___x_5475_);
v___x_5477_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
lean_object* v___x_5479_; 
if (v_isShared_5470_ == 0)
{
lean_ctor_set(v___x_5469_, 0, v___x_5477_);
v___x_5479_ = v___x_5469_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v___x_5477_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
}
else
{
lean_object* v___x_5483_; lean_object* v___x_5485_; 
lean_dec(v_a_5467_);
lean_dec_ref(v_scope_5432_);
v___x_5483_ = lean_box(0);
if (v_isShared_5470_ == 0)
{
lean_ctor_set(v___x_5469_, 0, v___x_5483_);
v___x_5485_ = v___x_5469_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v___x_5483_);
v___x_5485_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
return v___x_5485_;
}
}
}
}
else
{
lean_object* v_a_5488_; lean_object* v___x_5490_; uint8_t v_isShared_5491_; uint8_t v_isSharedCheck_5495_; 
lean_dec_ref(v_scope_5432_);
v_a_5488_ = lean_ctor_get(v___x_5466_, 0);
v_isSharedCheck_5495_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5495_ == 0)
{
v___x_5490_ = v___x_5466_;
v_isShared_5491_ = v_isSharedCheck_5495_;
goto v_resetjp_5489_;
}
else
{
lean_inc(v_a_5488_);
lean_dec(v___x_5466_);
v___x_5490_ = lean_box(0);
v_isShared_5491_ = v_isSharedCheck_5495_;
goto v_resetjp_5489_;
}
v_resetjp_5489_:
{
lean_object* v___x_5493_; 
if (v_isShared_5491_ == 0)
{
v___x_5493_ = v___x_5490_;
goto v_reusejp_5492_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v_a_5488_);
v___x_5493_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5492_;
}
v_reusejp_5492_:
{
return v___x_5493_;
}
}
}
}
v___jp_5496_:
{
lean_object* v_excessArgs_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; 
v_excessArgs_5512_ = lean_ctor_get(v_info_5434_, 2);
lean_inc_ref(v___y_5502_);
v___x_5513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5513_, 0, v___y_5502_);
lean_ctor_set(v___x_5513_, 1, v___y_5511_);
v___x_5514_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_5515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5515_, 0, v___x_5513_);
lean_ctor_set(v___x_5515_, 1, v___x_5514_);
v___x_5516_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5434_);
v___x_5517_ = l_Lean_MessageData_ofExpr(v___x_5516_);
v___x_5518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5518_, 0, v___x_5515_);
lean_ctor_set(v___x_5518_, 1, v___x_5517_);
v___x_5519_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5);
v___x_5520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5520_, 0, v___x_5518_);
lean_ctor_set(v___x_5520_, 1, v___x_5519_);
lean_inc_ref(v_excessArgs_5512_);
v___x_5521_ = lean_array_to_list(v_excessArgs_5512_);
v___x_5522_ = lean_box(0);
v___x_5523_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(v___x_5521_, v___x_5522_);
v___x_5524_ = l_Lean_MessageData_ofList(v___x_5523_);
v___x_5525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5525_, 0, v___x_5520_);
lean_ctor_set(v___x_5525_, 1, v___x_5524_);
lean_inc(v___y_5507_);
v___x_5526_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___y_5507_, v___x_5525_, v___y_5506_, v___y_5497_, v___y_5505_, v___y_5499_);
if (lean_obj_tag(v___x_5526_) == 0)
{
lean_dec_ref_known(v___x_5526_, 1);
v___y_5449_ = v___y_5508_;
v___y_5450_ = v___y_5510_;
v___y_5451_ = v___y_5504_;
v___y_5452_ = v___y_5501_;
v___y_5453_ = v___y_5500_;
v___y_5454_ = v___y_5509_;
v___y_5455_ = v___y_5498_;
v___y_5456_ = v___y_5503_;
v___y_5457_ = v___y_5506_;
v___y_5458_ = v___y_5497_;
v___y_5459_ = v___y_5505_;
v___y_5460_ = v___y_5499_;
goto v___jp_5448_;
}
else
{
lean_object* v_a_5527_; lean_object* v___x_5529_; uint8_t v_isShared_5530_; uint8_t v_isSharedCheck_5534_; 
lean_dec_ref(v___y_5508_);
lean_dec_ref(v_info_5434_);
lean_dec(v_goal_5433_);
lean_dec_ref(v_scope_5432_);
v_a_5527_ = lean_ctor_get(v___x_5526_, 0);
v_isSharedCheck_5534_ = !lean_is_exclusive(v___x_5526_);
if (v_isSharedCheck_5534_ == 0)
{
v___x_5529_ = v___x_5526_;
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
else
{
lean_inc(v_a_5527_);
lean_dec(v___x_5526_);
v___x_5529_ = lean_box(0);
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
v_resetjp_5528_:
{
lean_object* v___x_5532_; 
if (v_isShared_5530_ == 0)
{
v___x_5532_ = v___x_5529_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_a_5527_);
v___x_5532_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
return v___x_5532_;
}
}
}
}
v___jp_5535_:
{
lean_object* v_options_5548_; uint8_t v_hasTrace_5549_; 
v_options_5548_ = lean_ctor_get(v___y_5546_, 2);
v_hasTrace_5549_ = lean_ctor_get_uint8(v_options_5548_, sizeof(void*)*1);
if (v_hasTrace_5549_ == 0)
{
lean_dec_ref(v_thm_5435_);
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
v___y_5460_ = v___y_5547_;
goto v___jp_5448_;
}
else
{
lean_object* v_inheritedTraceOptions_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; uint8_t v___x_5553_; 
v_inheritedTraceOptions_5550_ = lean_ctor_get(v___y_5546_, 13);
v___x_5551_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5552_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5553_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5550_, v_options_5548_, v___x_5552_);
if (v___x_5553_ == 0)
{
lean_dec_ref(v_thm_5435_);
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
v___y_5460_ = v___y_5547_;
goto v___jp_5448_;
}
else
{
lean_object* v_proof_5554_; lean_object* v___x_5555_; 
v_proof_5554_ = lean_ctor_get(v_thm_5435_, 1);
lean_inc_ref(v_proof_5554_);
lean_dec_ref(v_thm_5435_);
v___x_5555_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7);
switch(lean_obj_tag(v_proof_5554_))
{
case 0:
{
lean_object* v_declName_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; 
v_declName_5556_ = lean_ctor_get(v_proof_5554_, 0);
lean_inc(v_declName_5556_);
lean_dec_ref_known(v_proof_5554_, 1);
v___x_5557_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_5558_ = l_Lean_MessageData_ofName(v_declName_5556_);
v___x_5559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5559_, 0, v___x_5557_);
lean_ctor_set(v___x_5559_, 1, v___x_5558_);
v___y_5497_ = v___y_5545_;
v___y_5498_ = v___y_5542_;
v___y_5499_ = v___y_5547_;
v___y_5500_ = v___y_5540_;
v___y_5501_ = v___y_5539_;
v___y_5502_ = v___x_5555_;
v___y_5503_ = v___y_5543_;
v___y_5504_ = v___y_5538_;
v___y_5505_ = v___y_5546_;
v___y_5506_ = v___y_5544_;
v___y_5507_ = v___x_5551_;
v___y_5508_ = v___y_5536_;
v___y_5509_ = v___y_5541_;
v___y_5510_ = v___y_5537_;
v___y_5511_ = v___x_5559_;
goto v___jp_5496_;
}
case 1:
{
lean_object* v_fvarId_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; 
v_fvarId_5560_ = lean_ctor_get(v_proof_5554_, 0);
lean_inc(v_fvarId_5560_);
lean_dec_ref_known(v_proof_5554_, 1);
v___x_5561_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_5562_ = l_Lean_mkFVar(v_fvarId_5560_);
v___x_5563_ = l_Lean_MessageData_ofExpr(v___x_5562_);
v___x_5564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5564_, 0, v___x_5561_);
lean_ctor_set(v___x_5564_, 1, v___x_5563_);
v___y_5497_ = v___y_5545_;
v___y_5498_ = v___y_5542_;
v___y_5499_ = v___y_5547_;
v___y_5500_ = v___y_5540_;
v___y_5501_ = v___y_5539_;
v___y_5502_ = v___x_5555_;
v___y_5503_ = v___y_5543_;
v___y_5504_ = v___y_5538_;
v___y_5505_ = v___y_5546_;
v___y_5506_ = v___y_5544_;
v___y_5507_ = v___x_5551_;
v___y_5508_ = v___y_5536_;
v___y_5509_ = v___y_5541_;
v___y_5510_ = v___y_5537_;
v___y_5511_ = v___x_5564_;
goto v___jp_5496_;
}
default: 
{
lean_object* v_ref_5565_; lean_object* v_proof_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; 
v_ref_5565_ = lean_ctor_get(v_proof_5554_, 1);
lean_inc(v_ref_5565_);
v_proof_5566_ = lean_ctor_get(v_proof_5554_, 2);
lean_inc_ref(v_proof_5566_);
lean_dec_ref_known(v_proof_5554_, 3);
v___x_5567_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_5568_ = l_Lean_MessageData_ofSyntax(v_ref_5565_);
v___x_5569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5569_, 0, v___x_5567_);
lean_ctor_set(v___x_5569_, 1, v___x_5568_);
v___x_5570_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_5571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5571_, 0, v___x_5569_);
lean_ctor_set(v___x_5571_, 1, v___x_5570_);
v___x_5572_ = l_Lean_MessageData_ofExpr(v_proof_5566_);
v___x_5573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5573_, 0, v___x_5571_);
lean_ctor_set(v___x_5573_, 1, v___x_5572_);
v___y_5497_ = v___y_5545_;
v___y_5498_ = v___y_5542_;
v___y_5499_ = v___y_5547_;
v___y_5500_ = v___y_5540_;
v___y_5501_ = v___y_5539_;
v___y_5502_ = v___x_5555_;
v___y_5503_ = v___y_5543_;
v___y_5504_ = v___y_5538_;
v___y_5505_ = v___y_5546_;
v___y_5506_ = v___y_5544_;
v___y_5507_ = v___x_5551_;
v___y_5508_ = v___y_5536_;
v___y_5509_ = v___y_5541_;
v___y_5510_ = v___y_5537_;
v___y_5511_ = v___x_5573_;
goto v___jp_5496_;
}
}
}
}
}
v___jp_5574_:
{
lean_object* v___x_5588_; 
v___x_5588_ = l_Lean_Elab_Tactic_VCGen_FrameSplit_instantiateMVarsS(v___y_5576_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_);
if (lean_obj_tag(v___x_5588_) == 0)
{
lean_object* v_a_5589_; lean_object* v___x_5590_; 
v_a_5589_ = lean_ctor_get(v___x_5588_, 0);
lean_inc(v_a_5589_);
lean_dec_ref_known(v___x_5588_, 1);
v___x_5590_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applyFrameRule(v_goal_5433_, v_info_5434_, v___y_5575_, v_a_5589_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_);
if (lean_obj_tag(v___x_5590_) == 0)
{
lean_object* v_a_5591_; lean_object* v___x_5593_; uint8_t v_isShared_5594_; uint8_t v_isSharedCheck_5600_; 
v_a_5591_ = lean_ctor_get(v___x_5590_, 0);
v_isSharedCheck_5600_ = !lean_is_exclusive(v___x_5590_);
if (v_isSharedCheck_5600_ == 0)
{
v___x_5593_ = v___x_5590_;
v_isShared_5594_ = v_isSharedCheck_5600_;
goto v_resetjp_5592_;
}
else
{
lean_inc(v_a_5591_);
lean_dec(v___x_5590_);
v___x_5593_ = lean_box(0);
v_isShared_5594_ = v_isSharedCheck_5600_;
goto v_resetjp_5592_;
}
v_resetjp_5592_:
{
lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5598_; 
v___x_5595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5595_, 0, v_scope_5432_);
lean_ctor_set(v___x_5595_, 1, v_a_5591_);
v___x_5596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5596_, 0, v___x_5595_);
if (v_isShared_5594_ == 0)
{
lean_ctor_set(v___x_5593_, 0, v___x_5596_);
v___x_5598_ = v___x_5593_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5599_; 
v_reuseFailAlloc_5599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5599_, 0, v___x_5596_);
v___x_5598_ = v_reuseFailAlloc_5599_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
return v___x_5598_;
}
}
}
else
{
lean_object* v_a_5601_; lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5608_; 
lean_dec_ref(v_scope_5432_);
v_a_5601_ = lean_ctor_get(v___x_5590_, 0);
v_isSharedCheck_5608_ = !lean_is_exclusive(v___x_5590_);
if (v_isSharedCheck_5608_ == 0)
{
v___x_5603_ = v___x_5590_;
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
else
{
lean_inc(v_a_5601_);
lean_dec(v___x_5590_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5606_; 
if (v_isShared_5604_ == 0)
{
v___x_5606_ = v___x_5603_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_a_5601_);
v___x_5606_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
return v___x_5606_;
}
}
}
}
else
{
lean_object* v_a_5609_; lean_object* v___x_5611_; uint8_t v_isShared_5612_; uint8_t v_isSharedCheck_5616_; 
lean_dec_ref(v___y_5575_);
lean_dec_ref(v_info_5434_);
lean_dec(v_goal_5433_);
lean_dec_ref(v_scope_5432_);
v_a_5609_ = lean_ctor_get(v___x_5588_, 0);
v_isSharedCheck_5616_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5616_ == 0)
{
v___x_5611_ = v___x_5588_;
v_isShared_5612_ = v_isSharedCheck_5616_;
goto v_resetjp_5610_;
}
else
{
lean_inc(v_a_5609_);
lean_dec(v___x_5588_);
v___x_5611_ = lean_box(0);
v_isShared_5612_ = v_isSharedCheck_5616_;
goto v_resetjp_5610_;
}
v_resetjp_5610_:
{
lean_object* v___x_5614_; 
if (v_isShared_5612_ == 0)
{
v___x_5614_ = v___x_5611_;
goto v_reusejp_5613_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v_a_5609_);
v___x_5614_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5613_;
}
v_reusejp_5613_:
{
return v___x_5614_;
}
}
}
}
v___jp_5617_:
{
lean_object* v___x_5620_; 
lean_inc_ref(v_info_5434_);
lean_inc_ref(v___y_5619_);
v___x_5620_ = l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(v___y_5619_, v_info_5434_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
if (lean_obj_tag(v___x_5620_) == 0)
{
lean_object* v_a_5621_; lean_object* v_mkOpAppM_5622_; lean_object* v_proc_5623_; lean_object* v___x_5624_; lean_object* v___f_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; 
v_a_5621_ = lean_ctor_get(v___x_5620_, 0);
lean_inc(v_a_5621_);
lean_dec_ref_known(v___x_5620_, 1);
v_mkOpAppM_5622_ = lean_ctor_get(v___y_5619_, 2);
v_proc_5623_ = lean_ctor_get(v___y_5619_, 4);
lean_inc_ref(v_thm_5435_);
v___x_5624_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorem_global_x3f(v_thm_5435_);
lean_inc_ref_n(v_info_5434_, 2);
lean_inc_ref(v_mkOpAppM_5622_);
v___f_5625_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5625_, 0, v_mkOpAppM_5622_);
lean_closure_set(v___f_5625_, 1, v_info_5434_);
lean_inc_ref(v___y_5618_);
lean_inc(v_goal_5433_);
v___x_5626_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5626_, 0, v_info_5434_);
lean_ctor_set(v___x_5626_, 1, v_goal_5433_);
lean_ctor_set(v___x_5626_, 2, v_a_5621_);
lean_ctor_set(v___x_5626_, 3, v___x_5624_);
lean_ctor_set(v___x_5626_, 4, v___y_5618_);
lean_ctor_set(v___x_5626_, 5, v___f_5625_);
lean_inc_ref(v_proc_5623_);
lean_inc(v_a_5446_);
lean_inc_ref(v_a_5445_);
lean_inc(v_a_5444_);
lean_inc_ref(v_a_5443_);
lean_inc(v_a_5442_);
lean_inc_ref(v_a_5441_);
v___x_5627_ = lean_apply_8(v_proc_5623_, v___x_5626_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_, lean_box(0));
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_object* v_a_5628_; 
v_a_5628_ = lean_ctor_get(v___x_5627_, 0);
lean_inc(v_a_5628_);
lean_dec_ref_known(v___x_5627_, 1);
if (lean_obj_tag(v_a_5628_) == 1)
{
lean_object* v_options_5629_; uint8_t v_hasTrace_5630_; 
lean_dec_ref(v___y_5618_);
lean_dec_ref(v_thm_5435_);
v_options_5629_ = lean_ctor_get(v_a_5445_, 2);
v_hasTrace_5630_ = lean_ctor_get_uint8(v_options_5629_, sizeof(void*)*1);
if (v_hasTrace_5630_ == 0)
{
lean_object* v_val_5631_; 
v_val_5631_ = lean_ctor_get(v_a_5628_, 0);
lean_inc(v_val_5631_);
lean_dec_ref_known(v_a_5628_, 1);
v___y_5575_ = v___y_5619_;
v___y_5576_ = v_val_5631_;
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
v___y_5587_ = v_a_5446_;
goto v___jp_5574_;
}
else
{
lean_object* v_val_5632_; lean_object* v_inheritedTraceOptions_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; uint8_t v___x_5636_; 
v_val_5632_ = lean_ctor_get(v_a_5628_, 0);
lean_inc(v_val_5632_);
lean_dec_ref_known(v_a_5628_, 1);
v_inheritedTraceOptions_5633_ = lean_ctor_get(v_a_5445_, 13);
v___x_5634_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5635_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5636_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5633_, v_options_5629_, v___x_5635_);
if (v___x_5636_ == 0)
{
v___y_5575_ = v___y_5619_;
v___y_5576_ = v_val_5632_;
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
v___y_5587_ = v_a_5446_;
goto v___jp_5574_;
}
else
{
lean_object* v_frame_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; 
v_frame_5637_ = lean_ctor_get(v_val_5632_, 0);
v___x_5638_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9);
v___x_5639_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5434_);
v___x_5640_ = l_Lean_MessageData_ofExpr(v___x_5639_);
v___x_5641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5638_);
lean_ctor_set(v___x_5641_, 1, v___x_5640_);
v___x_5642_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3);
v___x_5643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5641_);
lean_ctor_set(v___x_5643_, 1, v___x_5642_);
lean_inc_ref(v_frame_5637_);
v___x_5644_ = l_Lean_indentExpr(v_frame_5637_);
v___x_5645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5643_);
lean_ctor_set(v___x_5645_, 1, v___x_5644_);
v___x_5646_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5634_, v___x_5645_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
if (lean_obj_tag(v___x_5646_) == 0)
{
lean_dec_ref_known(v___x_5646_, 1);
v___y_5575_ = v___y_5619_;
v___y_5576_ = v_val_5632_;
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
v___y_5587_ = v_a_5446_;
goto v___jp_5574_;
}
else
{
lean_object* v_a_5647_; lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5654_; 
lean_dec(v_val_5632_);
lean_dec_ref(v___y_5619_);
lean_dec_ref(v_info_5434_);
lean_dec(v_goal_5433_);
lean_dec_ref(v_scope_5432_);
v_a_5647_ = lean_ctor_get(v___x_5646_, 0);
v_isSharedCheck_5654_ = !lean_is_exclusive(v___x_5646_);
if (v_isSharedCheck_5654_ == 0)
{
v___x_5649_ = v___x_5646_;
v_isShared_5650_ = v_isSharedCheck_5654_;
goto v_resetjp_5648_;
}
else
{
lean_inc(v_a_5647_);
lean_dec(v___x_5646_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5654_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v___x_5652_; 
if (v_isShared_5650_ == 0)
{
v___x_5652_ = v___x_5649_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5653_; 
v_reuseFailAlloc_5653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5653_, 0, v_a_5647_);
v___x_5652_ = v_reuseFailAlloc_5653_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
return v___x_5652_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5628_);
lean_dec_ref(v___y_5619_);
v___y_5536_ = v___y_5618_;
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
v___y_5547_ = v_a_5446_;
goto v___jp_5535_;
}
}
else
{
lean_object* v_a_5655_; lean_object* v___x_5657_; uint8_t v_isShared_5658_; uint8_t v_isSharedCheck_5662_; 
lean_dec_ref(v___y_5619_);
lean_dec_ref(v___y_5618_);
lean_dec_ref(v_thm_5435_);
lean_dec_ref(v_info_5434_);
lean_dec(v_goal_5433_);
lean_dec_ref(v_scope_5432_);
v_a_5655_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5662_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5662_ == 0)
{
v___x_5657_ = v___x_5627_;
v_isShared_5658_ = v_isSharedCheck_5662_;
goto v_resetjp_5656_;
}
else
{
lean_inc(v_a_5655_);
lean_dec(v___x_5627_);
v___x_5657_ = lean_box(0);
v_isShared_5658_ = v_isSharedCheck_5662_;
goto v_resetjp_5656_;
}
v_resetjp_5656_:
{
lean_object* v___x_5660_; 
if (v_isShared_5658_ == 0)
{
v___x_5660_ = v___x_5657_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v_a_5655_);
v___x_5660_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
return v___x_5660_;
}
}
}
}
else
{
lean_object* v_a_5663_; lean_object* v___x_5665_; uint8_t v_isShared_5666_; uint8_t v_isSharedCheck_5670_; 
lean_dec_ref(v___y_5619_);
lean_dec_ref(v___y_5618_);
lean_dec_ref(v_thm_5435_);
lean_dec_ref(v_info_5434_);
lean_dec(v_goal_5433_);
lean_dec_ref(v_scope_5432_);
v_a_5663_ = lean_ctor_get(v___x_5620_, 0);
v_isSharedCheck_5670_ = !lean_is_exclusive(v___x_5620_);
if (v_isSharedCheck_5670_ == 0)
{
v___x_5665_ = v___x_5620_;
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
else
{
lean_inc(v_a_5663_);
lean_dec(v___x_5620_);
v___x_5665_ = lean_box(0);
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
v_resetjp_5664_:
{
lean_object* v___x_5668_; 
if (v_isShared_5666_ == 0)
{
v___x_5668_ = v___x_5665_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5663_);
v___x_5668_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
return v___x_5668_;
}
}
}
}
v___jp_5671_:
{
lean_object* v___x_5673_; 
v___x_5673_ = l_Lean_Elab_Tactic_VCGen_meetFrameProc;
v___y_5618_ = v___y_5672_;
v___y_5619_ = v___x_5673_;
goto v___jp_5617_;
}
v___jp_5674_:
{
if (lean_obj_tag(v___y_5675_) == 0)
{
lean_object* v_a_5676_; lean_object* v___x_5678_; uint8_t v_isShared_5679_; uint8_t v_isSharedCheck_5696_; 
v_a_5676_ = lean_ctor_get(v___y_5675_, 0);
v_isSharedCheck_5696_ = !lean_is_exclusive(v___y_5675_);
if (v_isSharedCheck_5696_ == 0)
{
v___x_5678_ = v___y_5675_;
v_isShared_5679_ = v_isSharedCheck_5696_;
goto v_resetjp_5677_;
}
else
{
lean_inc(v_a_5676_);
lean_dec(v___y_5675_);
v___x_5678_ = lean_box(0);
v_isShared_5679_ = v_isSharedCheck_5696_;
goto v_resetjp_5677_;
}
v_resetjp_5677_:
{
if (lean_obj_tag(v_a_5676_) == 1)
{
uint8_t v_conjunctivePre_5680_; 
lean_del_object(v___x_5678_);
v_conjunctivePre_5680_ = lean_ctor_get_uint8(v_thm_5435_, sizeof(void*)*4);
if (v_conjunctivePre_5680_ == 0)
{
lean_object* v_val_5681_; lean_object* v___x_5682_; uint8_t v___x_5683_; 
v_val_5681_ = lean_ctor_get(v_a_5676_, 0);
lean_inc(v_val_5681_);
lean_dec_ref_known(v_a_5676_, 1);
v___x_5682_ = l_Lean_Elab_Tactic_VCGen_WPApp_post(v_info_5434_);
v___x_5683_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isFramedPost(v___x_5682_);
if (v___x_5683_ == 0)
{
lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; 
v___x_5684_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v_info_5434_);
v___x_5685_ = l_Lean_Expr_getAppFn(v___x_5684_);
lean_dec_ref(v___x_5684_);
v___x_5686_ = l_Lean_Expr_constName_x3f(v___x_5685_);
lean_dec_ref(v___x_5685_);
if (lean_obj_tag(v___x_5686_) == 0)
{
v___y_5672_ = v_val_5681_;
goto v___jp_5671_;
}
else
{
lean_object* v_val_5687_; lean_object* v_frameProcs_5688_; lean_object* v___x_5689_; 
v_val_5687_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_val_5687_);
lean_dec_ref_known(v___x_5686_, 1);
v_frameProcs_5688_ = lean_ctor_get(v_a_5436_, 1);
v___x_5689_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(v_frameProcs_5688_, v_val_5687_);
lean_dec(v_val_5687_);
if (lean_obj_tag(v___x_5689_) == 0)
{
v___y_5672_ = v_val_5681_;
goto v___jp_5671_;
}
else
{
lean_object* v_val_5690_; 
v_val_5690_ = lean_ctor_get(v___x_5689_, 0);
lean_inc(v_val_5690_);
lean_dec_ref_known(v___x_5689_, 1);
v___y_5618_ = v_val_5681_;
v___y_5619_ = v_val_5690_;
goto v___jp_5617_;
}
}
}
else
{
v___y_5536_ = v_val_5681_;
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
v___y_5547_ = v_a_5446_;
goto v___jp_5535_;
}
}
else
{
lean_object* v_val_5691_; 
v_val_5691_ = lean_ctor_get(v_a_5676_, 0);
lean_inc(v_val_5691_);
lean_dec_ref_known(v_a_5676_, 1);
v___y_5536_ = v_val_5691_;
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
v___y_5547_ = v_a_5446_;
goto v___jp_5535_;
}
}
else
{
lean_object* v___x_5692_; lean_object* v___x_5694_; 
lean_dec(v_a_5676_);
lean_dec_ref(v_thm_5435_);
lean_dec_ref(v_info_5434_);
lean_dec(v_goal_5433_);
lean_dec_ref(v_scope_5432_);
v___x_5692_ = lean_box(0);
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 0, v___x_5692_);
v___x_5694_ = v___x_5678_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v___x_5692_);
v___x_5694_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
return v___x_5694_;
}
}
}
}
else
{
lean_object* v_a_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5704_; 
lean_dec_ref(v_thm_5435_);
lean_dec_ref(v_info_5434_);
lean_dec(v_goal_5433_);
lean_dec_ref(v_scope_5432_);
v_a_5697_ = lean_ctor_get(v___y_5675_, 0);
v_isSharedCheck_5704_ = !lean_is_exclusive(v___y_5675_);
if (v_isSharedCheck_5704_ == 0)
{
v___x_5699_ = v___y_5675_;
v_isShared_5700_ = v_isSharedCheck_5704_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_a_5697_);
lean_dec(v___y_5675_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5704_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
lean_object* v___x_5702_; 
if (v_isShared_5700_ == 0)
{
v___x_5702_ = v___x_5699_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_a_5697_);
v___x_5702_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
return v___x_5702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___boxed(lean_object* v_scope_5773_, lean_object* v_goal_5774_, lean_object* v_info_5775_, lean_object* v_thm_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_){
_start:
{
lean_object* v_res_5789_; 
v_res_5789_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(v_scope_5773_, v_goal_5774_, v_info_5775_, v_thm_5776_, v_a_5777_, v_a_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_);
lean_dec(v_a_5787_);
lean_dec_ref(v_a_5786_);
lean_dec(v_a_5785_);
lean_dec_ref(v_a_5784_);
lean_dec(v_a_5783_);
lean_dec_ref(v_a_5782_);
lean_dec(v_a_5781_);
lean_dec_ref(v_a_5780_);
lean_dec(v_a_5779_);
lean_dec(v_a_5778_);
lean_dec_ref(v_a_5777_);
return v_res_5789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1(lean_object* v_00_u03b2_5790_, lean_object* v_m_5791_, lean_object* v_a_5792_){
_start:
{
lean_object* v___x_5793_; 
v___x_5793_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___redArg(v_m_5791_, v_a_5792_);
return v___x_5793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1___boxed(lean_object* v_00_u03b2_5794_, lean_object* v_m_5795_, lean_object* v_a_5796_){
_start:
{
lean_object* v_res_5797_; 
v_res_5797_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1(v_00_u03b2_5794_, v_m_5795_, v_a_5796_);
lean_dec(v_a_5796_);
lean_dec_ref(v_m_5795_);
return v_res_5797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1(lean_object* v_00_u03b2_5798_, lean_object* v_a_5799_, lean_object* v_x_5800_){
_start:
{
lean_object* v___x_5801_; 
v___x_5801_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___redArg(v_a_5799_, v_x_5800_);
return v___x_5801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5802_, lean_object* v_a_5803_, lean_object* v_x_5804_){
_start:
{
lean_object* v_res_5805_; 
v_res_5805_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__1_spec__1(v_00_u03b2_5802_, v_a_5803_, v_x_5804_);
lean_dec(v_x_5804_);
lean_dec(v_a_5803_);
return v_res_5805_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_5810_; lean_object* v___x_5811_; 
v___x_5810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__1));
v___x_5811_ = l_Lean_stringToMessageData(v___x_5810_);
return v___x_5811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(lean_object* v_scope_5812_, lean_object* v_goal_5813_, lean_object* v_info_5814_, lean_object* v___x_5815_, lean_object* v_as_5816_, size_t v_sz_5817_, size_t v_i_5818_, lean_object* v_b_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_){
_start:
{
lean_object* v_a_5833_; uint8_t v___x_5837_; 
v___x_5837_ = lean_usize_dec_lt(v_i_5818_, v_sz_5817_);
if (v___x_5837_ == 0)
{
lean_object* v___x_5838_; 
lean_dec_ref(v___x_5815_);
lean_dec_ref(v_info_5814_);
lean_dec(v_goal_5813_);
lean_dec_ref(v_scope_5812_);
v___x_5838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5838_, 0, v_b_5819_);
return v___x_5838_;
}
else
{
lean_object* v_a_5839_; lean_object* v___x_5840_; 
lean_dec_ref(v_b_5819_);
v_a_5839_ = lean_array_uget_borrowed(v_as_5816_, v_i_5818_);
lean_inc(v_a_5839_);
lean_inc_ref(v_info_5814_);
lean_inc(v_goal_5813_);
lean_inc_ref(v_scope_5812_);
v___x_5840_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(v_scope_5812_, v_goal_5813_, v_info_5814_, v_a_5839_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
if (lean_obj_tag(v___x_5840_) == 0)
{
lean_object* v_a_5841_; lean_object* v___x_5843_; uint8_t v_isShared_5844_; uint8_t v_isSharedCheck_5893_; 
v_a_5841_ = lean_ctor_get(v___x_5840_, 0);
v_isSharedCheck_5893_ = !lean_is_exclusive(v___x_5840_);
if (v_isSharedCheck_5893_ == 0)
{
v___x_5843_ = v___x_5840_;
v_isShared_5844_ = v_isSharedCheck_5893_;
goto v_resetjp_5842_;
}
else
{
lean_inc(v_a_5841_);
lean_dec(v___x_5840_);
v___x_5843_ = lean_box(0);
v_isShared_5844_ = v_isSharedCheck_5893_;
goto v_resetjp_5842_;
}
v_resetjp_5842_:
{
lean_object* v___x_5845_; 
v___x_5845_ = lean_box(0);
if (lean_obj_tag(v_a_5841_) == 1)
{
lean_object* v___x_5846_; lean_object* v___x_5848_; 
lean_dec_ref(v___x_5815_);
lean_dec_ref(v_info_5814_);
lean_dec(v_goal_5813_);
lean_dec_ref(v_scope_5812_);
v___x_5846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5846_, 0, v_a_5841_);
lean_ctor_set(v___x_5846_, 1, v___x_5845_);
if (v_isShared_5844_ == 0)
{
lean_ctor_set(v___x_5843_, 0, v___x_5846_);
v___x_5848_ = v___x_5843_;
goto v_reusejp_5847_;
}
else
{
lean_object* v_reuseFailAlloc_5849_; 
v_reuseFailAlloc_5849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5849_, 0, v___x_5846_);
v___x_5848_ = v_reuseFailAlloc_5849_;
goto v_reusejp_5847_;
}
v_reusejp_5847_:
{
return v___x_5848_;
}
}
else
{
lean_object* v_options_5850_; lean_object* v_inheritedTraceOptions_5851_; uint8_t v_hasTrace_5852_; lean_object* v___x_5853_; 
lean_del_object(v___x_5843_);
lean_dec(v_a_5841_);
v_options_5850_ = lean_ctor_get(v___y_5829_, 2);
v_inheritedTraceOptions_5851_ = lean_ctor_get(v___y_5829_, 13);
v_hasTrace_5852_ = lean_ctor_get_uint8(v_options_5850_, sizeof(void*)*1);
v___x_5853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0));
if (v_hasTrace_5852_ == 0)
{
v_a_5833_ = v___x_5853_;
goto v___jp_5832_;
}
else
{
lean_object* v___x_5854_; lean_object* v___x_5855_; uint8_t v___x_5856_; 
v___x_5854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5855_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5856_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5851_, v_options_5850_, v___x_5855_);
if (v___x_5856_ == 0)
{
v_a_5833_ = v___x_5853_;
goto v___jp_5832_;
}
else
{
lean_object* v_proof_5857_; lean_object* v___x_5858_; lean_object* v___y_5860_; 
v_proof_5857_ = lean_ctor_get(v_a_5839_, 1);
v___x_5858_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2);
switch(lean_obj_tag(v_proof_5857_))
{
case 0:
{
lean_object* v_declName_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; 
v_declName_5875_ = lean_ctor_get(v_proof_5857_, 0);
v___x_5876_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_5875_);
v___x_5877_ = l_Lean_MessageData_ofName(v_declName_5875_);
v___x_5878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5878_, 0, v___x_5876_);
lean_ctor_set(v___x_5878_, 1, v___x_5877_);
v___y_5860_ = v___x_5878_;
goto v___jp_5859_;
}
case 1:
{
lean_object* v_fvarId_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; 
v_fvarId_5879_ = lean_ctor_get(v_proof_5857_, 0);
v___x_5880_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_5879_);
v___x_5881_ = l_Lean_mkFVar(v_fvarId_5879_);
v___x_5882_ = l_Lean_MessageData_ofExpr(v___x_5881_);
v___x_5883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5883_, 0, v___x_5880_);
lean_ctor_set(v___x_5883_, 1, v___x_5882_);
v___y_5860_ = v___x_5883_;
goto v___jp_5859_;
}
default: 
{
lean_object* v_ref_5884_; lean_object* v_proof_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; 
v_ref_5884_ = lean_ctor_get(v_proof_5857_, 1);
v_proof_5885_ = lean_ctor_get(v_proof_5857_, 2);
v___x_5886_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_5884_);
v___x_5887_ = l_Lean_MessageData_ofSyntax(v_ref_5884_);
v___x_5888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5888_, 0, v___x_5886_);
lean_ctor_set(v___x_5888_, 1, v___x_5887_);
v___x_5889_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_5890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5890_, 0, v___x_5888_);
lean_ctor_set(v___x_5890_, 1, v___x_5889_);
lean_inc_ref(v_proof_5885_);
v___x_5891_ = l_Lean_MessageData_ofExpr(v_proof_5885_);
v___x_5892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5890_);
lean_ctor_set(v___x_5892_, 1, v___x_5891_);
v___y_5860_ = v___x_5892_;
goto v___jp_5859_;
}
}
v___jp_5859_:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5861_, 0, v___x_5858_);
lean_ctor_set(v___x_5861_, 1, v___y_5860_);
v___x_5862_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_5863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5863_, 0, v___x_5861_);
lean_ctor_set(v___x_5863_, 1, v___x_5862_);
lean_inc_ref(v___x_5815_);
v___x_5864_ = l_Lean_MessageData_ofExpr(v___x_5815_);
v___x_5865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5863_);
lean_ctor_set(v___x_5865_, 1, v___x_5864_);
v___x_5866_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5854_, v___x_5865_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
if (lean_obj_tag(v___x_5866_) == 0)
{
lean_dec_ref_known(v___x_5866_, 1);
v_a_5833_ = v___x_5853_;
goto v___jp_5832_;
}
else
{
lean_object* v_a_5867_; lean_object* v___x_5869_; uint8_t v_isShared_5870_; uint8_t v_isSharedCheck_5874_; 
lean_dec_ref(v___x_5815_);
lean_dec_ref(v_info_5814_);
lean_dec(v_goal_5813_);
lean_dec_ref(v_scope_5812_);
v_a_5867_ = lean_ctor_get(v___x_5866_, 0);
v_isSharedCheck_5874_ = !lean_is_exclusive(v___x_5866_);
if (v_isSharedCheck_5874_ == 0)
{
v___x_5869_ = v___x_5866_;
v_isShared_5870_ = v_isSharedCheck_5874_;
goto v_resetjp_5868_;
}
else
{
lean_inc(v_a_5867_);
lean_dec(v___x_5866_);
v___x_5869_ = lean_box(0);
v_isShared_5870_ = v_isSharedCheck_5874_;
goto v_resetjp_5868_;
}
v_resetjp_5868_:
{
lean_object* v___x_5872_; 
if (v_isShared_5870_ == 0)
{
v___x_5872_ = v___x_5869_;
goto v_reusejp_5871_;
}
else
{
lean_object* v_reuseFailAlloc_5873_; 
v_reuseFailAlloc_5873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5867_);
v___x_5872_ = v_reuseFailAlloc_5873_;
goto v_reusejp_5871_;
}
v_reusejp_5871_:
{
return v___x_5872_;
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
lean_object* v_a_5894_; lean_object* v___x_5896_; uint8_t v_isShared_5897_; uint8_t v_isSharedCheck_5901_; 
lean_dec_ref(v___x_5815_);
lean_dec_ref(v_info_5814_);
lean_dec(v_goal_5813_);
lean_dec_ref(v_scope_5812_);
v_a_5894_ = lean_ctor_get(v___x_5840_, 0);
v_isSharedCheck_5901_ = !lean_is_exclusive(v___x_5840_);
if (v_isSharedCheck_5901_ == 0)
{
v___x_5896_ = v___x_5840_;
v_isShared_5897_ = v_isSharedCheck_5901_;
goto v_resetjp_5895_;
}
else
{
lean_inc(v_a_5894_);
lean_dec(v___x_5840_);
v___x_5896_ = lean_box(0);
v_isShared_5897_ = v_isSharedCheck_5901_;
goto v_resetjp_5895_;
}
v_resetjp_5895_:
{
lean_object* v___x_5899_; 
if (v_isShared_5897_ == 0)
{
v___x_5899_ = v___x_5896_;
goto v_reusejp_5898_;
}
else
{
lean_object* v_reuseFailAlloc_5900_; 
v_reuseFailAlloc_5900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5900_, 0, v_a_5894_);
v___x_5899_ = v_reuseFailAlloc_5900_;
goto v_reusejp_5898_;
}
v_reusejp_5898_:
{
return v___x_5899_;
}
}
}
}
v___jp_5832_:
{
size_t v___x_5834_; size_t v___x_5835_; 
v___x_5834_ = ((size_t)1ULL);
v___x_5835_ = lean_usize_add(v_i_5818_, v___x_5834_);
lean_inc_ref(v_a_5833_);
v_i_5818_ = v___x_5835_;
v_b_5819_ = v_a_5833_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___boxed(lean_object** _args){
lean_object* v_scope_5902_ = _args[0];
lean_object* v_goal_5903_ = _args[1];
lean_object* v_info_5904_ = _args[2];
lean_object* v___x_5905_ = _args[3];
lean_object* v_as_5906_ = _args[4];
lean_object* v_sz_5907_ = _args[5];
lean_object* v_i_5908_ = _args[6];
lean_object* v_b_5909_ = _args[7];
lean_object* v___y_5910_ = _args[8];
lean_object* v___y_5911_ = _args[9];
lean_object* v___y_5912_ = _args[10];
lean_object* v___y_5913_ = _args[11];
lean_object* v___y_5914_ = _args[12];
lean_object* v___y_5915_ = _args[13];
lean_object* v___y_5916_ = _args[14];
lean_object* v___y_5917_ = _args[15];
lean_object* v___y_5918_ = _args[16];
lean_object* v___y_5919_ = _args[17];
lean_object* v___y_5920_ = _args[18];
lean_object* v___y_5921_ = _args[19];
_start:
{
size_t v_sz_boxed_5922_; size_t v_i_boxed_5923_; lean_object* v_res_5924_; 
v_sz_boxed_5922_ = lean_unbox_usize(v_sz_5907_);
lean_dec(v_sz_5907_);
v_i_boxed_5923_ = lean_unbox_usize(v_i_5908_);
lean_dec(v_i_5908_);
v_res_5924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(v_scope_5902_, v_goal_5903_, v_info_5904_, v___x_5905_, v_as_5906_, v_sz_boxed_5922_, v_i_boxed_5923_, v_b_5909_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_, v___y_5920_);
lean_dec(v___y_5920_);
lean_dec_ref(v___y_5919_);
lean_dec(v___y_5918_);
lean_dec_ref(v___y_5917_);
lean_dec(v___y_5916_);
lean_dec_ref(v___y_5915_);
lean_dec(v___y_5914_);
lean_dec_ref(v___y_5913_);
lean_dec(v___y_5912_);
lean_dec(v___y_5911_);
lean_dec_ref(v___y_5910_);
lean_dec_ref(v_as_5906_);
return v_res_5924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0(lean_object* v_specs_5925_, lean_object* v___x_5926_, lean_object* v_scope_5927_, lean_object* v_goal_5928_, lean_object* v_info_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_){
_start:
{
lean_object* v___x_5942_; 
lean_inc_ref(v___x_5926_);
v___x_5942_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_findSpecs(v_specs_5925_, v___x_5926_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_);
if (lean_obj_tag(v___x_5942_) == 0)
{
lean_object* v_a_5943_; lean_object* v___x_5944_; size_t v_sz_5945_; size_t v___x_5946_; lean_object* v___x_5947_; 
v_a_5943_ = lean_ctor_get(v___x_5942_, 0);
lean_inc(v_a_5943_);
lean_dec_ref_known(v___x_5942_, 1);
v___x_5944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0));
v_sz_5945_ = lean_array_size(v_a_5943_);
v___x_5946_ = ((size_t)0ULL);
lean_inc_ref(v___x_5926_);
lean_inc_ref(v_info_5929_);
v___x_5947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(v_scope_5927_, v_goal_5928_, v_info_5929_, v___x_5926_, v_a_5943_, v_sz_5945_, v___x_5946_, v___x_5944_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_);
if (lean_obj_tag(v___x_5947_) == 0)
{
lean_object* v_a_5948_; lean_object* v___x_5950_; uint8_t v_isShared_5951_; uint8_t v_isSharedCheck_5959_; 
v_a_5948_ = lean_ctor_get(v___x_5947_, 0);
v_isSharedCheck_5959_ = !lean_is_exclusive(v___x_5947_);
if (v_isSharedCheck_5959_ == 0)
{
v___x_5950_ = v___x_5947_;
v_isShared_5951_ = v_isSharedCheck_5959_;
goto v_resetjp_5949_;
}
else
{
lean_inc(v_a_5948_);
lean_dec(v___x_5947_);
v___x_5950_ = lean_box(0);
v_isShared_5951_ = v_isSharedCheck_5959_;
goto v_resetjp_5949_;
}
v_resetjp_5949_:
{
lean_object* v_fst_5952_; 
v_fst_5952_ = lean_ctor_get(v_a_5948_, 0);
lean_inc(v_fst_5952_);
lean_dec(v_a_5948_);
if (lean_obj_tag(v_fst_5952_) == 0)
{
lean_object* v___x_5953_; lean_object* v___x_5954_; 
lean_del_object(v___x_5950_);
v___x_5953_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v_info_5929_);
lean_dec_ref(v_info_5929_);
v___x_5954_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_5926_, v___x_5953_, v_a_5943_, v___y_5930_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_);
return v___x_5954_;
}
else
{
lean_object* v_val_5955_; lean_object* v___x_5957_; 
lean_dec(v_a_5943_);
lean_dec_ref(v_info_5929_);
lean_dec_ref(v___x_5926_);
v_val_5955_ = lean_ctor_get(v_fst_5952_, 0);
lean_inc(v_val_5955_);
lean_dec_ref_known(v_fst_5952_, 1);
if (v_isShared_5951_ == 0)
{
lean_ctor_set(v___x_5950_, 0, v_val_5955_);
v___x_5957_ = v___x_5950_;
goto v_reusejp_5956_;
}
else
{
lean_object* v_reuseFailAlloc_5958_; 
v_reuseFailAlloc_5958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5958_, 0, v_val_5955_);
v___x_5957_ = v_reuseFailAlloc_5958_;
goto v_reusejp_5956_;
}
v_reusejp_5956_:
{
return v___x_5957_;
}
}
}
}
else
{
lean_object* v_a_5960_; lean_object* v___x_5962_; uint8_t v_isShared_5963_; uint8_t v_isSharedCheck_5967_; 
lean_dec(v_a_5943_);
lean_dec_ref(v_info_5929_);
lean_dec_ref(v___x_5926_);
v_a_5960_ = lean_ctor_get(v___x_5947_, 0);
v_isSharedCheck_5967_ = !lean_is_exclusive(v___x_5947_);
if (v_isSharedCheck_5967_ == 0)
{
v___x_5962_ = v___x_5947_;
v_isShared_5963_ = v_isSharedCheck_5967_;
goto v_resetjp_5961_;
}
else
{
lean_inc(v_a_5960_);
lean_dec(v___x_5947_);
v___x_5962_ = lean_box(0);
v_isShared_5963_ = v_isSharedCheck_5967_;
goto v_resetjp_5961_;
}
v_resetjp_5961_:
{
lean_object* v___x_5965_; 
if (v_isShared_5963_ == 0)
{
v___x_5965_ = v___x_5962_;
goto v_reusejp_5964_;
}
else
{
lean_object* v_reuseFailAlloc_5966_; 
v_reuseFailAlloc_5966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5966_, 0, v_a_5960_);
v___x_5965_ = v_reuseFailAlloc_5966_;
goto v_reusejp_5964_;
}
v_reusejp_5964_:
{
return v___x_5965_;
}
}
}
}
else
{
lean_object* v_a_5968_; lean_object* v___x_5970_; uint8_t v_isShared_5971_; uint8_t v_isSharedCheck_5975_; 
lean_dec_ref(v_info_5929_);
lean_dec(v_goal_5928_);
lean_dec_ref(v_scope_5927_);
lean_dec_ref(v___x_5926_);
v_a_5968_ = lean_ctor_get(v___x_5942_, 0);
v_isSharedCheck_5975_ = !lean_is_exclusive(v___x_5942_);
if (v_isSharedCheck_5975_ == 0)
{
v___x_5970_ = v___x_5942_;
v_isShared_5971_ = v_isSharedCheck_5975_;
goto v_resetjp_5969_;
}
else
{
lean_inc(v_a_5968_);
lean_dec(v___x_5942_);
v___x_5970_ = lean_box(0);
v_isShared_5971_ = v_isSharedCheck_5975_;
goto v_resetjp_5969_;
}
v_resetjp_5969_:
{
lean_object* v___x_5973_; 
if (v_isShared_5971_ == 0)
{
v___x_5973_ = v___x_5970_;
goto v_reusejp_5972_;
}
else
{
lean_object* v_reuseFailAlloc_5974_; 
v_reuseFailAlloc_5974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5974_, 0, v_a_5968_);
v___x_5973_ = v_reuseFailAlloc_5974_;
goto v_reusejp_5972_;
}
v_reusejp_5972_:
{
return v___x_5973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0___boxed(lean_object** _args){
lean_object* v_specs_5976_ = _args[0];
lean_object* v___x_5977_ = _args[1];
lean_object* v_scope_5978_ = _args[2];
lean_object* v_goal_5979_ = _args[3];
lean_object* v_info_5980_ = _args[4];
lean_object* v___y_5981_ = _args[5];
lean_object* v___y_5982_ = _args[6];
lean_object* v___y_5983_ = _args[7];
lean_object* v___y_5984_ = _args[8];
lean_object* v___y_5985_ = _args[9];
lean_object* v___y_5986_ = _args[10];
lean_object* v___y_5987_ = _args[11];
lean_object* v___y_5988_ = _args[12];
lean_object* v___y_5989_ = _args[13];
lean_object* v___y_5990_ = _args[14];
lean_object* v___y_5991_ = _args[15];
lean_object* v___y_5992_ = _args[16];
_start:
{
lean_object* v_res_5993_; 
v_res_5993_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0(v_specs_5976_, v___x_5977_, v_scope_5978_, v_goal_5979_, v_info_5980_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_);
lean_dec(v___y_5991_);
lean_dec_ref(v___y_5990_);
lean_dec(v___y_5989_);
lean_dec_ref(v___y_5988_);
lean_dec(v___y_5987_);
lean_dec_ref(v___y_5986_);
lean_dec(v___y_5985_);
lean_dec_ref(v___y_5984_);
lean_dec(v___y_5983_);
lean_dec(v___y_5982_);
lean_dec_ref(v___y_5981_);
lean_dec_ref(v_specs_5976_);
return v_res_5993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(lean_object* v_scope_5994_, lean_object* v_goal_5995_, lean_object* v_info_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_, lean_object* v_a_6001_, lean_object* v_a_6002_, lean_object* v_a_6003_, lean_object* v_a_6004_, lean_object* v_a_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_){
_start:
{
lean_object* v_specs_6009_; lean_object* v___x_6010_; lean_object* v___f_6011_; lean_object* v___x_6012_; 
v_specs_6009_ = lean_ctor_get(v_scope_5994_, 0);
lean_inc_ref(v_specs_6009_);
v___x_6010_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5996_);
lean_inc(v_goal_5995_);
v___f_6011_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0___boxed), 17, 5);
lean_closure_set(v___f_6011_, 0, v_specs_6009_);
lean_closure_set(v___f_6011_, 1, v___x_6010_);
lean_closure_set(v___f_6011_, 2, v_scope_5994_);
lean_closure_set(v___f_6011_, 3, v_goal_5995_);
lean_closure_set(v___f_6011_, 4, v_info_5996_);
v___x_6012_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_5995_, v___f_6011_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_, v_a_6001_, v_a_6002_, v_a_6003_, v_a_6004_, v_a_6005_, v_a_6006_, v_a_6007_);
return v___x_6012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___boxed(lean_object* v_scope_6013_, lean_object* v_goal_6014_, lean_object* v_info_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_, lean_object* v_a_6025_, lean_object* v_a_6026_, lean_object* v_a_6027_){
_start:
{
lean_object* v_res_6028_; 
v_res_6028_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(v_scope_6013_, v_goal_6014_, v_info_6015_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_, v_a_6024_, v_a_6025_, v_a_6026_);
lean_dec(v_a_6026_);
lean_dec_ref(v_a_6025_);
lean_dec(v_a_6024_);
lean_dec_ref(v_a_6023_);
lean_dec(v_a_6022_);
lean_dec_ref(v_a_6021_);
lean_dec(v_a_6020_);
lean_dec_ref(v_a_6019_);
lean_dec(v_a_6018_);
lean_dec(v_a_6017_);
lean_dec_ref(v_a_6016_);
return v_res_6028_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6030_; lean_object* v___x_6031_; 
v___x_6030_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__0));
v___x_6031_ = l_Lean_stringToMessageData(v___x_6030_);
return v___x_6031_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3(void){
_start:
{
lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6033_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2));
v___x_6034_ = l_Lean_stringToMessageData(v___x_6033_);
return v___x_6034_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5(void){
_start:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; 
v___x_6036_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4));
v___x_6037_ = l_Lean_stringToMessageData(v___x_6036_);
return v___x_6037_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7(void){
_start:
{
lean_object* v___x_6039_; lean_object* v___x_6040_; 
v___x_6039_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__6));
v___x_6040_ = l_Lean_stringToMessageData(v___x_6039_);
return v___x_6040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0(lean_object* v_goal_6043_, lean_object* v_scope_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_){
_start:
{
lean_object* v_gs_6058_; lean_object* v_g_6062_; lean_object* v___y_6068_; lean_object* v___y_6069_; lean_object* v___y_6074_; lean_object* v_g_6075_; lean_object* v___y_6081_; lean_object* v_gs_6082_; lean_object* v___y_6086_; lean_object* v_g_6087_; lean_object* v___y_6088_; lean_object* v___y_6110_; lean_object* v___y_6111_; lean_object* v___y_6112_; lean_object* v___y_6113_; lean_object* v___y_6114_; lean_object* v___y_6115_; lean_object* v___y_6116_; lean_object* v___y_6117_; lean_object* v___y_6118_; lean_object* v___y_6119_; lean_object* v___y_6120_; lean_object* v___y_6121_; lean_object* v___y_6122_; lean_object* v___y_6134_; lean_object* v___y_6135_; lean_object* v___y_6136_; lean_object* v___y_6137_; lean_object* v___y_6138_; lean_object* v___y_6139_; lean_object* v___y_6140_; lean_object* v___y_6141_; lean_object* v___y_6142_; lean_object* v___y_6143_; lean_object* v___y_6144_; lean_object* v___y_6145_; lean_object* v___y_6146_; lean_object* v___y_6147_; lean_object* v___y_6148_; lean_object* v___x_6272_; 
v___x_6272_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v___y_6046_);
if (lean_obj_tag(v___x_6272_) == 0)
{
lean_object* v_a_6273_; lean_object* v___x_6275_; uint8_t v_isShared_6276_; uint8_t v_isSharedCheck_6537_; 
v_a_6273_ = lean_ctor_get(v___x_6272_, 0);
v_isSharedCheck_6537_ = !lean_is_exclusive(v___x_6272_);
if (v_isSharedCheck_6537_ == 0)
{
v___x_6275_ = v___x_6272_;
v_isShared_6276_ = v_isSharedCheck_6537_;
goto v_resetjp_6274_;
}
else
{
lean_inc(v_a_6273_);
lean_dec(v___x_6272_);
v___x_6275_ = lean_box(0);
v_isShared_6276_ = v_isSharedCheck_6537_;
goto v_resetjp_6274_;
}
v_resetjp_6274_:
{
uint8_t v___x_6277_; 
v___x_6277_ = lean_unbox(v_a_6273_);
lean_dec(v_a_6273_);
if (v___x_6277_ == 0)
{
lean_object* v___x_6278_; 
lean_del_object(v___x_6275_);
lean_inc(v_goal_6043_);
v___x_6278_ = l_Lean_MVarId_getType(v_goal_6043_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_);
if (lean_obj_tag(v___x_6278_) == 0)
{
lean_object* v_a_6279_; lean_object* v___x_6281_; uint8_t v_isShared_6282_; uint8_t v_isSharedCheck_6524_; 
v_a_6279_ = lean_ctor_get(v___x_6278_, 0);
v_isSharedCheck_6524_ = !lean_is_exclusive(v___x_6278_);
if (v_isSharedCheck_6524_ == 0)
{
v___x_6281_ = v___x_6278_;
v_isShared_6282_ = v_isSharedCheck_6524_;
goto v_resetjp_6280_;
}
else
{
lean_inc(v_a_6279_);
lean_dec(v___x_6278_);
v___x_6281_ = lean_box(0);
v_isShared_6282_ = v_isSharedCheck_6524_;
goto v_resetjp_6280_;
}
v_resetjp_6280_:
{
lean_object* v_options_6289_; lean_object* v_inheritedTraceOptions_6290_; uint8_t v_hasTrace_6291_; lean_object* v___x_6292_; lean_object* v___y_6294_; lean_object* v___y_6295_; lean_object* v___y_6296_; lean_object* v___y_6297_; lean_object* v___y_6298_; lean_object* v___y_6299_; lean_object* v___y_6300_; lean_object* v___y_6301_; lean_object* v___y_6302_; lean_object* v___y_6303_; lean_object* v___y_6304_; 
v_options_6289_ = lean_ctor_get(v___y_6054_, 2);
v_inheritedTraceOptions_6290_ = lean_ctor_get(v___y_6054_, 13);
v_hasTrace_6291_ = lean_ctor_get_uint8(v_options_6289_, sizeof(void*)*1);
v___x_6292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_6291_ == 0)
{
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
v___y_6304_ = v___y_6055_;
goto v___jp_6293_;
}
else
{
lean_object* v___x_6510_; uint8_t v___x_6511_; 
v___x_6510_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_6511_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6290_, v_options_6289_, v___x_6510_);
if (v___x_6511_ == 0)
{
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
v___y_6304_ = v___y_6055_;
goto v___jp_6293_;
}
else
{
lean_object* v___x_6512_; lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; 
v___x_6512_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__7);
lean_inc(v_a_6279_);
v___x_6513_ = l_Lean_MessageData_ofExpr(v_a_6279_);
v___x_6514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6514_, 0, v___x_6512_);
lean_ctor_set(v___x_6514_, 1, v___x_6513_);
v___x_6515_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_6292_, v___x_6514_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_);
if (lean_obj_tag(v___x_6515_) == 0)
{
lean_dec_ref_known(v___x_6515_, 1);
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
v___y_6304_ = v___y_6055_;
goto v___jp_6293_;
}
else
{
lean_object* v_a_6516_; lean_object* v___x_6518_; uint8_t v_isShared_6519_; uint8_t v_isSharedCheck_6523_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6516_ = lean_ctor_get(v___x_6515_, 0);
v_isSharedCheck_6523_ = !lean_is_exclusive(v___x_6515_);
if (v_isSharedCheck_6523_ == 0)
{
v___x_6518_ = v___x_6515_;
v_isShared_6519_ = v_isSharedCheck_6523_;
goto v_resetjp_6517_;
}
else
{
lean_inc(v_a_6516_);
lean_dec(v___x_6515_);
v___x_6518_ = lean_box(0);
v_isShared_6519_ = v_isSharedCheck_6523_;
goto v_resetjp_6517_;
}
v_resetjp_6517_:
{
lean_object* v___x_6521_; 
if (v_isShared_6519_ == 0)
{
v___x_6521_ = v___x_6518_;
goto v_reusejp_6520_;
}
else
{
lean_object* v_reuseFailAlloc_6522_; 
v_reuseFailAlloc_6522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6522_, 0, v_a_6516_);
v___x_6521_ = v_reuseFailAlloc_6522_;
goto v_reusejp_6520_;
}
v_reusejp_6520_:
{
return v___x_6521_;
}
}
}
}
}
v___jp_6283_:
{
lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6287_; 
v___x_6284_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6284_, 0, v_a_6279_);
v___x_6285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6285_, 0, v___x_6284_);
if (v_isShared_6282_ == 0)
{
lean_ctor_set(v___x_6281_, 0, v___x_6285_);
v___x_6287_ = v___x_6281_;
goto v_reusejp_6286_;
}
else
{
lean_object* v_reuseFailAlloc_6288_; 
v_reuseFailAlloc_6288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6288_, 0, v___x_6285_);
v___x_6287_ = v_reuseFailAlloc_6288_;
goto v_reusejp_6286_;
}
v_reusejp_6286_:
{
return v___x_6287_;
}
}
v___jp_6293_:
{
lean_object* v___x_6305_; 
lean_inc(v_goal_6043_);
v___x_6305_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg(v_goal_6043_, v_a_6279_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6305_) == 0)
{
lean_object* v_a_6306_; 
v_a_6306_ = lean_ctor_get(v___x_6305_, 0);
lean_inc(v_a_6306_);
lean_dec_ref_known(v___x_6305_, 1);
if (lean_obj_tag(v_a_6306_) == 1)
{
lean_object* v_val_6307_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec(v_goal_6043_);
v_val_6307_ = lean_ctor_get(v_a_6306_, 0);
lean_inc(v_val_6307_);
lean_dec_ref_known(v_a_6306_, 1);
v_g_6062_ = v_val_6307_;
goto v___jp_6061_;
}
else
{
lean_object* v___x_6308_; 
lean_dec(v_a_6306_);
lean_inc(v_goal_6043_);
v___x_6308_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f(v_goal_6043_, v_a_6279_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6308_) == 0)
{
lean_object* v_a_6309_; 
v_a_6309_ = lean_ctor_get(v___x_6308_, 0);
lean_inc(v_a_6309_);
lean_dec_ref_known(v___x_6308_, 1);
if (lean_obj_tag(v_a_6309_) == 1)
{
lean_object* v_val_6310_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec(v_goal_6043_);
v_val_6310_ = lean_ctor_get(v_a_6309_, 0);
lean_inc(v_val_6310_);
lean_dec_ref_known(v_a_6309_, 1);
v_gs_6058_ = v_val_6310_;
goto v___jp_6057_;
}
else
{
lean_object* v___x_6311_; 
lean_dec(v_a_6309_);
lean_inc(v_a_6279_);
lean_inc(v_goal_6043_);
v___x_6311_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f(v_goal_6043_, v_a_6279_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6311_) == 0)
{
lean_object* v_a_6312_; 
v_a_6312_ = lean_ctor_get(v___x_6311_, 0);
lean_inc(v_a_6312_);
lean_dec_ref_known(v___x_6311_, 1);
if (lean_obj_tag(v_a_6312_) == 1)
{
lean_object* v_val_6313_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec(v_goal_6043_);
v_val_6313_ = lean_ctor_get(v_a_6312_, 0);
lean_inc(v_val_6313_);
lean_dec_ref_known(v_a_6312_, 1);
v_g_6062_ = v_val_6313_;
goto v___jp_6061_;
}
else
{
lean_object* v___x_6314_; 
lean_dec(v_a_6312_);
lean_inc(v_goal_6043_);
v___x_6314_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f(v_goal_6043_, v_a_6279_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6314_) == 0)
{
lean_object* v_a_6315_; 
v_a_6315_ = lean_ctor_get(v___x_6314_, 0);
lean_inc(v_a_6315_);
lean_dec_ref_known(v___x_6314_, 1);
if (lean_obj_tag(v_a_6315_) == 1)
{
lean_object* v_val_6316_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec(v_goal_6043_);
v_val_6316_ = lean_ctor_get(v_a_6315_, 0);
lean_inc(v_val_6316_);
lean_dec_ref_known(v_a_6315_, 1);
v_g_6062_ = v_val_6316_;
goto v___jp_6061_;
}
else
{
lean_object* v___x_6317_; 
lean_dec(v_a_6315_);
lean_inc(v_a_6279_);
lean_inc(v_goal_6043_);
v___x_6317_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f(v_goal_6043_, v_a_6279_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6317_) == 0)
{
lean_object* v_a_6318_; 
v_a_6318_ = lean_ctor_get(v___x_6317_, 0);
lean_inc(v_a_6318_);
lean_dec_ref_known(v___x_6317_, 1);
if (lean_obj_tag(v_a_6318_) == 1)
{
lean_object* v_val_6319_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec(v_goal_6043_);
v_val_6319_ = lean_ctor_get(v_a_6318_, 0);
lean_inc(v_val_6319_);
lean_dec_ref_known(v_a_6318_, 1);
v_g_6062_ = v_val_6319_;
goto v___jp_6061_;
}
else
{
lean_object* v___x_6320_; 
lean_dec(v_a_6318_);
lean_inc(v_a_6279_);
lean_inc(v_goal_6043_);
lean_inc_ref(v_scope_6044_);
v___x_6320_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f(v_scope_6044_, v_goal_6043_, v_a_6279_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6320_) == 0)
{
lean_object* v_a_6321_; 
v_a_6321_ = lean_ctor_get(v___x_6320_, 0);
lean_inc(v_a_6321_);
lean_dec_ref_known(v___x_6320_, 1);
if (lean_obj_tag(v_a_6321_) == 1)
{
lean_object* v_val_6322_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec(v_goal_6043_);
v_val_6322_ = lean_ctor_get(v_a_6321_, 0);
lean_inc(v_val_6322_);
lean_dec_ref_known(v_a_6321_, 1);
v_gs_6058_ = v_val_6322_;
goto v___jp_6057_;
}
else
{
lean_object* v___x_6323_; 
lean_dec(v_a_6321_);
lean_inc(v_a_6279_);
lean_inc(v_goal_6043_);
v___x_6323_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(v_goal_6043_, v_a_6279_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6323_) == 0)
{
lean_object* v_a_6324_; 
v_a_6324_ = lean_ctor_get(v___x_6323_, 0);
lean_inc(v_a_6324_);
lean_dec_ref_known(v___x_6323_, 1);
if (lean_obj_tag(v_a_6324_) == 1)
{
lean_object* v_val_6325_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec(v_goal_6043_);
v_val_6325_ = lean_ctor_get(v_a_6324_, 0);
lean_inc(v_val_6325_);
lean_dec_ref_known(v_a_6324_, 1);
v_g_6062_ = v_val_6325_;
goto v___jp_6061_;
}
else
{
lean_object* v___x_6326_; uint8_t v___x_6327_; 
lean_dec(v_a_6324_);
lean_inc(v_a_6279_);
v___x_6326_ = l_Lean_Expr_cleanupAnnotations(v_a_6279_);
v___x_6327_ = l_Lean_Expr_isApp(v___x_6326_);
if (v___x_6327_ == 0)
{
lean_dec_ref(v___x_6326_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
goto v___jp_6283_;
}
else
{
lean_object* v_arg_6328_; lean_object* v___x_6329_; uint8_t v___x_6330_; 
v_arg_6328_ = lean_ctor_get(v___x_6326_, 1);
lean_inc_ref(v_arg_6328_);
v___x_6329_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6326_);
v___x_6330_ = l_Lean_Expr_isApp(v___x_6329_);
if (v___x_6330_ == 0)
{
lean_dec_ref(v___x_6329_);
lean_dec_ref(v_arg_6328_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
goto v___jp_6283_;
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
lean_dec_ref(v_arg_6328_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
goto v___jp_6283_;
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
lean_dec_ref(v_arg_6328_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
goto v___jp_6283_;
}
else
{
lean_object* v_arg_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; uint8_t v___x_6340_; 
v_arg_6337_ = lean_ctor_get(v___x_6335_, 1);
lean_inc_ref(v_arg_6337_);
v___x_6338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6335_);
v___x_6339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___closed__10));
v___x_6340_ = l_Lean_Expr_isConstOf(v___x_6338_, v___x_6339_);
lean_dec_ref(v___x_6338_);
if (v___x_6340_ == 0)
{
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
goto v___jp_6283_;
}
else
{
lean_object* v___x_6341_; 
lean_del_object(v___x_6281_);
lean_inc(v_goal_6043_);
v___x_6341_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(v_goal_6043_, v___y_6294_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6341_) == 0)
{
lean_object* v_a_6342_; 
v_a_6342_ = lean_ctor_get(v___x_6341_, 0);
lean_inc(v_a_6342_);
lean_dec_ref_known(v___x_6341_, 1);
if (lean_obj_tag(v_a_6342_) == 1)
{
lean_object* v_val_6343_; 
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_a_6279_);
lean_dec(v_goal_6043_);
v_val_6343_ = lean_ctor_get(v_a_6342_, 0);
lean_inc(v_val_6343_);
lean_dec_ref_known(v_a_6342_, 1);
v_gs_6058_ = v_val_6343_;
goto v___jp_6057_;
}
else
{
lean_object* v___x_6344_; 
lean_dec(v_a_6342_);
lean_inc(v_a_6279_);
lean_inc_ref(v_arg_6331_);
lean_inc(v_goal_6043_);
lean_inc_ref(v_scope_6044_);
v___x_6344_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(v_scope_6044_, v_goal_6043_, v_arg_6337_, v_arg_6331_, v_a_6279_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6344_) == 0)
{
lean_object* v_a_6345_; lean_object* v___x_6347_; uint8_t v_isShared_6348_; uint8_t v_isSharedCheck_6437_; 
v_a_6345_ = lean_ctor_get(v___x_6344_, 0);
v_isSharedCheck_6437_ = !lean_is_exclusive(v___x_6344_);
if (v_isSharedCheck_6437_ == 0)
{
v___x_6347_ = v___x_6344_;
v_isShared_6348_ = v_isSharedCheck_6437_;
goto v_resetjp_6346_;
}
else
{
lean_inc(v_a_6345_);
lean_dec(v___x_6344_);
v___x_6347_ = lean_box(0);
v_isShared_6348_ = v_isSharedCheck_6437_;
goto v_resetjp_6346_;
}
v_resetjp_6346_:
{
if (lean_obj_tag(v_a_6345_) == 1)
{
lean_object* v_val_6349_; lean_object* v_fst_6350_; lean_object* v_snd_6351_; lean_object* v___x_6353_; uint8_t v_isShared_6354_; uint8_t v_isSharedCheck_6361_; 
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_a_6279_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_val_6349_ = lean_ctor_get(v_a_6345_, 0);
lean_inc(v_val_6349_);
lean_dec_ref_known(v_a_6345_, 1);
v_fst_6350_ = lean_ctor_get(v_val_6349_, 0);
v_snd_6351_ = lean_ctor_get(v_val_6349_, 1);
v_isSharedCheck_6361_ = !lean_is_exclusive(v_val_6349_);
if (v_isSharedCheck_6361_ == 0)
{
v___x_6353_ = v_val_6349_;
v_isShared_6354_ = v_isSharedCheck_6361_;
goto v_resetjp_6352_;
}
else
{
lean_inc(v_snd_6351_);
lean_inc(v_fst_6350_);
lean_dec(v_val_6349_);
v___x_6353_ = lean_box(0);
v_isShared_6354_ = v_isSharedCheck_6361_;
goto v_resetjp_6352_;
}
v_resetjp_6352_:
{
lean_object* v___x_6356_; 
if (v_isShared_6354_ == 0)
{
v___x_6356_ = v___x_6353_;
goto v_reusejp_6355_;
}
else
{
lean_object* v_reuseFailAlloc_6360_; 
v_reuseFailAlloc_6360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6360_, 0, v_fst_6350_);
lean_ctor_set(v_reuseFailAlloc_6360_, 1, v_snd_6351_);
v___x_6356_ = v_reuseFailAlloc_6360_;
goto v_reusejp_6355_;
}
v_reusejp_6355_:
{
lean_object* v___x_6358_; 
if (v_isShared_6348_ == 0)
{
lean_ctor_set(v___x_6347_, 0, v___x_6356_);
v___x_6358_ = v___x_6347_;
goto v_reusejp_6357_;
}
else
{
lean_object* v_reuseFailAlloc_6359_; 
v_reuseFailAlloc_6359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6359_, 0, v___x_6356_);
v___x_6358_ = v_reuseFailAlloc_6359_;
goto v_reusejp_6357_;
}
v_reusejp_6357_:
{
return v___x_6358_;
}
}
}
}
else
{
lean_object* v___x_6362_; 
lean_del_object(v___x_6347_);
lean_dec(v_a_6345_);
lean_inc(v_goal_6043_);
v___x_6362_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(v_scope_6044_, v_goal_6043_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6362_) == 0)
{
lean_object* v_a_6363_; lean_object* v___x_6364_; 
v_a_6363_ = lean_ctor_get(v___x_6362_, 0);
lean_inc(v_a_6363_);
lean_dec_ref_known(v___x_6362_, 1);
lean_inc_ref(v_arg_6328_);
lean_inc_ref(v_arg_6331_);
lean_inc_ref(v_arg_6337_);
lean_inc(v_goal_6043_);
v___x_6364_ = l_Lean_Elab_Tactic_VCGen_reduceEPostHead_x3f(v_goal_6043_, v_a_6279_, v_arg_6337_, v_arg_6334_, v_arg_6331_, v_arg_6328_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6364_) == 0)
{
lean_object* v_a_6365_; 
v_a_6365_ = lean_ctor_get(v___x_6364_, 0);
lean_inc(v_a_6365_);
lean_dec_ref_known(v___x_6364_, 1);
if (lean_obj_tag(v_a_6365_) == 1)
{
lean_object* v_val_6366_; 
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_goal_6043_);
v_val_6366_ = lean_ctor_get(v_a_6365_, 0);
lean_inc(v_val_6366_);
lean_dec_ref_known(v_a_6365_, 1);
v___y_6074_ = v_a_6363_;
v_g_6075_ = v_val_6366_;
goto v___jp_6073_;
}
else
{
lean_object* v___x_6367_; 
lean_dec(v_a_6365_);
lean_inc_ref(v_arg_6328_);
lean_inc(v_goal_6043_);
v___x_6367_ = l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(v_goal_6043_, v_arg_6328_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6367_) == 0)
{
lean_object* v_a_6368_; 
v_a_6368_ = lean_ctor_get(v___x_6367_, 0);
lean_inc(v_a_6368_);
lean_dec_ref_known(v___x_6367_, 1);
if (lean_obj_tag(v_a_6368_) == 1)
{
lean_object* v_val_6369_; 
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_goal_6043_);
v_val_6369_ = lean_ctor_get(v_a_6368_, 0);
lean_inc(v_val_6369_);
lean_dec_ref_known(v_a_6368_, 1);
v___y_6081_ = v_a_6363_;
v_gs_6082_ = v_val_6369_;
goto v___jp_6080_;
}
else
{
lean_object* v___x_6370_; 
lean_dec(v_a_6368_);
lean_inc(v_goal_6043_);
v___x_6370_ = l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(v_goal_6043_, v_arg_6328_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6370_) == 0)
{
lean_object* v_a_6371_; 
v_a_6371_ = lean_ctor_get(v___x_6370_, 0);
lean_inc(v_a_6371_);
lean_dec_ref_known(v___x_6370_, 1);
if (lean_obj_tag(v_a_6371_) == 1)
{
lean_object* v_val_6372_; 
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_goal_6043_);
v_val_6372_ = lean_ctor_get(v_a_6371_, 0);
lean_inc(v_val_6372_);
lean_dec_ref_known(v_a_6371_, 1);
v___y_6081_ = v_a_6363_;
v_gs_6082_ = v_val_6372_;
goto v___jp_6080_;
}
else
{
lean_object* v___x_6373_; 
lean_dec(v_a_6371_);
lean_inc_ref(v_arg_6328_);
lean_inc_ref(v_arg_6331_);
lean_inc(v_goal_6043_);
lean_inc(v_a_6363_);
v___x_6373_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f(v_a_6363_, v_goal_6043_, v_arg_6337_, v_arg_6331_, v_arg_6328_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
lean_dec_ref(v_arg_6337_);
if (lean_obj_tag(v___x_6373_) == 0)
{
lean_object* v_a_6374_; 
v_a_6374_ = lean_ctor_get(v___x_6373_, 0);
lean_inc(v_a_6374_);
lean_dec_ref_known(v___x_6373_, 1);
if (lean_obj_tag(v_a_6374_) == 1)
{
lean_object* v_val_6375_; 
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_goal_6043_);
v_val_6375_ = lean_ctor_get(v_a_6374_, 0);
lean_inc(v_val_6375_);
lean_dec_ref_known(v_a_6374_, 1);
v___y_6081_ = v_a_6363_;
v_gs_6082_ = v_val_6375_;
goto v___jp_6080_;
}
else
{
lean_object* v___x_6376_; 
lean_dec(v_a_6374_);
lean_inc_ref(v_arg_6328_);
v___x_6376_ = l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(v_arg_6328_);
if (lean_obj_tag(v___x_6376_) == 1)
{
lean_object* v_options_6377_; uint8_t v_hasTrace_6378_; 
v_options_6377_ = lean_ctor_get(v___y_6303_, 2);
v_hasTrace_6378_ = lean_ctor_get_uint8(v_options_6377_, sizeof(void*)*1);
if (v_hasTrace_6378_ == 0)
{
lean_object* v_val_6379_; 
v_val_6379_ = lean_ctor_get(v___x_6376_, 0);
lean_inc(v_val_6379_);
lean_dec_ref_known(v___x_6376_, 1);
v___y_6134_ = v_arg_6331_;
v___y_6135_ = v_val_6379_;
v___y_6136_ = v_a_6363_;
v___y_6137_ = v_arg_6328_;
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
v___y_6148_ = v___y_6304_;
goto v___jp_6133_;
}
else
{
lean_object* v_val_6380_; lean_object* v_inheritedTraceOptions_6381_; lean_object* v___x_6382_; uint8_t v___x_6383_; 
v_val_6380_ = lean_ctor_get(v___x_6376_, 0);
lean_inc(v_val_6380_);
lean_dec_ref_known(v___x_6376_, 1);
v_inheritedTraceOptions_6381_ = lean_ctor_get(v___y_6303_, 13);
v___x_6382_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_6383_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6381_, v_options_6377_, v___x_6382_);
if (v___x_6383_ == 0)
{
v___y_6134_ = v_arg_6331_;
v___y_6135_ = v_val_6380_;
v___y_6136_ = v_a_6363_;
v___y_6137_ = v_arg_6328_;
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
v___y_6148_ = v___y_6304_;
goto v___jp_6133_;
}
else
{
lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; 
v___x_6384_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5);
v___x_6385_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_val_6380_);
v___x_6386_ = l_Lean_MessageData_ofExpr(v___x_6385_);
v___x_6387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6387_, 0, v___x_6384_);
lean_ctor_set(v___x_6387_, 1, v___x_6386_);
v___x_6388_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_6292_, v___x_6387_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
if (lean_obj_tag(v___x_6388_) == 0)
{
lean_dec_ref_known(v___x_6388_, 1);
v___y_6134_ = v_arg_6331_;
v___y_6135_ = v_val_6380_;
v___y_6136_ = v_a_6363_;
v___y_6137_ = v_arg_6328_;
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
v___y_6148_ = v___y_6304_;
goto v___jp_6133_;
}
else
{
lean_object* v_a_6389_; lean_object* v___x_6391_; uint8_t v_isShared_6392_; uint8_t v_isSharedCheck_6396_; 
lean_dec(v_val_6380_);
lean_dec(v_a_6363_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_goal_6043_);
v_a_6389_ = lean_ctor_get(v___x_6388_, 0);
v_isSharedCheck_6396_ = !lean_is_exclusive(v___x_6388_);
if (v_isSharedCheck_6396_ == 0)
{
v___x_6391_ = v___x_6388_;
v_isShared_6392_ = v_isSharedCheck_6396_;
goto v_resetjp_6390_;
}
else
{
lean_inc(v_a_6389_);
lean_dec(v___x_6388_);
v___x_6391_ = lean_box(0);
v_isShared_6392_ = v_isSharedCheck_6396_;
goto v_resetjp_6390_;
}
v_resetjp_6390_:
{
lean_object* v___x_6394_; 
if (v_isShared_6392_ == 0)
{
v___x_6394_ = v___x_6391_;
goto v_reusejp_6393_;
}
else
{
lean_object* v_reuseFailAlloc_6395_; 
v_reuseFailAlloc_6395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6395_, 0, v_a_6389_);
v___x_6394_ = v_reuseFailAlloc_6395_;
goto v_reusejp_6393_;
}
v_reusejp_6393_:
{
return v___x_6394_;
}
}
}
}
}
}
else
{
lean_dec(v___x_6376_);
lean_dec(v_a_6363_);
lean_dec(v_goal_6043_);
v___y_6068_ = v_arg_6331_;
v___y_6069_ = v_arg_6328_;
goto v___jp_6067_;
}
}
}
else
{
lean_object* v_a_6397_; lean_object* v___x_6399_; uint8_t v_isShared_6400_; uint8_t v_isSharedCheck_6404_; 
lean_dec(v_a_6363_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_goal_6043_);
v_a_6397_ = lean_ctor_get(v___x_6373_, 0);
v_isSharedCheck_6404_ = !lean_is_exclusive(v___x_6373_);
if (v_isSharedCheck_6404_ == 0)
{
v___x_6399_ = v___x_6373_;
v_isShared_6400_ = v_isSharedCheck_6404_;
goto v_resetjp_6398_;
}
else
{
lean_inc(v_a_6397_);
lean_dec(v___x_6373_);
v___x_6399_ = lean_box(0);
v_isShared_6400_ = v_isSharedCheck_6404_;
goto v_resetjp_6398_;
}
v_resetjp_6398_:
{
lean_object* v___x_6402_; 
if (v_isShared_6400_ == 0)
{
v___x_6402_ = v___x_6399_;
goto v_reusejp_6401_;
}
else
{
lean_object* v_reuseFailAlloc_6403_; 
v_reuseFailAlloc_6403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6403_, 0, v_a_6397_);
v___x_6402_ = v_reuseFailAlloc_6403_;
goto v_reusejp_6401_;
}
v_reusejp_6401_:
{
return v___x_6402_;
}
}
}
}
}
else
{
lean_object* v_a_6405_; lean_object* v___x_6407_; uint8_t v_isShared_6408_; uint8_t v_isSharedCheck_6412_; 
lean_dec(v_a_6363_);
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_goal_6043_);
v_a_6405_ = lean_ctor_get(v___x_6370_, 0);
v_isSharedCheck_6412_ = !lean_is_exclusive(v___x_6370_);
if (v_isSharedCheck_6412_ == 0)
{
v___x_6407_ = v___x_6370_;
v_isShared_6408_ = v_isSharedCheck_6412_;
goto v_resetjp_6406_;
}
else
{
lean_inc(v_a_6405_);
lean_dec(v___x_6370_);
v___x_6407_ = lean_box(0);
v_isShared_6408_ = v_isSharedCheck_6412_;
goto v_resetjp_6406_;
}
v_resetjp_6406_:
{
lean_object* v___x_6410_; 
if (v_isShared_6408_ == 0)
{
v___x_6410_ = v___x_6407_;
goto v_reusejp_6409_;
}
else
{
lean_object* v_reuseFailAlloc_6411_; 
v_reuseFailAlloc_6411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6411_, 0, v_a_6405_);
v___x_6410_ = v_reuseFailAlloc_6411_;
goto v_reusejp_6409_;
}
v_reusejp_6409_:
{
return v___x_6410_;
}
}
}
}
}
else
{
lean_object* v_a_6413_; lean_object* v___x_6415_; uint8_t v_isShared_6416_; uint8_t v_isSharedCheck_6420_; 
lean_dec(v_a_6363_);
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_goal_6043_);
v_a_6413_ = lean_ctor_get(v___x_6367_, 0);
v_isSharedCheck_6420_ = !lean_is_exclusive(v___x_6367_);
if (v_isSharedCheck_6420_ == 0)
{
v___x_6415_ = v___x_6367_;
v_isShared_6416_ = v_isSharedCheck_6420_;
goto v_resetjp_6414_;
}
else
{
lean_inc(v_a_6413_);
lean_dec(v___x_6367_);
v___x_6415_ = lean_box(0);
v_isShared_6416_ = v_isSharedCheck_6420_;
goto v_resetjp_6414_;
}
v_resetjp_6414_:
{
lean_object* v___x_6418_; 
if (v_isShared_6416_ == 0)
{
v___x_6418_ = v___x_6415_;
goto v_reusejp_6417_;
}
else
{
lean_object* v_reuseFailAlloc_6419_; 
v_reuseFailAlloc_6419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6419_, 0, v_a_6413_);
v___x_6418_ = v_reuseFailAlloc_6419_;
goto v_reusejp_6417_;
}
v_reusejp_6417_:
{
return v___x_6418_;
}
}
}
}
}
else
{
lean_object* v_a_6421_; lean_object* v___x_6423_; uint8_t v_isShared_6424_; uint8_t v_isSharedCheck_6428_; 
lean_dec(v_a_6363_);
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_goal_6043_);
v_a_6421_ = lean_ctor_get(v___x_6364_, 0);
v_isSharedCheck_6428_ = !lean_is_exclusive(v___x_6364_);
if (v_isSharedCheck_6428_ == 0)
{
v___x_6423_ = v___x_6364_;
v_isShared_6424_ = v_isSharedCheck_6428_;
goto v_resetjp_6422_;
}
else
{
lean_inc(v_a_6421_);
lean_dec(v___x_6364_);
v___x_6423_ = lean_box(0);
v_isShared_6424_ = v_isSharedCheck_6428_;
goto v_resetjp_6422_;
}
v_resetjp_6422_:
{
lean_object* v___x_6426_; 
if (v_isShared_6424_ == 0)
{
v___x_6426_ = v___x_6423_;
goto v_reusejp_6425_;
}
else
{
lean_object* v_reuseFailAlloc_6427_; 
v_reuseFailAlloc_6427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6427_, 0, v_a_6421_);
v___x_6426_ = v_reuseFailAlloc_6427_;
goto v_reusejp_6425_;
}
v_reusejp_6425_:
{
return v___x_6426_;
}
}
}
}
else
{
lean_object* v_a_6429_; lean_object* v___x_6431_; uint8_t v_isShared_6432_; uint8_t v_isSharedCheck_6436_; 
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_a_6279_);
lean_dec(v_goal_6043_);
v_a_6429_ = lean_ctor_get(v___x_6362_, 0);
v_isSharedCheck_6436_ = !lean_is_exclusive(v___x_6362_);
if (v_isSharedCheck_6436_ == 0)
{
v___x_6431_ = v___x_6362_;
v_isShared_6432_ = v_isSharedCheck_6436_;
goto v_resetjp_6430_;
}
else
{
lean_inc(v_a_6429_);
lean_dec(v___x_6362_);
v___x_6431_ = lean_box(0);
v_isShared_6432_ = v_isSharedCheck_6436_;
goto v_resetjp_6430_;
}
v_resetjp_6430_:
{
lean_object* v___x_6434_; 
if (v_isShared_6432_ == 0)
{
v___x_6434_ = v___x_6431_;
goto v_reusejp_6433_;
}
else
{
lean_object* v_reuseFailAlloc_6435_; 
v_reuseFailAlloc_6435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6435_, 0, v_a_6429_);
v___x_6434_ = v_reuseFailAlloc_6435_;
goto v_reusejp_6433_;
}
v_reusejp_6433_:
{
return v___x_6434_;
}
}
}
}
}
}
else
{
lean_object* v_a_6438_; lean_object* v___x_6440_; uint8_t v_isShared_6441_; uint8_t v_isSharedCheck_6445_; 
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_a_6279_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6438_ = lean_ctor_get(v___x_6344_, 0);
v_isSharedCheck_6445_ = !lean_is_exclusive(v___x_6344_);
if (v_isSharedCheck_6445_ == 0)
{
v___x_6440_ = v___x_6344_;
v_isShared_6441_ = v_isSharedCheck_6445_;
goto v_resetjp_6439_;
}
else
{
lean_inc(v_a_6438_);
lean_dec(v___x_6344_);
v___x_6440_ = lean_box(0);
v_isShared_6441_ = v_isSharedCheck_6445_;
goto v_resetjp_6439_;
}
v_resetjp_6439_:
{
lean_object* v___x_6443_; 
if (v_isShared_6441_ == 0)
{
v___x_6443_ = v___x_6440_;
goto v_reusejp_6442_;
}
else
{
lean_object* v_reuseFailAlloc_6444_; 
v_reuseFailAlloc_6444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6444_, 0, v_a_6438_);
v___x_6443_ = v_reuseFailAlloc_6444_;
goto v_reusejp_6442_;
}
v_reusejp_6442_:
{
return v___x_6443_;
}
}
}
}
}
else
{
lean_object* v_a_6446_; lean_object* v___x_6448_; uint8_t v_isShared_6449_; uint8_t v_isSharedCheck_6453_; 
lean_dec_ref(v_arg_6337_);
lean_dec_ref(v_arg_6334_);
lean_dec_ref(v_arg_6331_);
lean_dec_ref(v_arg_6328_);
lean_dec(v_a_6279_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6446_ = lean_ctor_get(v___x_6341_, 0);
v_isSharedCheck_6453_ = !lean_is_exclusive(v___x_6341_);
if (v_isSharedCheck_6453_ == 0)
{
v___x_6448_ = v___x_6341_;
v_isShared_6449_ = v_isSharedCheck_6453_;
goto v_resetjp_6447_;
}
else
{
lean_inc(v_a_6446_);
lean_dec(v___x_6341_);
v___x_6448_ = lean_box(0);
v_isShared_6449_ = v_isSharedCheck_6453_;
goto v_resetjp_6447_;
}
v_resetjp_6447_:
{
lean_object* v___x_6451_; 
if (v_isShared_6449_ == 0)
{
v___x_6451_ = v___x_6448_;
goto v_reusejp_6450_;
}
else
{
lean_object* v_reuseFailAlloc_6452_; 
v_reuseFailAlloc_6452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6452_, 0, v_a_6446_);
v___x_6451_ = v_reuseFailAlloc_6452_;
goto v_reusejp_6450_;
}
v_reusejp_6450_:
{
return v___x_6451_;
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
lean_object* v_a_6454_; lean_object* v___x_6456_; uint8_t v_isShared_6457_; uint8_t v_isSharedCheck_6461_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6454_ = lean_ctor_get(v___x_6323_, 0);
v_isSharedCheck_6461_ = !lean_is_exclusive(v___x_6323_);
if (v_isSharedCheck_6461_ == 0)
{
v___x_6456_ = v___x_6323_;
v_isShared_6457_ = v_isSharedCheck_6461_;
goto v_resetjp_6455_;
}
else
{
lean_inc(v_a_6454_);
lean_dec(v___x_6323_);
v___x_6456_ = lean_box(0);
v_isShared_6457_ = v_isSharedCheck_6461_;
goto v_resetjp_6455_;
}
v_resetjp_6455_:
{
lean_object* v___x_6459_; 
if (v_isShared_6457_ == 0)
{
v___x_6459_ = v___x_6456_;
goto v_reusejp_6458_;
}
else
{
lean_object* v_reuseFailAlloc_6460_; 
v_reuseFailAlloc_6460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6460_, 0, v_a_6454_);
v___x_6459_ = v_reuseFailAlloc_6460_;
goto v_reusejp_6458_;
}
v_reusejp_6458_:
{
return v___x_6459_;
}
}
}
}
}
else
{
lean_object* v_a_6462_; lean_object* v___x_6464_; uint8_t v_isShared_6465_; uint8_t v_isSharedCheck_6469_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6462_ = lean_ctor_get(v___x_6320_, 0);
v_isSharedCheck_6469_ = !lean_is_exclusive(v___x_6320_);
if (v_isSharedCheck_6469_ == 0)
{
v___x_6464_ = v___x_6320_;
v_isShared_6465_ = v_isSharedCheck_6469_;
goto v_resetjp_6463_;
}
else
{
lean_inc(v_a_6462_);
lean_dec(v___x_6320_);
v___x_6464_ = lean_box(0);
v_isShared_6465_ = v_isSharedCheck_6469_;
goto v_resetjp_6463_;
}
v_resetjp_6463_:
{
lean_object* v___x_6467_; 
if (v_isShared_6465_ == 0)
{
v___x_6467_ = v___x_6464_;
goto v_reusejp_6466_;
}
else
{
lean_object* v_reuseFailAlloc_6468_; 
v_reuseFailAlloc_6468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6468_, 0, v_a_6462_);
v___x_6467_ = v_reuseFailAlloc_6468_;
goto v_reusejp_6466_;
}
v_reusejp_6466_:
{
return v___x_6467_;
}
}
}
}
}
else
{
lean_object* v_a_6470_; lean_object* v___x_6472_; uint8_t v_isShared_6473_; uint8_t v_isSharedCheck_6477_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6470_ = lean_ctor_get(v___x_6317_, 0);
v_isSharedCheck_6477_ = !lean_is_exclusive(v___x_6317_);
if (v_isSharedCheck_6477_ == 0)
{
v___x_6472_ = v___x_6317_;
v_isShared_6473_ = v_isSharedCheck_6477_;
goto v_resetjp_6471_;
}
else
{
lean_inc(v_a_6470_);
lean_dec(v___x_6317_);
v___x_6472_ = lean_box(0);
v_isShared_6473_ = v_isSharedCheck_6477_;
goto v_resetjp_6471_;
}
v_resetjp_6471_:
{
lean_object* v___x_6475_; 
if (v_isShared_6473_ == 0)
{
v___x_6475_ = v___x_6472_;
goto v_reusejp_6474_;
}
else
{
lean_object* v_reuseFailAlloc_6476_; 
v_reuseFailAlloc_6476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6476_, 0, v_a_6470_);
v___x_6475_ = v_reuseFailAlloc_6476_;
goto v_reusejp_6474_;
}
v_reusejp_6474_:
{
return v___x_6475_;
}
}
}
}
}
else
{
lean_object* v_a_6478_; lean_object* v___x_6480_; uint8_t v_isShared_6481_; uint8_t v_isSharedCheck_6485_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6478_ = lean_ctor_get(v___x_6314_, 0);
v_isSharedCheck_6485_ = !lean_is_exclusive(v___x_6314_);
if (v_isSharedCheck_6485_ == 0)
{
v___x_6480_ = v___x_6314_;
v_isShared_6481_ = v_isSharedCheck_6485_;
goto v_resetjp_6479_;
}
else
{
lean_inc(v_a_6478_);
lean_dec(v___x_6314_);
v___x_6480_ = lean_box(0);
v_isShared_6481_ = v_isSharedCheck_6485_;
goto v_resetjp_6479_;
}
v_resetjp_6479_:
{
lean_object* v___x_6483_; 
if (v_isShared_6481_ == 0)
{
v___x_6483_ = v___x_6480_;
goto v_reusejp_6482_;
}
else
{
lean_object* v_reuseFailAlloc_6484_; 
v_reuseFailAlloc_6484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6484_, 0, v_a_6478_);
v___x_6483_ = v_reuseFailAlloc_6484_;
goto v_reusejp_6482_;
}
v_reusejp_6482_:
{
return v___x_6483_;
}
}
}
}
}
else
{
lean_object* v_a_6486_; lean_object* v___x_6488_; uint8_t v_isShared_6489_; uint8_t v_isSharedCheck_6493_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6486_ = lean_ctor_get(v___x_6311_, 0);
v_isSharedCheck_6493_ = !lean_is_exclusive(v___x_6311_);
if (v_isSharedCheck_6493_ == 0)
{
v___x_6488_ = v___x_6311_;
v_isShared_6489_ = v_isSharedCheck_6493_;
goto v_resetjp_6487_;
}
else
{
lean_inc(v_a_6486_);
lean_dec(v___x_6311_);
v___x_6488_ = lean_box(0);
v_isShared_6489_ = v_isSharedCheck_6493_;
goto v_resetjp_6487_;
}
v_resetjp_6487_:
{
lean_object* v___x_6491_; 
if (v_isShared_6489_ == 0)
{
v___x_6491_ = v___x_6488_;
goto v_reusejp_6490_;
}
else
{
lean_object* v_reuseFailAlloc_6492_; 
v_reuseFailAlloc_6492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6492_, 0, v_a_6486_);
v___x_6491_ = v_reuseFailAlloc_6492_;
goto v_reusejp_6490_;
}
v_reusejp_6490_:
{
return v___x_6491_;
}
}
}
}
}
else
{
lean_object* v_a_6494_; lean_object* v___x_6496_; uint8_t v_isShared_6497_; uint8_t v_isSharedCheck_6501_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6494_ = lean_ctor_get(v___x_6308_, 0);
v_isSharedCheck_6501_ = !lean_is_exclusive(v___x_6308_);
if (v_isSharedCheck_6501_ == 0)
{
v___x_6496_ = v___x_6308_;
v_isShared_6497_ = v_isSharedCheck_6501_;
goto v_resetjp_6495_;
}
else
{
lean_inc(v_a_6494_);
lean_dec(v___x_6308_);
v___x_6496_ = lean_box(0);
v_isShared_6497_ = v_isSharedCheck_6501_;
goto v_resetjp_6495_;
}
v_resetjp_6495_:
{
lean_object* v___x_6499_; 
if (v_isShared_6497_ == 0)
{
v___x_6499_ = v___x_6496_;
goto v_reusejp_6498_;
}
else
{
lean_object* v_reuseFailAlloc_6500_; 
v_reuseFailAlloc_6500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6500_, 0, v_a_6494_);
v___x_6499_ = v_reuseFailAlloc_6500_;
goto v_reusejp_6498_;
}
v_reusejp_6498_:
{
return v___x_6499_;
}
}
}
}
}
else
{
lean_object* v_a_6502_; lean_object* v___x_6504_; uint8_t v_isShared_6505_; uint8_t v_isSharedCheck_6509_; 
lean_del_object(v___x_6281_);
lean_dec(v_a_6279_);
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6502_ = lean_ctor_get(v___x_6305_, 0);
v_isSharedCheck_6509_ = !lean_is_exclusive(v___x_6305_);
if (v_isSharedCheck_6509_ == 0)
{
v___x_6504_ = v___x_6305_;
v_isShared_6505_ = v_isSharedCheck_6509_;
goto v_resetjp_6503_;
}
else
{
lean_inc(v_a_6502_);
lean_dec(v___x_6305_);
v___x_6504_ = lean_box(0);
v_isShared_6505_ = v_isSharedCheck_6509_;
goto v_resetjp_6503_;
}
v_resetjp_6503_:
{
lean_object* v___x_6507_; 
if (v_isShared_6505_ == 0)
{
v___x_6507_ = v___x_6504_;
goto v_reusejp_6506_;
}
else
{
lean_object* v_reuseFailAlloc_6508_; 
v_reuseFailAlloc_6508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6508_, 0, v_a_6502_);
v___x_6507_ = v_reuseFailAlloc_6508_;
goto v_reusejp_6506_;
}
v_reusejp_6506_:
{
return v___x_6507_;
}
}
}
}
}
}
else
{
lean_object* v_a_6525_; lean_object* v___x_6527_; uint8_t v_isShared_6528_; uint8_t v_isSharedCheck_6532_; 
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6525_ = lean_ctor_get(v___x_6278_, 0);
v_isSharedCheck_6532_ = !lean_is_exclusive(v___x_6278_);
if (v_isSharedCheck_6532_ == 0)
{
v___x_6527_ = v___x_6278_;
v_isShared_6528_ = v_isSharedCheck_6532_;
goto v_resetjp_6526_;
}
else
{
lean_inc(v_a_6525_);
lean_dec(v___x_6278_);
v___x_6527_ = lean_box(0);
v_isShared_6528_ = v_isSharedCheck_6532_;
goto v_resetjp_6526_;
}
v_resetjp_6526_:
{
lean_object* v___x_6530_; 
if (v_isShared_6528_ == 0)
{
v___x_6530_ = v___x_6527_;
goto v_reusejp_6529_;
}
else
{
lean_object* v_reuseFailAlloc_6531_; 
v_reuseFailAlloc_6531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6531_, 0, v_a_6525_);
v___x_6530_ = v_reuseFailAlloc_6531_;
goto v_reusejp_6529_;
}
v_reusejp_6529_:
{
return v___x_6530_;
}
}
}
}
else
{
lean_object* v___x_6533_; lean_object* v___x_6535_; 
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v___x_6533_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__8));
if (v_isShared_6276_ == 0)
{
lean_ctor_set(v___x_6275_, 0, v___x_6533_);
v___x_6535_ = v___x_6275_;
goto v_reusejp_6534_;
}
else
{
lean_object* v_reuseFailAlloc_6536_; 
v_reuseFailAlloc_6536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6536_, 0, v___x_6533_);
v___x_6535_ = v_reuseFailAlloc_6536_;
goto v_reusejp_6534_;
}
v_reusejp_6534_:
{
return v___x_6535_;
}
}
}
}
else
{
lean_object* v_a_6538_; lean_object* v___x_6540_; uint8_t v_isShared_6541_; uint8_t v_isSharedCheck_6545_; 
lean_dec_ref(v_scope_6044_);
lean_dec(v_goal_6043_);
v_a_6538_ = lean_ctor_get(v___x_6272_, 0);
v_isSharedCheck_6545_ = !lean_is_exclusive(v___x_6272_);
if (v_isSharedCheck_6545_ == 0)
{
v___x_6540_ = v___x_6272_;
v_isShared_6541_ = v_isSharedCheck_6545_;
goto v_resetjp_6539_;
}
else
{
lean_inc(v_a_6538_);
lean_dec(v___x_6272_);
v___x_6540_ = lean_box(0);
v_isShared_6541_ = v_isSharedCheck_6545_;
goto v_resetjp_6539_;
}
v_resetjp_6539_:
{
lean_object* v___x_6543_; 
if (v_isShared_6541_ == 0)
{
v___x_6543_ = v___x_6540_;
goto v_reusejp_6542_;
}
else
{
lean_object* v_reuseFailAlloc_6544_; 
v_reuseFailAlloc_6544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6544_, 0, v_a_6538_);
v___x_6543_ = v_reuseFailAlloc_6544_;
goto v_reusejp_6542_;
}
v_reusejp_6542_:
{
return v___x_6543_;
}
}
}
v___jp_6057_:
{
lean_object* v___x_6059_; lean_object* v___x_6060_; 
v___x_6059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6059_, 0, v_scope_6044_);
lean_ctor_set(v___x_6059_, 1, v_gs_6058_);
v___x_6060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6059_);
return v___x_6060_;
}
v___jp_6061_:
{
lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; 
v___x_6063_ = lean_box(0);
v___x_6064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6064_, 0, v_g_6062_);
lean_ctor_set(v___x_6064_, 1, v___x_6063_);
v___x_6065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6065_, 0, v_scope_6044_);
lean_ctor_set(v___x_6065_, 1, v___x_6064_);
v___x_6066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6065_);
return v___x_6066_;
}
v___jp_6067_:
{
lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; 
v___x_6070_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___y_6068_);
lean_ctor_set(v___x_6070_, 1, v___y_6069_);
v___x_6071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6070_);
v___x_6072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
return v___x_6072_;
}
v___jp_6073_:
{
lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; 
v___x_6076_ = lean_box(0);
v___x_6077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6077_, 0, v_g_6075_);
lean_ctor_set(v___x_6077_, 1, v___x_6076_);
v___x_6078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___y_6074_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
return v___x_6079_;
}
v___jp_6080_:
{
lean_object* v___x_6083_; lean_object* v___x_6084_; 
v___x_6083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6083_, 0, v___y_6081_);
lean_ctor_set(v___x_6083_, 1, v_gs_6082_);
v___x_6084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6084_, 0, v___x_6083_);
return v___x_6084_;
}
v___jp_6085_:
{
lean_object* v___x_6089_; 
v___x_6089_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_6088_);
if (lean_obj_tag(v___x_6089_) == 0)
{
lean_object* v___x_6091_; uint8_t v_isShared_6092_; uint8_t v_isSharedCheck_6099_; 
v_isSharedCheck_6099_ = !lean_is_exclusive(v___x_6089_);
if (v_isSharedCheck_6099_ == 0)
{
lean_object* v_unused_6100_; 
v_unused_6100_ = lean_ctor_get(v___x_6089_, 0);
lean_dec(v_unused_6100_);
v___x_6091_ = v___x_6089_;
v_isShared_6092_ = v_isSharedCheck_6099_;
goto v_resetjp_6090_;
}
else
{
lean_dec(v___x_6089_);
v___x_6091_ = lean_box(0);
v_isShared_6092_ = v_isSharedCheck_6099_;
goto v_resetjp_6090_;
}
v_resetjp_6090_:
{
lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6097_; 
v___x_6093_ = lean_box(0);
v___x_6094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6094_, 0, v_g_6087_);
lean_ctor_set(v___x_6094_, 1, v___x_6093_);
v___x_6095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___y_6086_);
lean_ctor_set(v___x_6095_, 1, v___x_6094_);
if (v_isShared_6092_ == 0)
{
lean_ctor_set(v___x_6091_, 0, v___x_6095_);
v___x_6097_ = v___x_6091_;
goto v_reusejp_6096_;
}
else
{
lean_object* v_reuseFailAlloc_6098_; 
v_reuseFailAlloc_6098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6098_, 0, v___x_6095_);
v___x_6097_ = v_reuseFailAlloc_6098_;
goto v_reusejp_6096_;
}
v_reusejp_6096_:
{
return v___x_6097_;
}
}
}
else
{
lean_object* v_a_6101_; lean_object* v___x_6103_; uint8_t v_isShared_6104_; uint8_t v_isSharedCheck_6108_; 
lean_dec(v_g_6087_);
lean_dec_ref(v___y_6086_);
v_a_6101_ = lean_ctor_get(v___x_6089_, 0);
v_isSharedCheck_6108_ = !lean_is_exclusive(v___x_6089_);
if (v_isSharedCheck_6108_ == 0)
{
v___x_6103_ = v___x_6089_;
v_isShared_6104_ = v_isSharedCheck_6108_;
goto v_resetjp_6102_;
}
else
{
lean_inc(v_a_6101_);
lean_dec(v___x_6089_);
v___x_6103_ = lean_box(0);
v_isShared_6104_ = v_isSharedCheck_6108_;
goto v_resetjp_6102_;
}
v_resetjp_6102_:
{
lean_object* v___x_6106_; 
if (v_isShared_6104_ == 0)
{
v___x_6106_ = v___x_6103_;
goto v_reusejp_6105_;
}
else
{
lean_object* v_reuseFailAlloc_6107_; 
v_reuseFailAlloc_6107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6107_, 0, v_a_6101_);
v___x_6106_ = v_reuseFailAlloc_6107_;
goto v_reusejp_6105_;
}
v_reusejp_6105_:
{
return v___x_6106_;
}
}
}
}
v___jp_6109_:
{
lean_object* v___x_6123_; 
v___x_6123_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_6114_);
if (lean_obj_tag(v___x_6123_) == 0)
{
lean_object* v___x_6124_; 
lean_dec_ref_known(v___x_6123_, 1);
v___x_6124_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(v___y_6120_, v_goal_6043_, v___y_6112_, v___y_6116_, v___y_6114_, v___y_6110_, v___y_6118_, v___y_6117_, v___y_6115_, v___y_6119_, v___y_6122_, v___y_6111_, v___y_6113_, v___y_6121_);
return v___x_6124_;
}
else
{
lean_object* v_a_6125_; lean_object* v___x_6127_; uint8_t v_isShared_6128_; uint8_t v_isSharedCheck_6132_; 
lean_dec_ref(v___y_6120_);
lean_dec_ref(v___y_6112_);
lean_dec(v_goal_6043_);
v_a_6125_ = lean_ctor_get(v___x_6123_, 0);
v_isSharedCheck_6132_ = !lean_is_exclusive(v___x_6123_);
if (v_isSharedCheck_6132_ == 0)
{
v___x_6127_ = v___x_6123_;
v_isShared_6128_ = v_isSharedCheck_6132_;
goto v_resetjp_6126_;
}
else
{
lean_inc(v_a_6125_);
lean_dec(v___x_6123_);
v___x_6127_ = lean_box(0);
v_isShared_6128_ = v_isSharedCheck_6132_;
goto v_resetjp_6126_;
}
v_resetjp_6126_:
{
lean_object* v___x_6130_; 
if (v_isShared_6128_ == 0)
{
v___x_6130_ = v___x_6127_;
goto v_reusejp_6129_;
}
else
{
lean_object* v_reuseFailAlloc_6131_; 
v_reuseFailAlloc_6131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6131_, 0, v_a_6125_);
v___x_6130_ = v_reuseFailAlloc_6131_;
goto v_reusejp_6129_;
}
v_reusejp_6129_:
{
return v___x_6130_;
}
}
}
}
v___jp_6133_:
{
lean_object* v___x_6149_; lean_object* v___x_6150_; 
lean_dec_ref(v___y_6137_);
lean_dec_ref(v___y_6134_);
v___x_6149_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v___y_6135_);
lean_inc_ref(v___x_6149_);
v___x_6150_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v___x_6149_, v___y_6138_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
if (lean_obj_tag(v___x_6150_) == 0)
{
lean_object* v_a_6151_; lean_object* v___x_6153_; uint8_t v_isShared_6154_; uint8_t v_isSharedCheck_6263_; 
v_a_6151_ = lean_ctor_get(v___x_6150_, 0);
v_isSharedCheck_6263_ = !lean_is_exclusive(v___x_6150_);
if (v_isSharedCheck_6263_ == 0)
{
v___x_6153_ = v___x_6150_;
v_isShared_6154_ = v_isSharedCheck_6263_;
goto v_resetjp_6152_;
}
else
{
lean_inc(v_a_6151_);
lean_dec(v___x_6150_);
v___x_6153_ = lean_box(0);
v_isShared_6154_ = v_isSharedCheck_6263_;
goto v_resetjp_6152_;
}
v_resetjp_6152_:
{
uint8_t v___x_6155_; 
v___x_6155_ = lean_unbox(v_a_6151_);
lean_dec(v_a_6151_);
if (v___x_6155_ == 0)
{
lean_object* v___x_6156_; 
lean_del_object(v___x_6153_);
lean_inc_ref(v___y_6135_);
lean_inc(v_goal_6043_);
v___x_6156_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(v_goal_6043_, v___y_6135_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
if (lean_obj_tag(v___x_6156_) == 0)
{
lean_object* v_a_6157_; 
v_a_6157_ = lean_ctor_get(v___x_6156_, 0);
lean_inc(v_a_6157_);
lean_dec_ref_known(v___x_6156_, 1);
if (lean_obj_tag(v_a_6157_) == 1)
{
lean_object* v_val_6158_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_val_6158_ = lean_ctor_get(v_a_6157_, 0);
lean_inc(v_val_6158_);
lean_dec_ref_known(v_a_6157_, 1);
v___y_6074_ = v___y_6136_;
v_g_6075_ = v_val_6158_;
goto v___jp_6073_;
}
else
{
lean_object* v___x_6159_; 
lean_dec(v_a_6157_);
lean_inc_ref(v___y_6135_);
lean_inc(v_goal_6043_);
v___x_6159_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(v_goal_6043_, v___y_6135_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
if (lean_obj_tag(v___x_6159_) == 0)
{
lean_object* v_a_6160_; 
v_a_6160_ = lean_ctor_get(v___x_6159_, 0);
lean_inc(v_a_6160_);
lean_dec_ref_known(v___x_6159_, 1);
if (lean_obj_tag(v_a_6160_) == 1)
{
lean_object* v_val_6161_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_val_6161_ = lean_ctor_get(v_a_6160_, 0);
lean_inc(v_val_6161_);
lean_dec_ref_known(v_a_6160_, 1);
v___y_6086_ = v___y_6136_;
v_g_6087_ = v_val_6161_;
v___y_6088_ = v___y_6139_;
goto v___jp_6085_;
}
else
{
lean_object* v___x_6162_; 
lean_dec(v_a_6160_);
lean_inc_ref(v___y_6135_);
lean_inc(v_goal_6043_);
v___x_6162_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(v_goal_6043_, v___y_6135_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
if (lean_obj_tag(v___x_6162_) == 0)
{
lean_object* v_a_6163_; 
v_a_6163_ = lean_ctor_get(v___x_6162_, 0);
lean_inc(v_a_6163_);
lean_dec_ref_known(v___x_6162_, 1);
if (lean_obj_tag(v_a_6163_) == 1)
{
lean_object* v_val_6164_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_val_6164_ = lean_ctor_get(v_a_6163_, 0);
lean_inc(v_val_6164_);
lean_dec_ref_known(v_a_6163_, 1);
v___y_6081_ = v___y_6136_;
v_gs_6082_ = v_val_6164_;
goto v___jp_6080_;
}
else
{
lean_object* v___x_6165_; 
lean_dec(v_a_6163_);
lean_inc_ref(v___y_6135_);
lean_inc(v_goal_6043_);
v___x_6165_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(v_goal_6043_, v___y_6135_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
if (lean_obj_tag(v___x_6165_) == 0)
{
lean_object* v_a_6166_; 
v_a_6166_ = lean_ctor_get(v___x_6165_, 0);
lean_inc(v_a_6166_);
lean_dec_ref_known(v___x_6165_, 1);
if (lean_obj_tag(v_a_6166_) == 1)
{
lean_object* v_val_6167_; lean_object* v___x_6168_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_val_6167_ = lean_ctor_get(v_a_6166_, 0);
lean_inc(v_val_6167_);
lean_dec_ref_known(v_a_6166_, 1);
v___x_6168_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_6139_);
if (lean_obj_tag(v___x_6168_) == 0)
{
lean_object* v___x_6170_; uint8_t v_isShared_6171_; uint8_t v_isSharedCheck_6176_; 
v_isSharedCheck_6176_ = !lean_is_exclusive(v___x_6168_);
if (v_isSharedCheck_6176_ == 0)
{
lean_object* v_unused_6177_; 
v_unused_6177_ = lean_ctor_get(v___x_6168_, 0);
lean_dec(v_unused_6177_);
v___x_6170_ = v___x_6168_;
v_isShared_6171_ = v_isSharedCheck_6176_;
goto v_resetjp_6169_;
}
else
{
lean_dec(v___x_6168_);
v___x_6170_ = lean_box(0);
v_isShared_6171_ = v_isSharedCheck_6176_;
goto v_resetjp_6169_;
}
v_resetjp_6169_:
{
lean_object* v___x_6172_; lean_object* v___x_6174_; 
v___x_6172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6172_, 0, v___y_6136_);
lean_ctor_set(v___x_6172_, 1, v_val_6167_);
if (v_isShared_6171_ == 0)
{
lean_ctor_set(v___x_6170_, 0, v___x_6172_);
v___x_6174_ = v___x_6170_;
goto v_reusejp_6173_;
}
else
{
lean_object* v_reuseFailAlloc_6175_; 
v_reuseFailAlloc_6175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6175_, 0, v___x_6172_);
v___x_6174_ = v_reuseFailAlloc_6175_;
goto v_reusejp_6173_;
}
v_reusejp_6173_:
{
return v___x_6174_;
}
}
}
else
{
lean_object* v_a_6178_; lean_object* v___x_6180_; uint8_t v_isShared_6181_; uint8_t v_isSharedCheck_6185_; 
lean_dec(v_val_6167_);
lean_dec_ref(v___y_6136_);
v_a_6178_ = lean_ctor_get(v___x_6168_, 0);
v_isSharedCheck_6185_ = !lean_is_exclusive(v___x_6168_);
if (v_isSharedCheck_6185_ == 0)
{
v___x_6180_ = v___x_6168_;
v_isShared_6181_ = v_isSharedCheck_6185_;
goto v_resetjp_6179_;
}
else
{
lean_inc(v_a_6178_);
lean_dec(v___x_6168_);
v___x_6180_ = lean_box(0);
v_isShared_6181_ = v_isSharedCheck_6185_;
goto v_resetjp_6179_;
}
v_resetjp_6179_:
{
lean_object* v___x_6183_; 
if (v_isShared_6181_ == 0)
{
v___x_6183_ = v___x_6180_;
goto v_reusejp_6182_;
}
else
{
lean_object* v_reuseFailAlloc_6184_; 
v_reuseFailAlloc_6184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6184_, 0, v_a_6178_);
v___x_6183_ = v_reuseFailAlloc_6184_;
goto v_reusejp_6182_;
}
v_reusejp_6182_:
{
return v___x_6183_;
}
}
}
}
else
{
lean_object* v___x_6186_; 
lean_dec(v_a_6166_);
lean_inc_ref(v___y_6135_);
lean_inc(v_goal_6043_);
v___x_6186_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(v_goal_6043_, v___y_6135_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
if (lean_obj_tag(v___x_6186_) == 0)
{
lean_object* v_a_6187_; 
v_a_6187_ = lean_ctor_get(v___x_6186_, 0);
lean_inc(v_a_6187_);
lean_dec_ref_known(v___x_6186_, 1);
if (lean_obj_tag(v_a_6187_) == 1)
{
lean_object* v_val_6188_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_val_6188_ = lean_ctor_get(v_a_6187_, 0);
lean_inc(v_val_6188_);
lean_dec_ref_known(v_a_6187_, 1);
v___y_6086_ = v___y_6136_;
v_g_6087_ = v_val_6188_;
v___y_6088_ = v___y_6139_;
goto v___jp_6085_;
}
else
{
lean_object* v___x_6189_; 
lean_dec(v_a_6187_);
lean_inc_ref(v___y_6135_);
lean_inc(v_goal_6043_);
v___x_6189_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpHeadReduce_x3f(v_goal_6043_, v___y_6135_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
if (lean_obj_tag(v___x_6189_) == 0)
{
lean_object* v_a_6190_; 
v_a_6190_ = lean_ctor_get(v___x_6189_, 0);
lean_inc(v_a_6190_);
lean_dec_ref_known(v___x_6189_, 1);
if (lean_obj_tag(v_a_6190_) == 1)
{
lean_object* v_val_6191_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_val_6191_ = lean_ctor_get(v_a_6190_, 0);
lean_inc(v_val_6191_);
lean_dec_ref_known(v_a_6190_, 1);
v___y_6086_ = v___y_6136_;
v_g_6087_ = v_val_6191_;
v___y_6088_ = v___y_6139_;
goto v___jp_6085_;
}
else
{
lean_object* v___x_6192_; uint8_t v___x_6193_; 
lean_dec(v_a_6190_);
v___x_6192_ = l_Lean_Expr_getAppFn(v___x_6149_);
v___x_6193_ = l_Lean_Expr_isConst(v___x_6192_);
if (v___x_6193_ == 0)
{
uint8_t v___x_6194_; 
v___x_6194_ = l_Lean_Expr_isFVar(v___x_6192_);
lean_dec_ref(v___x_6192_);
if (v___x_6194_ == 0)
{
lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v_a_6201_; lean_object* v___x_6203_; uint8_t v_isShared_6204_; uint8_t v_isSharedCheck_6208_; 
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v___x_6195_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1);
v___x_6196_ = l_Lean_MessageData_ofExpr(v___x_6149_);
v___x_6197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6195_);
lean_ctor_set(v___x_6197_, 1, v___x_6196_);
v___x_6198_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3);
v___x_6199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6199_, 0, v___x_6197_);
lean_ctor_set(v___x_6199_, 1, v___x_6198_);
v___x_6200_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_6199_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
v_a_6201_ = lean_ctor_get(v___x_6200_, 0);
v_isSharedCheck_6208_ = !lean_is_exclusive(v___x_6200_);
if (v_isSharedCheck_6208_ == 0)
{
v___x_6203_ = v___x_6200_;
v_isShared_6204_ = v_isSharedCheck_6208_;
goto v_resetjp_6202_;
}
else
{
lean_inc(v_a_6201_);
lean_dec(v___x_6200_);
v___x_6203_ = lean_box(0);
v_isShared_6204_ = v_isSharedCheck_6208_;
goto v_resetjp_6202_;
}
v_resetjp_6202_:
{
lean_object* v___x_6206_; 
if (v_isShared_6204_ == 0)
{
v___x_6206_ = v___x_6203_;
goto v_reusejp_6205_;
}
else
{
lean_object* v_reuseFailAlloc_6207_; 
v_reuseFailAlloc_6207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6207_, 0, v_a_6201_);
v___x_6206_ = v_reuseFailAlloc_6207_;
goto v_reusejp_6205_;
}
v_reusejp_6205_:
{
return v___x_6206_;
}
}
}
else
{
lean_dec_ref(v___x_6149_);
v___y_6110_ = v___y_6140_;
v___y_6111_ = v___y_6146_;
v___y_6112_ = v___y_6135_;
v___y_6113_ = v___y_6147_;
v___y_6114_ = v___y_6139_;
v___y_6115_ = v___y_6143_;
v___y_6116_ = v___y_6138_;
v___y_6117_ = v___y_6142_;
v___y_6118_ = v___y_6141_;
v___y_6119_ = v___y_6144_;
v___y_6120_ = v___y_6136_;
v___y_6121_ = v___y_6148_;
v___y_6122_ = v___y_6145_;
goto v___jp_6109_;
}
}
else
{
lean_dec_ref(v___x_6192_);
lean_dec_ref(v___x_6149_);
v___y_6110_ = v___y_6140_;
v___y_6111_ = v___y_6146_;
v___y_6112_ = v___y_6135_;
v___y_6113_ = v___y_6147_;
v___y_6114_ = v___y_6139_;
v___y_6115_ = v___y_6143_;
v___y_6116_ = v___y_6138_;
v___y_6117_ = v___y_6142_;
v___y_6118_ = v___y_6141_;
v___y_6119_ = v___y_6144_;
v___y_6120_ = v___y_6136_;
v___y_6121_ = v___y_6148_;
v___y_6122_ = v___y_6145_;
goto v___jp_6109_;
}
}
}
else
{
lean_object* v_a_6209_; lean_object* v___x_6211_; uint8_t v_isShared_6212_; uint8_t v_isSharedCheck_6216_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_a_6209_ = lean_ctor_get(v___x_6189_, 0);
v_isSharedCheck_6216_ = !lean_is_exclusive(v___x_6189_);
if (v_isSharedCheck_6216_ == 0)
{
v___x_6211_ = v___x_6189_;
v_isShared_6212_ = v_isSharedCheck_6216_;
goto v_resetjp_6210_;
}
else
{
lean_inc(v_a_6209_);
lean_dec(v___x_6189_);
v___x_6211_ = lean_box(0);
v_isShared_6212_ = v_isSharedCheck_6216_;
goto v_resetjp_6210_;
}
v_resetjp_6210_:
{
lean_object* v___x_6214_; 
if (v_isShared_6212_ == 0)
{
v___x_6214_ = v___x_6211_;
goto v_reusejp_6213_;
}
else
{
lean_object* v_reuseFailAlloc_6215_; 
v_reuseFailAlloc_6215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6215_, 0, v_a_6209_);
v___x_6214_ = v_reuseFailAlloc_6215_;
goto v_reusejp_6213_;
}
v_reusejp_6213_:
{
return v___x_6214_;
}
}
}
}
}
else
{
lean_object* v_a_6217_; lean_object* v___x_6219_; uint8_t v_isShared_6220_; uint8_t v_isSharedCheck_6224_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_a_6217_ = lean_ctor_get(v___x_6186_, 0);
v_isSharedCheck_6224_ = !lean_is_exclusive(v___x_6186_);
if (v_isSharedCheck_6224_ == 0)
{
v___x_6219_ = v___x_6186_;
v_isShared_6220_ = v_isSharedCheck_6224_;
goto v_resetjp_6218_;
}
else
{
lean_inc(v_a_6217_);
lean_dec(v___x_6186_);
v___x_6219_ = lean_box(0);
v_isShared_6220_ = v_isSharedCheck_6224_;
goto v_resetjp_6218_;
}
v_resetjp_6218_:
{
lean_object* v___x_6222_; 
if (v_isShared_6220_ == 0)
{
v___x_6222_ = v___x_6219_;
goto v_reusejp_6221_;
}
else
{
lean_object* v_reuseFailAlloc_6223_; 
v_reuseFailAlloc_6223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6223_, 0, v_a_6217_);
v___x_6222_ = v_reuseFailAlloc_6223_;
goto v_reusejp_6221_;
}
v_reusejp_6221_:
{
return v___x_6222_;
}
}
}
}
}
else
{
lean_object* v_a_6225_; lean_object* v___x_6227_; uint8_t v_isShared_6228_; uint8_t v_isSharedCheck_6232_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_a_6225_ = lean_ctor_get(v___x_6165_, 0);
v_isSharedCheck_6232_ = !lean_is_exclusive(v___x_6165_);
if (v_isSharedCheck_6232_ == 0)
{
v___x_6227_ = v___x_6165_;
v_isShared_6228_ = v_isSharedCheck_6232_;
goto v_resetjp_6226_;
}
else
{
lean_inc(v_a_6225_);
lean_dec(v___x_6165_);
v___x_6227_ = lean_box(0);
v_isShared_6228_ = v_isSharedCheck_6232_;
goto v_resetjp_6226_;
}
v_resetjp_6226_:
{
lean_object* v___x_6230_; 
if (v_isShared_6228_ == 0)
{
v___x_6230_ = v___x_6227_;
goto v_reusejp_6229_;
}
else
{
lean_object* v_reuseFailAlloc_6231_; 
v_reuseFailAlloc_6231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6231_, 0, v_a_6225_);
v___x_6230_ = v_reuseFailAlloc_6231_;
goto v_reusejp_6229_;
}
v_reusejp_6229_:
{
return v___x_6230_;
}
}
}
}
}
else
{
lean_object* v_a_6233_; lean_object* v___x_6235_; uint8_t v_isShared_6236_; uint8_t v_isSharedCheck_6240_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_a_6233_ = lean_ctor_get(v___x_6162_, 0);
v_isSharedCheck_6240_ = !lean_is_exclusive(v___x_6162_);
if (v_isSharedCheck_6240_ == 0)
{
v___x_6235_ = v___x_6162_;
v_isShared_6236_ = v_isSharedCheck_6240_;
goto v_resetjp_6234_;
}
else
{
lean_inc(v_a_6233_);
lean_dec(v___x_6162_);
v___x_6235_ = lean_box(0);
v_isShared_6236_ = v_isSharedCheck_6240_;
goto v_resetjp_6234_;
}
v_resetjp_6234_:
{
lean_object* v___x_6238_; 
if (v_isShared_6236_ == 0)
{
v___x_6238_ = v___x_6235_;
goto v_reusejp_6237_;
}
else
{
lean_object* v_reuseFailAlloc_6239_; 
v_reuseFailAlloc_6239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6239_, 0, v_a_6233_);
v___x_6238_ = v_reuseFailAlloc_6239_;
goto v_reusejp_6237_;
}
v_reusejp_6237_:
{
return v___x_6238_;
}
}
}
}
}
else
{
lean_object* v_a_6241_; lean_object* v___x_6243_; uint8_t v_isShared_6244_; uint8_t v_isSharedCheck_6248_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_a_6241_ = lean_ctor_get(v___x_6159_, 0);
v_isSharedCheck_6248_ = !lean_is_exclusive(v___x_6159_);
if (v_isSharedCheck_6248_ == 0)
{
v___x_6243_ = v___x_6159_;
v_isShared_6244_ = v_isSharedCheck_6248_;
goto v_resetjp_6242_;
}
else
{
lean_inc(v_a_6241_);
lean_dec(v___x_6159_);
v___x_6243_ = lean_box(0);
v_isShared_6244_ = v_isSharedCheck_6248_;
goto v_resetjp_6242_;
}
v_resetjp_6242_:
{
lean_object* v___x_6246_; 
if (v_isShared_6244_ == 0)
{
v___x_6246_ = v___x_6243_;
goto v_reusejp_6245_;
}
else
{
lean_object* v_reuseFailAlloc_6247_; 
v_reuseFailAlloc_6247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6247_, 0, v_a_6241_);
v___x_6246_ = v_reuseFailAlloc_6247_;
goto v_reusejp_6245_;
}
v_reusejp_6245_:
{
return v___x_6246_;
}
}
}
}
}
else
{
lean_object* v_a_6249_; lean_object* v___x_6251_; uint8_t v_isShared_6252_; uint8_t v_isSharedCheck_6256_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_a_6249_ = lean_ctor_get(v___x_6156_, 0);
v_isSharedCheck_6256_ = !lean_is_exclusive(v___x_6156_);
if (v_isSharedCheck_6256_ == 0)
{
v___x_6251_ = v___x_6156_;
v_isShared_6252_ = v_isSharedCheck_6256_;
goto v_resetjp_6250_;
}
else
{
lean_inc(v_a_6249_);
lean_dec(v___x_6156_);
v___x_6251_ = lean_box(0);
v_isShared_6252_ = v_isSharedCheck_6256_;
goto v_resetjp_6250_;
}
v_resetjp_6250_:
{
lean_object* v___x_6254_; 
if (v_isShared_6252_ == 0)
{
v___x_6254_ = v___x_6251_;
goto v_reusejp_6253_;
}
else
{
lean_object* v_reuseFailAlloc_6255_; 
v_reuseFailAlloc_6255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6255_, 0, v_a_6249_);
v___x_6254_ = v_reuseFailAlloc_6255_;
goto v_reusejp_6253_;
}
v_reusejp_6253_:
{
return v___x_6254_;
}
}
}
}
else
{
lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6261_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6136_);
lean_dec(v_goal_6043_);
v___x_6257_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v___y_6135_);
lean_dec_ref(v___y_6135_);
v___x_6258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6258_, 0, v___x_6257_);
v___x_6259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6259_, 0, v___x_6258_);
if (v_isShared_6154_ == 0)
{
lean_ctor_set(v___x_6153_, 0, v___x_6259_);
v___x_6261_ = v___x_6153_;
goto v_reusejp_6260_;
}
else
{
lean_object* v_reuseFailAlloc_6262_; 
v_reuseFailAlloc_6262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6262_, 0, v___x_6259_);
v___x_6261_ = v_reuseFailAlloc_6262_;
goto v_reusejp_6260_;
}
v_reusejp_6260_:
{
return v___x_6261_;
}
}
}
}
else
{
lean_object* v_a_6264_; lean_object* v___x_6266_; uint8_t v_isShared_6267_; uint8_t v_isSharedCheck_6271_; 
lean_dec_ref(v___x_6149_);
lean_dec_ref(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec(v_goal_6043_);
v_a_6264_ = lean_ctor_get(v___x_6150_, 0);
v_isSharedCheck_6271_ = !lean_is_exclusive(v___x_6150_);
if (v_isSharedCheck_6271_ == 0)
{
v___x_6266_ = v___x_6150_;
v_isShared_6267_ = v_isSharedCheck_6271_;
goto v_resetjp_6265_;
}
else
{
lean_inc(v_a_6264_);
lean_dec(v___x_6150_);
v___x_6266_ = lean_box(0);
v_isShared_6267_ = v_isSharedCheck_6271_;
goto v_resetjp_6265_;
}
v_resetjp_6265_:
{
lean_object* v___x_6269_; 
if (v_isShared_6267_ == 0)
{
v___x_6269_ = v___x_6266_;
goto v_reusejp_6268_;
}
else
{
lean_object* v_reuseFailAlloc_6270_; 
v_reuseFailAlloc_6270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6270_, 0, v_a_6264_);
v___x_6269_ = v_reuseFailAlloc_6270_;
goto v_reusejp_6268_;
}
v_reusejp_6268_:
{
return v___x_6269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___boxed(lean_object* v_goal_6546_, lean_object* v_scope_6547_, lean_object* v___y_6548_, lean_object* v___y_6549_, lean_object* v___y_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_, lean_object* v___y_6559_){
_start:
{
lean_object* v_res_6560_; 
v_res_6560_ = l_Lean_Elab_Tactic_VCGen_solve___lam__0(v_goal_6546_, v_scope_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
lean_dec(v___y_6558_);
lean_dec_ref(v___y_6557_);
lean_dec(v___y_6556_);
lean_dec_ref(v___y_6555_);
lean_dec(v___y_6554_);
lean_dec_ref(v___y_6553_);
lean_dec(v___y_6552_);
lean_dec_ref(v___y_6551_);
lean_dec(v___y_6550_);
lean_dec(v___y_6549_);
lean_dec_ref(v___y_6548_);
return v_res_6560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve(lean_object* v_scope_6561_, lean_object* v_goal_6562_, lean_object* v_a_6563_, lean_object* v_a_6564_, lean_object* v_a_6565_, lean_object* v_a_6566_, lean_object* v_a_6567_, lean_object* v_a_6568_, lean_object* v_a_6569_, lean_object* v_a_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_, lean_object* v_a_6573_){
_start:
{
lean_object* v___f_6575_; lean_object* v___x_6576_; 
lean_inc(v_goal_6562_);
v___f_6575_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___boxed), 14, 2);
lean_closure_set(v___f_6575_, 0, v_goal_6562_);
lean_closure_set(v___f_6575_, 1, v_scope_6561_);
v___x_6576_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_6562_, v___f_6575_, v_a_6563_, v_a_6564_, v_a_6565_, v_a_6566_, v_a_6567_, v_a_6568_, v_a_6569_, v_a_6570_, v_a_6571_, v_a_6572_, v_a_6573_);
return v___x_6576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___boxed(lean_object* v_scope_6577_, lean_object* v_goal_6578_, lean_object* v_a_6579_, lean_object* v_a_6580_, lean_object* v_a_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_, lean_object* v_a_6584_, lean_object* v_a_6585_, lean_object* v_a_6586_, lean_object* v_a_6587_, lean_object* v_a_6588_, lean_object* v_a_6589_, lean_object* v_a_6590_){
_start:
{
lean_object* v_res_6591_; 
v_res_6591_ = l_Lean_Elab_Tactic_VCGen_solve(v_scope_6577_, v_goal_6578_, v_a_6579_, v_a_6580_, v_a_6581_, v_a_6582_, v_a_6583_, v_a_6584_, v_a_6585_, v_a_6586_, v_a_6587_, v_a_6588_, v_a_6589_);
lean_dec(v_a_6589_);
lean_dec_ref(v_a_6588_);
lean_dec(v_a_6587_);
lean_dec_ref(v_a_6586_);
lean_dec(v_a_6585_);
lean_dec_ref(v_a_6584_);
lean_dec(v_a_6583_);
lean_dec_ref(v_a_6582_);
lean_dec(v_a_6581_);
lean_dec(v_a_6580_);
lean_dec_ref(v_a_6579_);
return v_res_6591_;
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
