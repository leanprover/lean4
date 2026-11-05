// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.Solve
// Imports: public import Lean.Elab.Tactic.VCGen.Context public import Lean.Elab.Tactic.VCGen.RuleCache public import Lean.Elab.Tactic.VCGen.Entails public import Lean.Elab.Tactic.VCGen.JoinPoint public import Lean.Elab.Tactic.VCGen.BinderName public import Lean.Meta.Sym.InstantiateS public import Lean.Meta.Sym.Simp.App import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS import Init.Data.Prod
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_introPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_prog(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_registerJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Elab_Tactic_VCGen_isProgramName(lean_object*);
lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_numBindersToIntro(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Expr_stripArgsN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorem_global_x3f(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Pred(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkCongr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_introsExcessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_findSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_M(lean_object*);
lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc;
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_wpJump_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_consumeBinderNameHint_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forall"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(169, 112, 70, 140, 78, 80, 193, 185)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(14, 81, 9, 215, 230, 198, 87, 3)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Failed to intro forall target "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__1;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 33, 148, 124, 218, 91, 248, 169)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__6;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "of_top_le_prop"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(112, 50, 129, 57, 86, 19, 237, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "le_prop_of_right"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 133, 84, 135, 43, 159, 224, 56)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 43, .m_data = "Failed to cancel the `⊓ ⊤` precondition of "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 160, 150, 32, 134, 96, 114, 42)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Failed to eliminate the `iSup` precondition of "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iSup"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(46, 241, 153, 184, 251, 59, 2, 100)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3_value;
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpReduceHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpReduceHead_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Failed to intro the `let` of"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let-hoist: "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to apply split rule for "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__4;
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "frame: the weakest footprint is not a `wp` application for"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "frame: spec rule left no precondition VC for"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "frame rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "frame: split VC is not an entailment"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "frame: failed to apply rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "`@[frameproc]` framed "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "frameproc: the spec must run at "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = " state arguments for now, got "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Failed to construct rule "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nerror: "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\ntarget:"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\nPred:"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__21;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\nexcessArgs: "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__22_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__23;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Failed to apply spec "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 11, .m_data = "📜 Program: "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 10, .m_data = "🎯 Target: "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
return v_k_6_;
}
case 3:
{
lean_object* v_pre_7_; lean_object* v_rhs_8_; lean_object* v___x_9_; 
v_pre_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_pre_7_);
v_rhs_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_rhs_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_pre_7_, v_rhs_8_);
return v___x_9_;
}
case 4:
{
lean_object* v_e_10_; lean_object* v_monad_11_; lean_object* v_thms_12_; lean_object* v___x_13_; 
v_e_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_e_10_);
v_monad_11_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_monad_11_);
v_thms_12_ = lean_ctor_get(v_t_5_, 2);
lean_inc_ref(v_thms_12_);
lean_dec_ref_known(v_t_5_, 3);
v___x_13_ = lean_apply_3(v_k_6_, v_e_10_, v_monad_11_, v_thms_12_);
return v___x_13_;
}
default: 
{
lean_object* v_m_14_; lean_object* v___x_15_; 
v_m_14_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_m_14_);
lean_dec(v_t_5_);
v___x_15_ = lean_apply_1(v_k_6_, v_m_14_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_18_, v_k_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_24_, v_h_25_, v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_outOfFuel_elim___redArg(lean_object* v_t_28_, lean_object* v_outOfFuel_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_28_, v_outOfFuel_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_outOfFuel_elim(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_outOfFuel_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_32_, v_outOfFuel_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_untilPatternMatched_elim___redArg(lean_object* v_t_36_, lean_object* v_untilPatternMatched_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_36_, v_untilPatternMatched_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_untilPatternMatched_elim(lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_untilPatternMatched_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_40_, v_untilPatternMatched_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noEntailment_elim___redArg(lean_object* v_t_44_, lean_object* v_noEntailment_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_44_, v_noEntailment_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noEntailment_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_noEntailment_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_48_, v_noEntailment_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noProgress_elim___redArg(lean_object* v_t_52_, lean_object* v_noProgress_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_52_, v_noProgress_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noProgress_elim(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_noProgress_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_56_, v_noProgress_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noSpecFound_elim___redArg(lean_object* v_t_60_, lean_object* v_noSpecFound_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_60_, v_noSpecFound_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_noSpecFound_elim(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_noSpecFound_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Elab_Tactic_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_64_, v_noSpecFound_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorIdx___impl(lean_object* v_x_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_obj_tag_nat(v_x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorIdx___impl___boxed(lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorIdx___impl(v_x_70_);
lean_dec_ref(v_x_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(lean_object* v_t_72_, lean_object* v_k_73_){
_start:
{
if (lean_obj_tag(v_t_72_) == 0)
{
lean_object* v_scope_74_; lean_object* v_subgoals_75_; lean_object* v___x_76_; 
v_scope_74_ = lean_ctor_get(v_t_72_, 0);
lean_inc_ref(v_scope_74_);
v_subgoals_75_ = lean_ctor_get(v_t_72_, 1);
lean_inc(v_subgoals_75_);
lean_dec_ref_known(v_t_72_, 2);
v___x_76_ = lean_apply_2(v_k_73_, v_scope_74_, v_subgoals_75_);
return v___x_76_;
}
else
{
lean_object* v_reason_77_; lean_object* v___x_78_; 
v_reason_77_ = lean_ctor_get(v_t_72_, 0);
lean_inc(v_reason_77_);
lean_dec_ref_known(v_t_72_, 1);
v___x_78_ = lean_apply_1(v_k_73_, v_reason_77_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim(lean_object* v_motive_79_, lean_object* v_ctorIdx_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_k_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(v_t_81_, v_k_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___boxed(lean_object* v_motive_85_, lean_object* v_ctorIdx_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_k_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim(v_motive_85_, v_ctorIdx_86_, v_t_87_, v_h_88_, v_k_89_);
lean_dec(v_ctorIdx_86_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_goals_elim___redArg(lean_object* v_t_91_, lean_object* v_goals_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(v_t_91_, v_goals_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_goals_elim(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_goals_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(v_t_95_, v_goals_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_stop_elim___redArg(lean_object* v_t_99_, lean_object* v_stop_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(v_t_99_, v_stop_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_SolveResult_stop_elim(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_stop_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Elab_Tactic_VCGen_SolveResult_ctorElim___redArg(v_t_103_, v_stop_105_);
return v___x_106_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable(lean_object* v_e_112_){
_start:
{
switch(lean_obj_tag(v_e_112_))
{
case 5:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___closed__2));
v___x_114_ = l_Lean_Expr_isAppOf(v_e_112_, v___x_113_);
return v___x_114_;
}
case 6:
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
case 7:
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
case 8:
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
case 10:
{
lean_object* v_expr_118_; 
v_expr_118_ = lean_ctor_get(v_e_112_, 1);
v_e_112_ = v_expr_118_;
goto _start;
}
case 11:
{
lean_object* v_struct_120_; 
v_struct_120_ = lean_ctor_get(v_e_112_, 2);
v_e_112_ = v_struct_120_;
goto _start;
}
default: 
{
uint8_t v___x_122_; 
v___x_122_ = 1;
return v___x_122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable___boxed(lean_object* v_e_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable(v_e_123_);
lean_dec_ref(v_e_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg(lean_object* v_goal_126_, lean_object* v_target_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
uint8_t v___x_133_; 
v___x_133_ = l_Lean_Expr_isMData(v_target_127_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_goal_126_);
v___x_134_ = lean_box(0);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = l_Lean_Expr_consumeMData(v_target_127_);
v___x_137_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_126_, v___x_136_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_146_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_146_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_142_, 0, v_a_138_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_142_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
v_a_147_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_137_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_137_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg___boxed(lean_object* v_goal_155_, lean_object* v_target_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg(v_goal_155_, v_target_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec_ref(v_target_156_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f(lean_object* v_goal_163_, lean_object* v_target_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg(v_goal_163_, v_target_164_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___boxed(lean_object* v_goal_178_, lean_object* v_target_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f(v_goal_178_, v_target_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec_ref(v_target_179_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0___redArg(lean_object* v_declName_193_, lean_object* v_us_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = l_Lean_Expr_const___override(v_declName_193_, v_us_194_);
v___x_198_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_197_, v___y_195_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0___redArg___boxed(lean_object* v_declName_199_, lean_object* v_us_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0___redArg(v_declName_199_, v_us_200_, v___y_201_);
lean_dec(v___y_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0(lean_object* v_declName_204_, lean_object* v_us_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0___redArg(v_declName_204_, v_us_205_, v___y_212_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0___boxed(lean_object* v_declName_219_, lean_object* v_us_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0(v_declName_219_, v_us_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg___lam__0(lean_object* v_x_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; 
lean_inc(v___y_241_);
lean_inc_ref(v___y_240_);
lean_inc(v___y_239_);
lean_inc_ref(v___y_238_);
lean_inc(v___y_237_);
lean_inc(v___y_236_);
lean_inc_ref(v___y_235_);
v___x_247_ = lean_apply_12(v_x_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, lean_box(0));
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg___lam__0___boxed(lean_object* v_x_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg___lam__0(v_x_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg(lean_object* v_mvarId_262_, lean_object* v_x_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___f_276_; lean_object* v___x_277_; 
lean_inc(v___y_270_);
lean_inc_ref(v___y_269_);
lean_inc(v___y_268_);
lean_inc_ref(v___y_267_);
lean_inc(v___y_266_);
lean_inc(v___y_265_);
lean_inc_ref(v___y_264_);
v___f_276_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_276_, 0, v_x_263_);
lean_closure_set(v___f_276_, 1, v___y_264_);
lean_closure_set(v___f_276_, 2, v___y_265_);
lean_closure_set(v___f_276_, 3, v___y_266_);
lean_closure_set(v___f_276_, 4, v___y_267_);
lean_closure_set(v___f_276_, 5, v___y_268_);
lean_closure_set(v___f_276_, 6, v___y_269_);
lean_closure_set(v___f_276_, 7, v___y_270_);
v___x_277_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_262_, v___f_276_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_277_) == 0)
{
return v___x_277_;
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg___boxed(lean_object* v_mvarId_286_, lean_object* v_x_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg(v_mvarId_286_, v_x_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3(lean_object* v_00_u03b1_301_, lean_object* v_mvarId_302_, lean_object* v_x_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg(v_mvarId_302_, v_x_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___boxed(lean_object* v_00_u03b1_317_, lean_object* v_mvarId_318_, lean_object* v_x_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3(v_00_u03b1_317_, v_mvarId_318_, v_x_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3___redArg(lean_object* v_f_333_, lean_object* v_a_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___y_343_; lean_object* v___x_346_; uint8_t v_debug_347_; 
v___x_346_ = lean_st_ref_get(v___y_336_);
v_debug_347_ = lean_ctor_get_uint8(v___x_346_, sizeof(void*)*13);
lean_dec(v___x_346_);
if (v_debug_347_ == 0)
{
v___y_343_ = v___y_336_;
goto v___jp_342_;
}
else
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_333_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v___x_349_; 
lean_dec_ref_known(v___x_348_, 1);
v___x_349_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_dec_ref_known(v___x_349_, 1);
v___y_343_ = v___y_336_;
goto v___jp_342_;
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v_a_334_);
lean_dec_ref(v_f_333_);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v_a_334_);
lean_dec_ref(v_f_333_);
v_a_358_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_348_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_348_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = l_Lean_Expr_app___override(v_f_333_, v_a_334_);
v___x_345_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_344_, v___y_343_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_f_366_, lean_object* v_a_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3___redArg(v_f_366_, v_a_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1(lean_object* v_args_376_, lean_object* v_endIdx_377_, lean_object* v_b_378_, lean_object* v_i_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = lean_nat_dec_le(v_endIdx_377_, v_i_379_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = l_Lean_instInhabitedExpr;
v___x_394_ = lean_array_get_borrowed(v___x_393_, v_args_376_, v_i_379_);
lean_inc(v___x_394_);
v___x_395_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3___redArg(v_b_378_, v___x_394_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_395_, 1);
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_nat_add(v_i_379_, v___x_397_);
lean_dec(v_i_379_);
v_b_378_ = v_a_396_;
v_i_379_ = v___x_398_;
goto _start;
}
else
{
lean_dec(v_i_379_);
return v___x_395_;
}
}
else
{
lean_object* v___x_400_; 
lean_dec(v_i_379_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_b_378_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1___boxed(lean_object* v_args_401_, lean_object* v_endIdx_402_, lean_object* v_b_403_, lean_object* v_i_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1(v_args_401_, v_endIdx_402_, v_b_403_, v_i_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v_endIdx_402_);
lean_dec_ref(v_args_401_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(lean_object* v_f_418_, lean_object* v_args_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_array_get_size(v_args_419_);
v___x_434_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1(v_args_419_, v___x_433_, v_f_418_, v___x_432_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1___boxed(lean_object* v_f_435_, lean_object* v_args_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(v_f_435_, v_args_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec_ref(v_args_436_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
lean_object* v_ks_454_; lean_object* v_vs_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_479_; 
v_ks_454_ = lean_ctor_get(v_x_450_, 0);
v_vs_455_ = lean_ctor_get(v_x_450_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_x_450_);
if (v_isSharedCheck_479_ == 0)
{
v___x_457_ = v_x_450_;
v_isShared_458_ = v_isSharedCheck_479_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_vs_455_);
lean_inc(v_ks_454_);
lean_dec(v_x_450_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_479_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_array_get_size(v_ks_454_);
v___x_460_ = lean_nat_dec_lt(v_x_451_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
lean_dec(v_x_451_);
v___x_461_ = lean_array_push(v_ks_454_, v_x_452_);
v___x_462_ = lean_array_push(v_vs_455_, v_x_453_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v___x_462_);
lean_ctor_set(v___x_457_, 0, v___x_461_);
v___x_464_ = v___x_457_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
else
{
lean_object* v_k_x27_466_; uint8_t v___x_467_; 
v_k_x27_466_ = lean_array_fget_borrowed(v_ks_454_, v_x_451_);
v___x_467_ = l_Lean_instBEqMVarId_beq(v_x_452_, v_k_x27_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_469_; 
if (v_isShared_458_ == 0)
{
v___x_469_ = v___x_457_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_ks_454_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_vs_455_);
v___x_469_ = v_reuseFailAlloc_473_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = lean_nat_add(v_x_451_, v___x_470_);
lean_dec(v_x_451_);
v_x_450_ = v___x_469_;
v_x_451_ = v___x_471_;
goto _start;
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = lean_array_fset(v_ks_454_, v_x_451_, v_x_452_);
v___x_475_ = lean_array_fset(v_vs_455_, v_x_451_, v_x_453_);
lean_dec(v_x_451_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v___x_475_);
lean_ctor_set(v___x_457_, 0, v___x_474_);
v___x_477_ = v___x_457_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7___redArg(lean_object* v_n_480_, lean_object* v_k_481_, lean_object* v_v_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(v_n_480_, v___x_483_, v_k_481_, v_v_482_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg(lean_object* v_x_486_, size_t v_x_487_, size_t v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
lean_object* v_es_491_; size_t v___x_492_; size_t v___x_493_; lean_object* v_j_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_es_491_ = lean_ctor_get(v_x_486_, 0);
v___x_492_ = ((size_t)31ULL);
v___x_493_ = lean_usize_land(v_x_487_, v___x_492_);
v_j_494_ = lean_usize_to_nat(v___x_493_);
v___x_495_ = lean_array_get_size(v_es_491_);
v___x_496_ = lean_nat_dec_lt(v_j_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_dec(v_j_494_);
lean_dec(v_x_490_);
lean_dec(v_x_489_);
return v_x_486_;
}
else
{
lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_535_; 
lean_inc_ref(v_es_491_);
v_isSharedCheck_535_ = !lean_is_exclusive(v_x_486_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; 
v_unused_536_ = lean_ctor_get(v_x_486_, 0);
lean_dec(v_unused_536_);
v___x_498_ = v_x_486_;
v_isShared_499_ = v_isSharedCheck_535_;
goto v_resetjp_497_;
}
else
{
lean_dec(v_x_486_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_535_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v_v_500_; lean_object* v___x_501_; lean_object* v_xs_x27_502_; lean_object* v___y_504_; 
v_v_500_ = lean_array_fget(v_es_491_, v_j_494_);
v___x_501_ = lean_box(0);
v_xs_x27_502_ = lean_array_fset(v_es_491_, v_j_494_, v___x_501_);
switch(lean_obj_tag(v_v_500_))
{
case 0:
{
lean_object* v_key_509_; lean_object* v_val_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_520_; 
v_key_509_ = lean_ctor_get(v_v_500_, 0);
v_val_510_ = lean_ctor_get(v_v_500_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_v_500_);
if (v_isSharedCheck_520_ == 0)
{
v___x_512_ = v_v_500_;
v_isShared_513_ = v_isSharedCheck_520_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_val_510_);
lean_inc(v_key_509_);
lean_dec(v_v_500_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_520_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___x_514_; 
v___x_514_ = l_Lean_instBEqMVarId_beq(v_x_489_, v_key_509_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_del_object(v___x_512_);
v___x_515_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_509_, v_val_510_, v_x_489_, v_x_490_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
v___y_504_ = v___x_516_;
goto v___jp_503_;
}
else
{
lean_object* v___x_518_; 
lean_dec(v_val_510_);
lean_dec(v_key_509_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v_x_490_);
lean_ctor_set(v___x_512_, 0, v_x_489_);
v___x_518_ = v___x_512_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_x_489_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_x_490_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
v___y_504_ = v___x_518_;
goto v___jp_503_;
}
}
}
}
case 1:
{
lean_object* v_node_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_533_; 
v_node_521_ = lean_ctor_get(v_v_500_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_v_500_);
if (v_isSharedCheck_533_ == 0)
{
v___x_523_ = v_v_500_;
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_node_521_);
lean_dec(v_v_500_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
size_t v___x_525_; size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_525_ = ((size_t)5ULL);
v___x_526_ = lean_usize_shift_right(v_x_487_, v___x_525_);
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_add(v_x_488_, v___x_527_);
v___x_529_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg(v_node_521_, v___x_526_, v___x_528_, v_x_489_, v_x_490_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_529_);
v___x_531_ = v___x_523_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
v___y_504_ = v___x_531_;
goto v___jp_503_;
}
}
}
default: 
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_x_489_);
lean_ctor_set(v___x_534_, 1, v_x_490_);
v___y_504_ = v___x_534_;
goto v___jp_503_;
}
}
v___jp_503_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_array_fset(v_xs_x27_502_, v_j_494_, v___y_504_);
lean_dec(v_j_494_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_505_);
v___x_507_ = v___x_498_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
else
{
lean_object* v_ks_537_; lean_object* v_vs_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_556_; 
v_ks_537_ = lean_ctor_get(v_x_486_, 0);
v_vs_538_ = lean_ctor_get(v_x_486_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_486_);
if (v_isSharedCheck_556_ == 0)
{
v___x_540_ = v_x_486_;
v_isShared_541_ = v_isSharedCheck_556_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_vs_538_);
lean_inc(v_ks_537_);
lean_dec(v_x_486_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_556_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_ks_537_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_vs_538_);
v___x_543_ = v_reuseFailAlloc_555_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v_newNode_544_; size_t v___x_545_; uint8_t v___x_546_; 
v_newNode_544_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7___redArg(v___x_543_, v_x_489_, v_x_490_);
v___x_545_ = ((size_t)7ULL);
v___x_546_ = lean_usize_dec_le(v___x_545_, v_x_488_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_547_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_544_);
v___x_548_ = lean_unsigned_to_nat(4u);
v___x_549_ = lean_nat_dec_lt(v___x_547_, v___x_548_);
lean_dec(v___x_547_);
if (v___x_549_ == 0)
{
lean_object* v_ks_550_; lean_object* v_vs_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_ks_550_ = lean_ctor_get(v_newNode_544_, 0);
lean_inc_ref(v_ks_550_);
v_vs_551_ = lean_ctor_get(v_newNode_544_, 1);
lean_inc_ref(v_vs_551_);
lean_dec_ref(v_newNode_544_);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg___closed__0);
v___x_554_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8___redArg(v_x_488_, v_ks_550_, v_vs_551_, v___x_552_, v___x_553_);
lean_dec_ref(v_vs_551_);
lean_dec_ref(v_ks_550_);
return v___x_554_;
}
else
{
return v_newNode_544_;
}
}
else
{
return v_newNode_544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8___redArg(size_t v_depth_557_, lean_object* v_keys_558_, lean_object* v_vals_559_, lean_object* v_i_560_, lean_object* v_entries_561_){
_start:
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_array_get_size(v_keys_558_);
v___x_563_ = lean_nat_dec_lt(v_i_560_, v___x_562_);
if (v___x_563_ == 0)
{
lean_dec(v_i_560_);
return v_entries_561_;
}
else
{
lean_object* v_k_564_; lean_object* v_v_565_; uint64_t v___x_566_; size_t v_h_567_; size_t v___x_568_; lean_object* v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v_h_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_k_564_ = lean_array_fget_borrowed(v_keys_558_, v_i_560_);
v_v_565_ = lean_array_fget_borrowed(v_vals_559_, v_i_560_);
v___x_566_ = l_Lean_instHashableMVarId_hash(v_k_564_);
v_h_567_ = lean_uint64_to_usize(v___x_566_);
v___x_568_ = ((size_t)5ULL);
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = ((size_t)1ULL);
v___x_571_ = lean_usize_sub(v_depth_557_, v___x_570_);
v___x_572_ = lean_usize_mul(v___x_568_, v___x_571_);
v_h_573_ = lean_usize_shift_right(v_h_567_, v___x_572_);
v___x_574_ = lean_nat_add(v_i_560_, v___x_569_);
lean_dec(v_i_560_);
lean_inc(v_v_565_);
lean_inc(v_k_564_);
v___x_575_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg(v_entries_561_, v_h_573_, v_depth_557_, v_k_564_, v_v_565_);
v_i_560_ = v___x_574_;
v_entries_561_ = v___x_575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_depth_577_, lean_object* v_keys_578_, lean_object* v_vals_579_, lean_object* v_i_580_, lean_object* v_entries_581_){
_start:
{
size_t v_depth_boxed_582_; lean_object* v_res_583_; 
v_depth_boxed_582_ = lean_unbox_usize(v_depth_577_);
lean_dec(v_depth_577_);
v_res_583_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8___redArg(v_depth_boxed_582_, v_keys_578_, v_vals_579_, v_i_580_, v_entries_581_);
lean_dec_ref(v_vals_579_);
lean_dec_ref(v_keys_578_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
size_t v_x_24721__boxed_589_; size_t v_x_24722__boxed_590_; lean_object* v_res_591_; 
v_x_24721__boxed_589_ = lean_unbox_usize(v_x_585_);
lean_dec(v_x_585_);
v_x_24722__boxed_590_ = lean_unbox_usize(v_x_586_);
lean_dec(v_x_586_);
v_res_591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg(v_x_584_, v_x_24721__boxed_589_, v_x_24722__boxed_590_, v_x_587_, v_x_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3___redArg(lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
uint64_t v___x_595_; size_t v___x_596_; size_t v___x_597_; lean_object* v___x_598_; 
v___x_595_ = l_Lean_instHashableMVarId_hash(v_x_593_);
v___x_596_ = lean_uint64_to_usize(v___x_595_);
v___x_597_ = ((size_t)1ULL);
v___x_598_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg(v_x_592_, v___x_596_, v___x_597_, v_x_593_, v_x_594_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg(lean_object* v_mvarId_599_, lean_object* v_val_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; lean_object* v_mctx_604_; lean_object* v_cache_605_; lean_object* v_zetaDeltaFVarIds_606_; lean_object* v_postponed_607_; lean_object* v_diag_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_637_; 
v___x_603_ = lean_st_ref_take(v___y_601_);
v_mctx_604_ = lean_ctor_get(v___x_603_, 0);
v_cache_605_ = lean_ctor_get(v___x_603_, 1);
v_zetaDeltaFVarIds_606_ = lean_ctor_get(v___x_603_, 2);
v_postponed_607_ = lean_ctor_get(v___x_603_, 3);
v_diag_608_ = lean_ctor_get(v___x_603_, 4);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_637_ == 0)
{
v___x_610_ = v___x_603_;
v_isShared_611_ = v_isSharedCheck_637_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_diag_608_);
lean_inc(v_postponed_607_);
lean_inc(v_zetaDeltaFVarIds_606_);
lean_inc(v_cache_605_);
lean_inc(v_mctx_604_);
lean_dec(v___x_603_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_637_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_depth_612_; lean_object* v_levelAssignDepth_613_; lean_object* v_lmvarCounter_614_; lean_object* v_mvarCounter_615_; lean_object* v_lDecls_616_; lean_object* v_decls_617_; lean_object* v_userNames_618_; lean_object* v_lAssignment_619_; lean_object* v_eAssignment_620_; lean_object* v_dAssignment_621_; lean_object* v_instanceTypedMVars_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_636_; 
v_depth_612_ = lean_ctor_get(v_mctx_604_, 0);
v_levelAssignDepth_613_ = lean_ctor_get(v_mctx_604_, 1);
v_lmvarCounter_614_ = lean_ctor_get(v_mctx_604_, 2);
v_mvarCounter_615_ = lean_ctor_get(v_mctx_604_, 3);
v_lDecls_616_ = lean_ctor_get(v_mctx_604_, 4);
v_decls_617_ = lean_ctor_get(v_mctx_604_, 5);
v_userNames_618_ = lean_ctor_get(v_mctx_604_, 6);
v_lAssignment_619_ = lean_ctor_get(v_mctx_604_, 7);
v_eAssignment_620_ = lean_ctor_get(v_mctx_604_, 8);
v_dAssignment_621_ = lean_ctor_get(v_mctx_604_, 9);
v_instanceTypedMVars_622_ = lean_ctor_get(v_mctx_604_, 10);
v_isSharedCheck_636_ = !lean_is_exclusive(v_mctx_604_);
if (v_isSharedCheck_636_ == 0)
{
v___x_624_ = v_mctx_604_;
v_isShared_625_ = v_isSharedCheck_636_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_instanceTypedMVars_622_);
lean_inc(v_dAssignment_621_);
lean_inc(v_eAssignment_620_);
lean_inc(v_lAssignment_619_);
lean_inc(v_userNames_618_);
lean_inc(v_decls_617_);
lean_inc(v_lDecls_616_);
lean_inc(v_mvarCounter_615_);
lean_inc(v_lmvarCounter_614_);
lean_inc(v_levelAssignDepth_613_);
lean_inc(v_depth_612_);
lean_dec(v_mctx_604_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_636_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_626_ = lean_box(0);
v___x_627_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3___redArg(v_eAssignment_620_, v_mvarId_599_, v_val_600_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 8, v___x_627_);
v___x_629_ = v___x_624_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_depth_612_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_levelAssignDepth_613_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_lmvarCounter_614_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_mvarCounter_615_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v_lDecls_616_);
lean_ctor_set(v_reuseFailAlloc_635_, 5, v_decls_617_);
lean_ctor_set(v_reuseFailAlloc_635_, 6, v_userNames_618_);
lean_ctor_set(v_reuseFailAlloc_635_, 7, v_lAssignment_619_);
lean_ctor_set(v_reuseFailAlloc_635_, 8, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_635_, 9, v_dAssignment_621_);
lean_ctor_set(v_reuseFailAlloc_635_, 10, v_instanceTypedMVars_622_);
v___x_629_ = v_reuseFailAlloc_635_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_629_);
v___x_631_ = v___x_610_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_cache_605_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_zetaDeltaFVarIds_606_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_postponed_607_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v_diag_608_);
v___x_631_ = v_reuseFailAlloc_634_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_st_ref_put(v___y_601_, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_626_);
return v___x_633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg___boxed(lean_object* v_mvarId_638_, lean_object* v_val_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg(v_mvarId_638_, v_val_639_, v___y_640_);
lean_dec(v___y_640_);
return v_res_642_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = l_Lean_Expr_bvar___override(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__5(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = l_Lean_Expr_bvar___override(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__17(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_box(0);
v___x_673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__16));
v___x_674_ = l_Lean_Expr_const___override(v___x_673_, v___x_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0(lean_object* v_target_675_, lean_object* v_goal_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
if (lean_obj_tag(v_target_675_) == 7)
{
lean_object* v_binderType_689_; lean_object* v_body_690_; lean_object* v___x_691_; 
v_binderType_689_ = lean_ctor_get(v_target_675_, 1);
v_body_690_ = lean_ctor_get(v_target_675_, 2);
lean_inc_ref(v_binderType_689_);
v___x_691_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_binderType_689_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_811_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_811_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_811_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_811_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = l_Lean_Expr_cleanupAnnotations(v_a_692_);
v___x_697_ = l_Lean_Expr_isApp(v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_699_; 
lean_dec_ref(v___x_696_);
lean_dec(v_a_692_);
lean_dec_ref_known(v_target_675_, 3);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_goal_676_);
v___x_699_ = v___x_694_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_goal_676_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
else
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = l_Lean_Expr_appFnCleanup___redArg(v___x_696_);
v___x_702_ = l_Lean_Expr_isApp(v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_704_; 
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_696_);
lean_dec(v_a_692_);
lean_dec_ref_known(v_target_675_, 3);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_goal_676_);
v___x_704_ = v___x_694_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_goal_676_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_706_ = l_Lean_Expr_appFnCleanup___redArg(v___x_701_);
v___x_707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__1));
v___x_708_ = l_Lean_Expr_isConstOf(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_710_; 
lean_dec_ref(v___x_706_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_696_);
lean_dec(v_a_692_);
lean_dec_ref_known(v_target_675_, 3);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_goal_676_);
v___x_710_ = v___x_694_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_goal_676_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
else
{
lean_object* v_arg_712_; lean_object* v_arg_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_del_object(v___x_694_);
v_arg_712_ = lean_ctor_get(v___x_696_, 1);
lean_inc_ref(v_arg_712_);
lean_dec_ref(v___x_696_);
v_arg_713_ = lean_ctor_get(v___x_701_, 1);
lean_inc_ref(v_arg_713_);
lean_dec_ref(v___x_701_);
v___x_714_ = l_Lean_Expr_constLevels_x21(v___x_706_);
lean_dec_ref(v___x_706_);
v___x_715_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__3));
lean_inc(v___x_714_);
v___x_716_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0___redArg(v___x_715_, v___x_714_, v___y_683_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__4, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__4);
v___x_719_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__5);
v___x_720_ = lean_unsigned_to_nat(4u);
v___x_721_ = lean_mk_empty_array_with_capacity(v___x_720_);
lean_inc_ref(v_arg_713_);
v___x_722_ = lean_array_push(v___x_721_, v_arg_713_);
lean_inc_ref(v_arg_712_);
v___x_723_ = lean_array_push(v___x_722_, v_arg_712_);
v___x_724_ = lean_array_push(v___x_723_, v___x_718_);
v___x_725_ = lean_array_push(v___x_724_, v___x_719_);
v___x_726_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(v_a_717_, v___x_725_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v___x_725_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__7));
v___x_729_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__9));
v___x_730_ = lean_expr_instantiate1(v_body_690_, v_a_727_);
lean_dec(v_a_727_);
v___x_731_ = 0;
lean_inc_ref(v_arg_712_);
v___x_732_ = l_Lean_Expr_forallE___override(v___x_729_, v_arg_712_, v___x_730_, v___x_731_);
lean_inc_ref(v_arg_713_);
v___x_733_ = l_Lean_Expr_forallE___override(v___x_728_, v_arg_713_, v___x_732_, v___x_731_);
lean_inc_ref(v___x_733_);
v___x_734_ = l_Lean_Meta_Sym_shareCommon(v___x_733_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = lean_box(0);
v___x_737_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_735_, v___x_736_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_739_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__11));
lean_inc_ref(v_body_690_);
v___x_740_ = l_Lean_Expr_lam___override(v___x_739_, v_a_692_, v_body_690_, v___x_731_);
v___x_741_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__13));
v___x_742_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__0___redArg(v___x_741_, v___x_714_, v___y_683_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v___x_744_ = lean_unsigned_to_nat(3u);
v___x_745_ = lean_mk_empty_array_with_capacity(v___x_744_);
v___x_746_ = lean_array_push(v___x_745_, v_arg_713_);
v___x_747_ = lean_array_push(v___x_746_, v_arg_712_);
v___x_748_ = lean_array_push(v___x_747_, v___x_740_);
v___x_749_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(v_a_743_, v___x_748_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v___x_748_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_761_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
v___x_751_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__17, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__17_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___closed__17);
lean_inc(v_a_738_);
v___x_752_ = l_Lean_mkApp4(v___x_751_, v_target_675_, v___x_733_, v_a_750_, v_a_738_);
v___x_753_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg(v_goal_676_, v___x_752_, v___y_685_);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v___x_753_, 0);
lean_dec(v_unused_762_);
v___x_755_ = v___x_753_;
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
else
{
lean_dec(v___x_753_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = l_Lean_Expr_mvarId_x21(v_a_738_);
lean_dec(v_a_738_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_738_);
lean_dec_ref(v___x_733_);
lean_dec_ref_known(v_target_675_, 3);
lean_dec(v_goal_676_);
v_a_763_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_749_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_749_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v___x_740_);
lean_dec(v_a_738_);
lean_dec_ref(v___x_733_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec_ref_known(v_target_675_, 3);
lean_dec(v_goal_676_);
v_a_771_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_742_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_742_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref(v___x_733_);
lean_dec(v___x_714_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec(v_a_692_);
lean_dec_ref_known(v_target_675_, 3);
lean_dec(v_goal_676_);
v_a_779_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_737_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_737_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v___x_733_);
lean_dec(v___x_714_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec(v_a_692_);
lean_dec_ref_known(v_target_675_, 3);
lean_dec(v_goal_676_);
v_a_787_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_734_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_734_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v___x_714_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec(v_a_692_);
lean_dec_ref_known(v_target_675_, 3);
lean_dec(v_goal_676_);
v_a_795_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_726_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_726_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec(v___x_714_);
lean_dec_ref(v_arg_713_);
lean_dec_ref(v_arg_712_);
lean_dec(v_a_692_);
lean_dec_ref_known(v_target_675_, 3);
lean_dec(v_goal_676_);
v_a_803_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_716_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_716_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
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
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref_known(v_target_675_, 3);
lean_dec(v_goal_676_);
v_a_812_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_691_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_691_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v___x_820_; 
lean_dec_ref(v_target_675_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_goal_676_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___boxed(lean_object* v_target_821_, lean_object* v_goal_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0(v_target_821_, v_goal_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder(lean_object* v_goal_836_, lean_object* v_target_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___y_850_; lean_object* v___x_851_; 
lean_inc(v_goal_836_);
v___y_850_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___lam__0___boxed), 14, 2);
lean_closure_set(v___y_850_, 0, v_target_837_);
lean_closure_set(v___y_850_, 1, v_goal_836_);
v___x_851_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg(v_goal_836_, v___y_850_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder___boxed(lean_object* v_goal_852_, lean_object* v_target_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder(v_goal_852_, v_target_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2(lean_object* v_mvarId_867_, lean_object* v_val_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg(v_mvarId_867_, v_val_868_, v___y_877_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___boxed(lean_object* v_mvarId_882_, lean_object* v_val_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2(v_mvarId_882_, v_val_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3(lean_object* v_f_897_, lean_object* v_a_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3___redArg(v_f_897_, v_a_898_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3___boxed(lean_object* v_f_912_, lean_object* v_a_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3(v_f_912_, v_a_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3(lean_object* v_00_u03b2_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3___redArg(v_x_928_, v_x_929_, v_x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_932_, lean_object* v_x_933_, size_t v_x_934_, size_t v_x_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___redArg(v_x_933_, v_x_934_, v_x_935_, v_x_936_, v_x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
size_t v_x_25423__boxed_945_; size_t v_x_25424__boxed_946_; lean_object* v_res_947_; 
v_x_25423__boxed_945_ = lean_unbox_usize(v_x_941_);
lean_dec(v_x_941_);
v_x_25424__boxed_946_ = lean_unbox_usize(v_x_942_);
lean_dec(v_x_942_);
v_res_947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6(v_00_u03b2_939_, v_x_940_, v_x_25423__boxed_945_, v_x_25424__boxed_946_, v_x_943_, v_x_944_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_948_, lean_object* v_n_949_, lean_object* v_k_950_, lean_object* v_v_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7___redArg(v_n_949_, v_k_950_, v_v_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_953_, size_t v_depth_954_, lean_object* v_keys_955_, lean_object* v_vals_956_, lean_object* v_heq_957_, lean_object* v_i_958_, lean_object* v_entries_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8___redArg(v_depth_954_, v_keys_955_, v_vals_956_, v_i_958_, v_entries_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_961_, lean_object* v_depth_962_, lean_object* v_keys_963_, lean_object* v_vals_964_, lean_object* v_heq_965_, lean_object* v_i_966_, lean_object* v_entries_967_){
_start:
{
size_t v_depth_boxed_968_; lean_object* v_res_969_; 
v_depth_boxed_968_ = lean_unbox_usize(v_depth_962_);
lean_dec(v_depth_962_);
v_res_969_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__8(v_00_u03b2_961_, v_depth_boxed_968_, v_keys_963_, v_vals_964_, v_heq_965_, v_i_966_, v_entries_967_);
lean_dec_ref(v_vals_964_);
lean_dec_ref(v_keys_963_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_970_, lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_x_973_, lean_object* v_x_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(v_x_971_, v_x_972_, v_x_973_, v_x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg___lam__0(lean_object* v_fst_976_, lean_object* v_snd_977_, lean_object* v_goal_x27_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = l_Lean_instBEqMVarId_beq(v_goal_x27_978_, v_fst_976_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_dec(v_snd_977_);
lean_dec(v_fst_976_);
lean_inc(v_goal_x27_978_);
v___x_992_ = l_Lean_MVarId_getType(v_goal_x27_978_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1002_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v_goal_x27_978_);
lean_ctor_set(v___x_997_, 1, v_a_993_);
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_998_);
v___x_1000_ = v___x_995_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v_goal_x27_978_);
v_a_1003_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_992_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_992_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v_goal_x27_978_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_fst_976_);
lean_ctor_set(v___x_1011_, 1, v_snd_977_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_fst_1014_, lean_object* v_snd_1015_, lean_object* v_goal_x27_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg___lam__0(v_fst_1014_, v_snd_1015_, v_goal_x27_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(lean_object* v_a_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___y_1044_; lean_object* v_fst_1064_; lean_object* v_snd_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1099_; 
v_fst_1064_ = lean_ctor_get(v_a_1030_, 0);
v_snd_1065_ = lean_ctor_get(v_a_1030_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_a_1030_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1067_ = v_a_1030_;
v_isShared_1068_ = v_isSharedCheck_1099_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_snd_1065_);
lean_inc(v_fst_1064_);
lean_dec(v_a_1030_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1099_;
goto v_resetjp_1066_;
}
v___jp_1043_:
{
if (lean_obj_tag(v___y_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1055_; 
v_a_1045_ = lean_ctor_get(v___y_1044_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___y_1044_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1047_ = v___y_1044_;
v_isShared_1048_ = v_isSharedCheck_1055_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___y_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1055_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
if (lean_obj_tag(v_a_1045_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; 
v_a_1049_ = lean_ctor_get(v_a_1045_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v_a_1045_, 1);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v_a_1049_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
else
{
lean_object* v_a_1053_; 
lean_del_object(v___x_1047_);
v_a_1053_ = lean_ctor_get(v_a_1045_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v_a_1045_, 1);
v_a_1030_ = v_a_1053_;
goto _start;
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___y_1044_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___y_1044_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___y_1044_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___y_1044_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
v_resetjp_1066_:
{
uint8_t v___x_1069_; 
v___x_1069_ = l_Lean_Expr_isForall(v_snd_1065_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1071_; 
if (v_isShared_1068_ == 0)
{
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_fst_1064_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_snd_1065_);
v___x_1071_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
lean_del_object(v___x_1067_);
v___x_1074_ = l_Lean_Elab_Tactic_VCGen_numBindersToIntro(v_snd_1065_);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_nat_dec_eq(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
lean_inc(v_fst_1064_);
v___x_1077_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_fst_1064_, v___x_1074_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg___lam__0(v_fst_1064_, v_snd_1065_, v_a_1078_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
v___y_1044_ = v___x_1079_;
goto v___jp_1043_;
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v_snd_1065_);
lean_dec(v_fst_1064_);
v_a_1080_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1077_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1077_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_object* v___x_1088_; 
lean_dec(v___x_1074_);
lean_inc(v_snd_1065_);
lean_inc(v_fst_1064_);
v___x_1088_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder(v_fst_1064_, v_snd_1065_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg___lam__0(v_fst_1064_, v_snd_1065_, v_a_1089_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
v___y_1044_ = v___x_1090_;
goto v___jp_1043_;
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_snd_1065_);
lean_dec(v_fst_1064_);
v_a_1091_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1088_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1088_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg___boxed(lean_object* v_a_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v_a_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1_spec__1(lean_object* v_msgData_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v_env_1121_; uint8_t v___x_1122_; lean_object* v_env_1123_; lean_object* v___x_1124_; lean_object* v_toCold_1125_; lean_object* v_mctx_1126_; lean_object* v_lctx_1127_; lean_object* v_options_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1120_ = lean_st_ref_get(v___y_1118_);
v_env_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc_ref(v_env_1121_);
lean_dec(v___x_1120_);
v___x_1122_ = 0;
v_env_1123_ = l_Lean_Environment_setRecordingDeps(v_env_1121_, v___x_1122_);
v___x_1124_ = lean_st_ref_get(v___y_1116_);
v_toCold_1125_ = lean_ctor_get(v___y_1117_, 0);
v_mctx_1126_ = lean_ctor_get(v___x_1124_, 0);
lean_inc_ref(v_mctx_1126_);
lean_dec(v___x_1124_);
v_lctx_1127_ = lean_ctor_get(v___y_1115_, 2);
v_options_1128_ = lean_ctor_get(v_toCold_1125_, 2);
lean_inc_ref(v_options_1128_);
lean_inc_ref(v_lctx_1127_);
v___x_1129_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1129_, 0, v_env_1123_);
lean_ctor_set(v___x_1129_, 1, v_mctx_1126_);
lean_ctor_set(v___x_1129_, 2, v_lctx_1127_);
lean_ctor_set(v___x_1129_, 3, v_options_1128_);
v___x_1130_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
lean_ctor_set(v___x_1130_, 1, v_msgData_1114_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1_spec__1___boxed(lean_object* v_msgData_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1_spec__1(v_msgData_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(lean_object* v_msg_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_ref_1145_; lean_object* v___x_1146_; lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1155_; 
v_ref_1145_ = lean_ctor_get(v___y_1142_, 2);
v___x_1146_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1_spec__1(v_msg_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
lean_inc(v_ref_1145_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_ref_1145_);
lean_ctor_set(v___x_1151_, 1, v_a_1147_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 1);
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg___boxed(lean_object* v_msg_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v_msg_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
return v_res_1162_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__1(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__0));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f(lean_object* v_oldGoal_1168_, lean_object* v_target_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___y_1183_; uint8_t v___x_1188_; 
v___x_1188_ = l_Lean_Expr_isForall(v_target_1169_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec(v_oldGoal_1168_);
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
else
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Elab_Tactic_VCGen_instantiateBinderDomains___redArg(v_oldGoal_1168_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v_goal_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___x_1248_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_n(v_a_1192_, 2);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1248_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_a_1192_, v_a_1170_, v_a_1171_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1258_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
switch(lean_obj_tag(v_a_1249_))
{
case 0:
{
lean_del_object(v___x_1251_);
lean_inc(v_a_1192_);
v_goal_1194_ = v_a_1192_;
v___y_1195_ = v_a_1170_;
v___y_1196_ = v_a_1171_;
v___y_1197_ = v_a_1172_;
v___y_1198_ = v_a_1173_;
v___y_1199_ = v_a_1174_;
v___y_1200_ = v_a_1175_;
v___y_1201_ = v_a_1176_;
v___y_1202_ = v_a_1177_;
v___y_1203_ = v_a_1178_;
v___y_1204_ = v_a_1179_;
v___y_1205_ = v_a_1180_;
goto v___jp_1193_;
}
case 1:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_dec(v_a_1192_);
v___x_1253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2));
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1253_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
default: 
{
lean_object* v_mvarId_1257_; 
lean_del_object(v___x_1251_);
v_mvarId_1257_ = lean_ctor_get(v_a_1249_, 0);
lean_inc(v_mvarId_1257_);
lean_dec_ref_known(v_a_1249_, 1);
v_goal_1194_ = v_mvarId_1257_;
v___y_1195_ = v_a_1170_;
v___y_1196_ = v_a_1171_;
v___y_1197_ = v_a_1172_;
v___y_1198_ = v_a_1173_;
v___y_1199_ = v_a_1174_;
v___y_1200_ = v_a_1175_;
v___y_1201_ = v_a_1176_;
v___y_1202_ = v_a_1177_;
v___y_1203_ = v_a_1178_;
v___y_1204_ = v_a_1179_;
v___y_1205_ = v_a_1180_;
goto v___jp_1193_;
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_a_1192_);
v_a_1259_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1248_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1248_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
v___jp_1193_:
{
lean_object* v___x_1206_; 
lean_inc(v_goal_1194_);
v___x_1206_ = l_Lean_MVarId_getType(v_goal_1194_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_goal_1194_);
lean_ctor_set(v___x_1208_, 1, v_a_1207_);
v___x_1209_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v___x_1208_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v_fst_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1230_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v_fst_1211_ = lean_ctor_get(v_a_1210_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_a_1210_, 1);
lean_dec(v_unused_1231_);
v___x_1213_ = v_a_1210_;
v_isShared_1214_ = v_isSharedCheck_1230_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_fst_1211_);
lean_dec(v_a_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1230_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
uint8_t v___x_1215_; 
v___x_1215_ = l_Lean_instBEqMVarId_beq(v_fst_1211_, v_a_1192_);
lean_dec(v_a_1192_);
if (v___x_1215_ == 0)
{
lean_del_object(v___x_1213_);
v___y_1183_ = v_fst_1211_;
goto v___jp_1182_;
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1216_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__1);
v___x_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1217_, 0, v_fst_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 7);
lean_ctor_set(v___x_1213_, 1, v___x_1217_);
lean_ctor_set(v___x_1213_, 0, v___x_1216_);
v___x_1219_ = v___x_1213_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v___x_1220_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_1219_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_a_1192_);
v_a_1232_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1209_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1209_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_goal_1194_);
lean_dec(v_a_1192_);
v_a_1240_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1206_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1206_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_a_1267_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1191_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1191_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
v___jp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___y_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___boxed(lean_object* v_oldGoal_1275_, lean_object* v_target_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f(v_oldGoal_1275_, v_target_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec_ref(v_target_1276_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0(lean_object* v_inst_1290_, lean_object* v_a_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___redArg(v_a_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0___boxed(lean_object* v_inst_1305_, lean_object* v_a_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__0(v_inst_1305_, v_a_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1(lean_object* v_00_u03b1_1320_, lean_object* v_msg_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v_msg_1321_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___boxed(lean_object* v_00_u03b1_1335_, lean_object* v_msg_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1(v_00_u03b1_1335_, v_msg_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
return v_res_1349_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1350_; double v___x_1351_; 
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_float_of_nat(v___x_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(lean_object* v_cls_1355_, lean_object* v_msg_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_ref_1362_; lean_object* v___x_1363_; lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1409_; 
v_ref_1362_ = lean_ctor_get(v___y_1359_, 2);
v___x_1363_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1_spec__1(v_msg_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1409_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1409_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v_traceState_1369_; lean_object* v_env_1370_; lean_object* v_nextMacroScope_1371_; lean_object* v_ngen_1372_; lean_object* v_auxDeclNGen_1373_; lean_object* v_cache_1374_; lean_object* v_recordedDeps_1375_; lean_object* v_messages_1376_; lean_object* v_infoState_1377_; lean_object* v_snapshotTasks_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1408_; 
v___x_1368_ = lean_st_ref_take(v___y_1360_);
v_traceState_1369_ = lean_ctor_get(v___x_1368_, 4);
v_env_1370_ = lean_ctor_get(v___x_1368_, 0);
v_nextMacroScope_1371_ = lean_ctor_get(v___x_1368_, 1);
v_ngen_1372_ = lean_ctor_get(v___x_1368_, 2);
v_auxDeclNGen_1373_ = lean_ctor_get(v___x_1368_, 3);
v_cache_1374_ = lean_ctor_get(v___x_1368_, 5);
v_recordedDeps_1375_ = lean_ctor_get(v___x_1368_, 6);
v_messages_1376_ = lean_ctor_get(v___x_1368_, 7);
v_infoState_1377_ = lean_ctor_get(v___x_1368_, 8);
v_snapshotTasks_1378_ = lean_ctor_get(v___x_1368_, 9);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1380_ = v___x_1368_;
v_isShared_1381_ = v_isSharedCheck_1408_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_snapshotTasks_1378_);
lean_inc(v_infoState_1377_);
lean_inc(v_messages_1376_);
lean_inc(v_recordedDeps_1375_);
lean_inc(v_cache_1374_);
lean_inc(v_traceState_1369_);
lean_inc(v_auxDeclNGen_1373_);
lean_inc(v_ngen_1372_);
lean_inc(v_nextMacroScope_1371_);
lean_inc(v_env_1370_);
lean_dec(v___x_1368_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1408_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
uint64_t v_tid_1382_; lean_object* v_traces_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1407_; 
v_tid_1382_ = lean_ctor_get_uint64(v_traceState_1369_, sizeof(void*)*1);
v_traces_1383_ = lean_ctor_get(v_traceState_1369_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_traceState_1369_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1385_ = v_traceState_1369_;
v_isShared_1386_ = v_isSharedCheck_1407_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_traces_1383_);
lean_dec(v_traceState_1369_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1407_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; double v___x_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0);
v___x_1390_ = 0;
v___x_1391_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__1));
v___x_1392_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1392_, 0, v_cls_1355_);
lean_ctor_set(v___x_1392_, 1, v___x_1388_);
lean_ctor_set(v___x_1392_, 2, v___x_1391_);
lean_ctor_set_float(v___x_1392_, sizeof(void*)*3, v___x_1389_);
lean_ctor_set_float(v___x_1392_, sizeof(void*)*3 + 8, v___x_1389_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*3 + 16, v___x_1390_);
v___x_1393_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__2));
v___x_1394_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v_a_1364_);
lean_ctor_set(v___x_1394_, 2, v___x_1393_);
lean_inc(v_ref_1362_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v_ref_1362_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___x_1396_ = l_Lean_PersistentArray_push___redArg(v_traces_1383_, v___x_1395_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1396_);
v___x_1398_ = v___x_1385_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1396_);
lean_ctor_set_uint64(v_reuseFailAlloc_1406_, sizeof(void*)*1, v_tid_1382_);
v___x_1398_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1400_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 4, v___x_1398_);
v___x_1400_ = v___x_1380_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_env_1370_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_nextMacroScope_1371_);
lean_ctor_set(v_reuseFailAlloc_1405_, 2, v_ngen_1372_);
lean_ctor_set(v_reuseFailAlloc_1405_, 3, v_auxDeclNGen_1373_);
lean_ctor_set(v_reuseFailAlloc_1405_, 4, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1405_, 5, v_cache_1374_);
lean_ctor_set(v_reuseFailAlloc_1405_, 6, v_recordedDeps_1375_);
lean_ctor_set(v_reuseFailAlloc_1405_, 7, v_messages_1376_);
lean_ctor_set(v_reuseFailAlloc_1405_, 8, v_infoState_1377_);
lean_ctor_set(v_reuseFailAlloc_1405_, 9, v_snapshotTasks_1378_);
v___x_1400_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1401_ = lean_st_ref_put(v___y_1360_, v___x_1400_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1387_);
v___x_1403_ = v___x_1366_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1387_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg___boxed(lean_object* v_cls_1410_, lean_object* v_msg_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_1410_, v_msg_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1417_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7(void){
_start:
{
lean_object* v_cls_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_cls_1430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_1431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__6));
v___x_1432_ = l_Lean_Name_append(v___x_1431_, v_cls_1430_);
return v___x_1432_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__9(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__8));
v___x_1435_ = l_Lean_stringToMessageData(v___x_1434_);
return v___x_1435_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__10));
v___x_1438_ = l_Lean_stringToMessageData(v___x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f(lean_object* v_goal_1439_, lean_object* v_target_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; 
if (lean_obj_tag(v_target_1440_) == 8)
{
lean_object* v_declName_1483_; lean_object* v_value_1484_; lean_object* v_body_1485_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; uint8_t v___x_1524_; 
v_declName_1483_ = lean_ctor_get(v_target_1440_, 0);
lean_inc(v_declName_1483_);
v_value_1484_ = lean_ctor_get(v_target_1440_, 2);
lean_inc_ref(v_value_1484_);
v_body_1485_ = lean_ctor_get(v_target_1440_, 3);
lean_inc_ref(v_body_1485_);
lean_dec_ref_known(v_target_1440_, 4);
v___x_1524_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable(v_value_1484_);
if (v___x_1524_ == 0)
{
lean_object* v_toCold_1525_; lean_object* v_options_1526_; uint8_t v_hasTrace_1527_; 
lean_dec_ref(v_body_1485_);
lean_dec_ref(v_value_1484_);
v_toCold_1525_ = lean_ctor_get(v_a_1450_, 0);
v_options_1526_ = lean_ctor_get(v_toCold_1525_, 2);
v_hasTrace_1527_ = lean_ctor_get_uint8(v_options_1526_, sizeof(void*)*1);
if (v_hasTrace_1527_ == 0)
{
lean_dec(v_declName_1483_);
v___y_1454_ = v_a_1441_;
v___y_1455_ = v_a_1442_;
v___y_1456_ = v_a_1443_;
v___y_1457_ = v_a_1444_;
v___y_1458_ = v_a_1445_;
v___y_1459_ = v_a_1446_;
v___y_1460_ = v_a_1447_;
v___y_1461_ = v_a_1448_;
v___y_1462_ = v_a_1449_;
v___y_1463_ = v_a_1450_;
v___y_1464_ = v_a_1451_;
goto v___jp_1453_;
}
else
{
lean_object* v_inheritedTraceOptions_1528_; lean_object* v_cls_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v_inheritedTraceOptions_1528_ = lean_ctor_get(v_toCold_1525_, 11);
v_cls_1529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_1530_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_1531_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1528_, v_options_1526_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_dec(v_declName_1483_);
v___y_1454_ = v_a_1441_;
v___y_1455_ = v_a_1442_;
v___y_1456_ = v_a_1443_;
v___y_1457_ = v_a_1444_;
v___y_1458_ = v_a_1445_;
v___y_1459_ = v_a_1446_;
v___y_1460_ = v_a_1447_;
v___y_1461_ = v_a_1448_;
v___y_1462_ = v_a_1449_;
v___y_1463_ = v_a_1450_;
v___y_1464_ = v_a_1451_;
goto v___jp_1453_;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1532_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__9, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__9);
v___x_1533_ = l_Lean_MessageData_ofName(v_declName_1483_);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_1529_, v___x_1534_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_dec_ref_known(v___x_1535_, 1);
v___y_1454_ = v_a_1441_;
v___y_1455_ = v_a_1442_;
v___y_1456_ = v_a_1443_;
v___y_1457_ = v_a_1444_;
v___y_1458_ = v_a_1445_;
v___y_1459_ = v_a_1446_;
v___y_1460_ = v_a_1447_;
v___y_1461_ = v_a_1448_;
v___y_1462_ = v_a_1449_;
v___y_1463_ = v_a_1450_;
v___y_1464_ = v_a_1451_;
goto v___jp_1453_;
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec(v_goal_1439_);
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
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
}
else
{
lean_object* v_toCold_1544_; lean_object* v_options_1545_; uint8_t v_hasTrace_1546_; 
v_toCold_1544_ = lean_ctor_get(v_a_1450_, 0);
v_options_1545_ = lean_ctor_get(v_toCold_1544_, 2);
v_hasTrace_1546_ = lean_ctor_get_uint8(v_options_1545_, sizeof(void*)*1);
if (v_hasTrace_1546_ == 0)
{
lean_dec(v_declName_1483_);
v___y_1487_ = v_a_1446_;
v___y_1488_ = v_a_1447_;
v___y_1489_ = v_a_1448_;
v___y_1490_ = v_a_1449_;
v___y_1491_ = v_a_1450_;
v___y_1492_ = v_a_1451_;
goto v___jp_1486_;
}
else
{
lean_object* v_inheritedTraceOptions_1547_; lean_object* v_cls_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_inheritedTraceOptions_1547_ = lean_ctor_get(v_toCold_1544_, 11);
v_cls_1548_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_1549_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_1550_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1547_, v_options_1545_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_dec(v_declName_1483_);
v___y_1487_ = v_a_1446_;
v___y_1488_ = v_a_1447_;
v___y_1489_ = v_a_1448_;
v___y_1490_ = v_a_1449_;
v___y_1491_ = v_a_1450_;
v___y_1492_ = v_a_1451_;
goto v___jp_1486_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1551_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11);
v___x_1552_ = l_Lean_MessageData_ofName(v_declName_1483_);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_1548_, v___x_1553_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_dec_ref_known(v___x_1554_, 1);
v___y_1487_ = v_a_1446_;
v___y_1488_ = v_a_1447_;
v___y_1489_ = v_a_1448_;
v___y_1490_ = v_a_1449_;
v___y_1491_ = v_a_1450_;
v___y_1492_ = v_a_1451_;
goto v___jp_1486_;
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v_body_1485_);
lean_dec_ref(v_value_1484_);
lean_dec(v_goal_1439_);
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1554_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1554_);
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
}
}
v___jp_1486_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1493_ = lean_unsigned_to_nat(1u);
v___x_1494_ = lean_mk_empty_array_with_capacity(v___x_1493_);
v___x_1495_ = lean_array_push(v___x_1494_, v_value_1484_);
v___x_1496_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_1485_, v___x_1495_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_1439_, v_a_1497_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1507_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1503_, 0, v_a_1499_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1503_);
v___x_1505_ = v___x_1501_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
v_a_1508_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1498_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1498_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec(v_goal_1439_);
v_a_1516_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1496_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1496_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v_target_1440_);
lean_dec(v_goal_1439_);
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
v___jp_1453_:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_Elab_Tactic_VCGen_introsHygienic(v_goal_1439_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1474_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1470_, 0, v_a_1466_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
v_a_1475_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1465_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1465_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___boxed(lean_object* v_goal_1565_, lean_object* v_target_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f(v_goal_1565_, v_target_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0(lean_object* v_cls_1580_, lean_object* v_msg_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_1580_, v_msg_1581_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___boxed(lean_object* v_cls_1595_, lean_object* v_msg_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0(v_cls_1595_, v_msg_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f(lean_object* v_goal_1617_, lean_object* v_target_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___closed__3));
v___x_1632_ = l_Lean_Expr_isAppOf(v_target_1618_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec(v_goal_1617_);
v___x_1633_ = lean_box(0);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Elab_Tactic_VCGen_unfoldTriple(v_goal_1617_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1644_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_a_1636_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1640_);
v___x_1642_ = v___x_1638_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1635_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1635_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f___boxed(lean_object* v_goal_1653_, lean_object* v_target_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f(v_goal_1653_, v_target_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec_ref(v_target_1654_);
return v_res_1667_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = l_Lean_Level_ofNat(v___x_1675_);
return v___x_1676_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__5(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__4, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__4);
v___x_1678_ = l_Lean_mkSort(v___x_1677_);
return v___x_1678_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__6(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__5);
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__7(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1681_ = lean_box(0);
v___x_1682_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__6, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__6);
v___x_1683_ = lean_unsigned_to_nat(2u);
v___x_1684_ = lean_mk_empty_array_with_capacity(v___x_1683_);
v___x_1685_ = lean_array_push(v___x_1684_, v___x_1682_);
v___x_1686_ = lean_array_push(v___x_1685_, v___x_1681_);
return v___x_1686_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__13(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = lean_box(0);
v___x_1700_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__12));
v___x_1701_ = l_Lean_mkConst(v___x_1700_, v___x_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg(lean_object* v_goal_1702_, lean_object* v_target_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___x_1711_; 
lean_inc_ref(v_target_1703_);
v___x_1711_ = l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(v_target_1703_);
if (lean_obj_tag(v___x_1711_) == 1)
{
lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1778_; 
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v___x_1711_, 0);
lean_dec(v_unused_1779_);
v___x_1713_ = v___x_1711_;
v_isShared_1714_ = v_isSharedCheck_1778_;
goto v_resetjp_1712_;
}
else
{
lean_dec(v___x_1711_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1778_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1715_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__3));
v___x_1716_ = lean_unsigned_to_nat(2u);
v___x_1717_ = lean_mk_empty_array_with_capacity(v___x_1716_);
v___x_1718_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__7);
v___x_1719_ = l_Lean_Meta_mkAppOptM(v___x_1715_, v___x_1718_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10));
v___x_1722_ = lean_array_push(v___x_1717_, v_a_1720_);
lean_inc_ref(v_target_1703_);
v___x_1723_ = lean_array_push(v___x_1722_, v_target_1703_);
v___x_1724_ = l_Lean_Meta_mkAppM(v___x_1721_, v___x_1723_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = l_Lean_Meta_Sym_shareCommon(v_a_1725_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = lean_box(0);
v___x_1729_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1727_, v___x_1728_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1744_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc_n(v_a_1730_, 2);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__13, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__13_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__13);
v___x_1732_ = l_Lean_mkAppB(v___x_1731_, v_target_1703_, v_a_1730_);
v___x_1733_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg(v_goal_1702_, v___x_1732_, v_a_1707_);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v___x_1733_, 0);
lean_dec(v_unused_1745_);
v___x_1735_ = v___x_1733_;
v_isShared_1736_ = v_isSharedCheck_1744_;
goto v_resetjp_1734_;
}
else
{
lean_dec(v___x_1733_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1744_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1737_ = l_Lean_Expr_mvarId_x21(v_a_1730_);
lean_dec(v_a_1730_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1737_);
v___x_1739_ = v___x_1713_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1741_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1739_);
v___x_1741_ = v___x_1735_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_del_object(v___x_1713_);
lean_dec_ref(v_target_1703_);
lean_dec(v_goal_1702_);
v_a_1746_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1729_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1729_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_del_object(v___x_1713_);
lean_dec_ref(v_target_1703_);
lean_dec(v_goal_1702_);
v_a_1754_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1726_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1726_);
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
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_del_object(v___x_1713_);
lean_dec_ref(v_target_1703_);
lean_dec(v_goal_1702_);
v_a_1762_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1724_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1724_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v___x_1717_);
lean_del_object(v___x_1713_);
lean_dec_ref(v_target_1703_);
lean_dec(v_goal_1702_);
v_a_1770_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1719_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1719_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec(v___x_1711_);
lean_dec_ref(v_target_1703_);
lean_dec(v_goal_1702_);
v___x_1780_ = lean_box(0);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___boxed(lean_object* v_goal_1782_, lean_object* v_target_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg(v_goal_1782_, v_target_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f(lean_object* v_goal_1792_, lean_object* v_target_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg(v_goal_1792_, v_target_1793_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___boxed(lean_object* v_goal_1807_, lean_object* v_target_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f(v_goal_1807_, v_target_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
return v_res_1821_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__0));
v___x_1824_ = l_Lean_stringToMessageData(v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(lean_object* v_goal_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_backwardRules_1834_; lean_object* v_refl_1835_; lean_object* v___x_1836_; 
v_backwardRules_1834_ = lean_ctor_get(v_a_1826_, 0);
v_refl_1835_ = lean_ctor_get(v_backwardRules_1834_, 9);
lean_inc_ref(v_refl_1835_);
lean_inc(v_goal_1825_);
v___x_1836_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1825_, v_refl_1835_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1876_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1876_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1876_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
if (lean_obj_tag(v_a_1837_) == 1)
{
lean_object* v_mvarIds_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1871_; 
v_mvarIds_1841_ = lean_ctor_get(v_a_1837_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_a_1837_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1843_ = v_a_1837_;
v_isShared_1844_ = v_isSharedCheck_1871_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_mvarIds_1841_);
lean_dec(v_a_1837_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1871_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_toCold_1852_; lean_object* v_options_1853_; uint8_t v_hasTrace_1854_; 
v_toCold_1852_ = lean_ctor_get(v_a_1831_, 0);
v_options_1853_ = lean_ctor_get(v_toCold_1852_, 2);
v_hasTrace_1854_ = lean_ctor_get_uint8(v_options_1853_, sizeof(void*)*1);
if (v_hasTrace_1854_ == 0)
{
lean_dec(v_goal_1825_);
goto v___jp_1845_;
}
else
{
lean_object* v_inheritedTraceOptions_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v_inheritedTraceOptions_1855_ = lean_ctor_get(v_toCold_1852_, 11);
v___x_1856_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_1857_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_1858_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1855_, v_options_1853_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_dec(v_goal_1825_);
goto v___jp_1845_;
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1859_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___closed__1);
v___x_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_goal_1825_);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1856_, v___x_1861_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_dec_ref_known(v___x_1862_, 1);
goto v___jp_1845_;
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_del_object(v___x_1843_);
lean_dec(v_mvarIds_1841_);
lean_del_object(v___x_1839_);
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
}
v___jp_1845_:
{
lean_object* v___x_1847_; 
if (v_isShared_1844_ == 0)
{
v___x_1847_ = v___x_1843_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_mvarIds_1841_);
v___x_1847_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1847_);
v___x_1849_ = v___x_1839_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_dec(v_a_1837_);
lean_dec(v_goal_1825_);
v___x_1872_ = lean_box(0);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1872_);
v___x_1874_ = v___x_1839_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v_goal_1825_);
v_a_1877_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1836_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1836_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg___boxed(lean_object* v_goal_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(v_goal_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec_ref(v_a_1886_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f(lean_object* v_goal_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(v_goal_1895_, v_a_1896_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___boxed(lean_object* v_goal_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f(v_goal_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
return v_res_1922_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__0));
v___x_1925_ = l_Lean_stringToMessageData(v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(lean_object* v_scope_1926_, lean_object* v_e_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v_lastLiftedPre_x3f_1933_; 
v_lastLiftedPre_x3f_1933_ = lean_ctor_get(v_scope_1926_, 1);
lean_inc(v_lastLiftedPre_x3f_1933_);
lean_dec_ref(v_scope_1926_);
if (lean_obj_tag(v_lastLiftedPre_x3f_1933_) == 1)
{
lean_object* v_val_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1992_; 
v_val_1934_ = lean_ctor_get(v_lastLiftedPre_x3f_1933_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_lastLiftedPre_x3f_1933_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1936_ = v_lastLiftedPre_x3f_1933_;
v_isShared_1937_ = v_isSharedCheck_1992_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_val_1934_);
lean_dec(v_lastLiftedPre_x3f_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1992_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v_lctx_1938_; lean_object* v___x_1939_; 
v_lctx_1938_ = lean_ctor_get(v_a_1928_, 2);
lean_inc_ref(v_lctx_1938_);
v___x_1939_ = lean_local_ctx_find(v_lctx_1938_, v_val_1934_);
if (lean_obj_tag(v___x_1939_) == 1)
{
lean_object* v_val_1940_; lean_object* v___x_1941_; size_t v___x_1942_; size_t v___x_1943_; uint8_t v___x_1944_; 
v_val_1940_ = lean_ctor_get(v___x_1939_, 0);
v___x_1941_ = l_Lean_LocalDecl_type(v_val_1940_);
v___x_1942_ = lean_ptr_addr(v_e_1927_);
v___x_1943_ = lean_ptr_addr(v___x_1941_);
lean_dec_ref(v___x_1941_);
v___x_1944_ = lean_usize_dec_eq(v___x_1942_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1952_; 
lean_del_object(v___x_1936_);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; 
v_unused_1953_ = lean_ctor_get(v___x_1939_, 0);
lean_dec(v_unused_1953_);
v___x_1946_ = v___x_1939_;
v_isShared_1947_ = v_isSharedCheck_1952_;
goto v_resetjp_1945_;
}
else
{
lean_dec(v___x_1939_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1952_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1948_ = lean_box(0);
if (v_isShared_1947_ == 0)
{
lean_ctor_set_tag(v___x_1946_, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1948_);
v___x_1950_ = v___x_1946_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
else
{
lean_object* v_toCold_1954_; lean_object* v_options_1955_; uint8_t v_hasTrace_1956_; 
v_toCold_1954_ = lean_ctor_get(v_a_1930_, 0);
v_options_1955_ = lean_ctor_get(v_toCold_1954_, 2);
v_hasTrace_1956_ = lean_ctor_get_uint8(v_options_1955_, sizeof(void*)*1);
if (v_hasTrace_1956_ == 0)
{
lean_object* v___x_1958_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1939_);
v___x_1958_ = v___x_1936_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1939_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
else
{
lean_object* v_inheritedTraceOptions_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v_inheritedTraceOptions_1960_ = lean_ctor_get(v_toCold_1954_, 11);
v___x_1961_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_1962_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_1963_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1960_, v_options_1955_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1965_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1939_);
v___x_1965_ = v___x_1936_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1939_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_del_object(v___x_1936_);
v___x_1967_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___closed__1);
v___x_1968_ = l_Lean_LocalDecl_userName(v_val_1940_);
v___x_1969_ = l_Lean_MessageData_ofName(v___x_1968_);
v___x_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1967_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1961_, v___x_1970_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v___x_1971_, 0);
lean_dec(v_unused_1979_);
v___x_1973_ = v___x_1971_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_dec(v___x_1971_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1939_);
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1939_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref_known(v___x_1939_, 1);
v_a_1980_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1971_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1971_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_dec(v___x_1939_);
v___x_1988_ = lean_box(0);
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1988_);
v___x_1990_ = v___x_1936_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_dec(v_lastLiftedPre_x3f_1933_);
v___x_1993_ = lean_box(0);
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg___boxed(lean_object* v_scope_1995_, lean_object* v_e_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_1995_, v_e_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec_ref(v_e_1996_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f(lean_object* v_scope_2003_, lean_object* v_e_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_2003_, v_e_2004_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___boxed(lean_object* v_scope_2018_, lean_object* v_e_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f(v_scope_2018_, v_e_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec_ref(v_e_2019_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0(uint8_t v___x_2038_, lean_object* v_scope_2039_, lean_object* v_rhs_2040_, lean_object* v_pre_2041_, lean_object* v_goal_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
if (v___x_2038_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec(v_goal_2042_);
lean_dec_ref(v_pre_2041_);
lean_dec_ref(v_rhs_2040_);
lean_dec_ref(v_scope_2039_);
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
else
{
lean_object* v___x_2057_; 
v___x_2057_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_2039_, v_rhs_2040_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2094_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2094_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2094_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
if (lean_obj_tag(v_a_2058_) == 1)
{
lean_object* v_val_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_del_object(v___x_2060_);
v_val_2062_ = lean_ctor_get(v_a_2058_, 0);
lean_inc(v_val_2062_);
lean_dec_ref_known(v_a_2058_, 1);
v___x_2063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___closed__1));
v___x_2064_ = l_Lean_LocalDecl_toExpr(v_val_2062_);
v___x_2065_ = lean_unsigned_to_nat(3u);
v___x_2066_ = lean_mk_empty_array_with_capacity(v___x_2065_);
v___x_2067_ = lean_array_push(v___x_2066_, v_pre_2041_);
v___x_2068_ = lean_array_push(v___x_2067_, v_rhs_2040_);
v___x_2069_ = lean_array_push(v___x_2068_, v___x_2064_);
v___x_2070_ = l_Lean_Meta_mkAppM(v___x_2063_, v___x_2069_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2080_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v___x_2072_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg(v_goal_2042_, v_a_2071_, v___y_2051_);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; 
v_unused_2081_ = lean_ctor_get(v___x_2072_, 0);
lean_dec(v_unused_2081_);
v___x_2074_ = v___x_2072_;
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
else
{
lean_dec(v___x_2072_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2));
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_goal_2042_);
v_a_2082_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2070_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2070_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
lean_dec(v_a_2058_);
lean_dec(v_goal_2042_);
lean_dec_ref(v_pre_2041_);
lean_dec_ref(v_rhs_2040_);
v___x_2090_ = lean_box(0);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2090_);
v___x_2092_ = v___x_2060_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_goal_2042_);
lean_dec_ref(v_pre_2041_);
lean_dec_ref(v_rhs_2040_);
v_a_2095_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2057_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2057_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___boxed(lean_object** _args){
lean_object* v___x_2103_ = _args[0];
lean_object* v_scope_2104_ = _args[1];
lean_object* v_rhs_2105_ = _args[2];
lean_object* v_pre_2106_ = _args[3];
lean_object* v_goal_2107_ = _args[4];
lean_object* v___y_2108_ = _args[5];
lean_object* v___y_2109_ = _args[6];
lean_object* v___y_2110_ = _args[7];
lean_object* v___y_2111_ = _args[8];
lean_object* v___y_2112_ = _args[9];
lean_object* v___y_2113_ = _args[10];
lean_object* v___y_2114_ = _args[11];
lean_object* v___y_2115_ = _args[12];
lean_object* v___y_2116_ = _args[13];
lean_object* v___y_2117_ = _args[14];
lean_object* v___y_2118_ = _args[15];
lean_object* v___y_2119_ = _args[16];
_start:
{
uint8_t v___x_4206__boxed_2120_; lean_object* v_res_2121_; 
v___x_4206__boxed_2120_ = lean_unbox(v___x_2103_);
v_res_2121_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0(v___x_4206__boxed_2120_, v_scope_2104_, v_rhs_2105_, v_pre_2106_, v_goal_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f(lean_object* v_scope_2122_, lean_object* v_goal_2123_, lean_object* v_00_u03b1_2124_, lean_object* v_pre_2125_, lean_object* v_rhs_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___y_2141_; lean_object* v___x_2142_; 
v___x_2139_ = l_Lean_Expr_isProp(v_00_u03b1_2124_);
v___x_2140_ = lean_box(v___x_2139_);
lean_inc(v_goal_2123_);
v___y_2141_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___lam__0___boxed), 17, 5);
lean_closure_set(v___y_2141_, 0, v___x_2140_);
lean_closure_set(v___y_2141_, 1, v_scope_2122_);
lean_closure_set(v___y_2141_, 2, v_rhs_2126_);
lean_closure_set(v___y_2141_, 3, v_pre_2125_);
lean_closure_set(v___y_2141_, 4, v_goal_2123_);
v___x_2142_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg(v_goal_2123_, v___y_2141_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f___boxed(lean_object** _args){
lean_object* v_scope_2143_ = _args[0];
lean_object* v_goal_2144_ = _args[1];
lean_object* v_00_u03b1_2145_ = _args[2];
lean_object* v_pre_2146_ = _args[3];
lean_object* v_rhs_2147_ = _args[4];
lean_object* v_a_2148_ = _args[5];
lean_object* v_a_2149_ = _args[6];
lean_object* v_a_2150_ = _args[7];
lean_object* v_a_2151_ = _args[8];
lean_object* v_a_2152_ = _args[9];
lean_object* v_a_2153_ = _args[10];
lean_object* v_a_2154_ = _args[11];
lean_object* v_a_2155_ = _args[12];
lean_object* v_a_2156_ = _args[13];
lean_object* v_a_2157_ = _args[14];
lean_object* v_a_2158_ = _args[15];
lean_object* v_a_2159_ = _args[16];
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f(v_scope_2143_, v_goal_2144_, v_00_u03b1_2145_, v_pre_2146_, v_rhs_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec_ref(v_00_u03b1_2145_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0(lean_object* v_scope_2161_, lean_object* v_target_2162_, lean_object* v_goal_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedPreFor_x3f___redArg(v_scope_2161_, v_target_2162_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2197_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2197_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2197_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
if (lean_obj_tag(v_a_2177_) == 1)
{
lean_object* v_val_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2191_; 
lean_del_object(v___x_2179_);
v_val_2181_ = lean_ctor_get(v_a_2177_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v_a_2177_, 1);
v___x_2182_ = l_Lean_LocalDecl_toExpr(v_val_2181_);
v___x_2183_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg(v_goal_2163_, v___x_2182_, v___y_2172_);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; 
v_unused_2192_ = lean_ctor_get(v___x_2183_, 0);
lean_dec(v_unused_2192_);
v___x_2185_ = v___x_2183_;
v_isShared_2186_ = v_isSharedCheck_2191_;
goto v_resetjp_2184_;
}
else
{
lean_dec(v___x_2183_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2191_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2));
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2187_);
v___x_2189_ = v___x_2185_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
lean_dec(v_a_2177_);
lean_dec(v_goal_2163_);
v___x_2193_ = lean_box(0);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2193_);
v___x_2195_ = v___x_2179_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_goal_2163_);
v_a_2198_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2176_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2176_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0___boxed(lean_object* v_scope_2206_, lean_object* v_target_2207_, lean_object* v_goal_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0(v_scope_2206_, v_target_2207_, v_goal_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec_ref(v_target_2207_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f(lean_object* v_scope_2222_, lean_object* v_goal_2223_, lean_object* v_target_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v___f_2237_; lean_object* v___x_2238_; 
lean_inc(v_goal_2223_);
v___f_2237_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___lam__0___boxed), 15, 3);
lean_closure_set(v___f_2237_, 0, v_scope_2222_);
lean_closure_set(v___f_2237_, 1, v_target_2224_);
lean_closure_set(v___f_2237_, 2, v_goal_2223_);
v___x_2238_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg(v_goal_2223_, v___f_2237_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f___boxed(lean_object* v_scope_2239_, lean_object* v_goal_2240_, lean_object* v_target_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f(v_scope_2239_, v_goal_2240_, v_target_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
lean_dec(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(lean_object* v_e_2255_, lean_object* v_i_2256_, lean_object* v_n_2257_, lean_object* v_v_2258_){
_start:
{
if (lean_obj_tag(v_e_2255_) == 5)
{
lean_object* v_fn_2259_; lean_object* v_arg_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_fn_2259_ = lean_ctor_get(v_e_2255_, 0);
v_arg_2260_ = lean_ctor_get(v_e_2255_, 1);
v___x_2261_ = lean_unsigned_to_nat(1u);
v___x_2262_ = lean_nat_add(v_i_2256_, v___x_2261_);
v___x_2263_ = lean_nat_dec_eq(v_n_2257_, v___x_2262_);
lean_dec(v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; uint8_t v___x_2268_; 
v___x_2264_ = lean_nat_sub(v_n_2257_, v___x_2261_);
lean_inc_ref(v_fn_2259_);
v___x_2265_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(v_fn_2259_, v_i_2256_, v___x_2264_, v_v_2258_);
lean_dec(v___x_2264_);
v___x_2266_ = lean_ptr_addr(v_fn_2259_);
v___x_2267_ = lean_ptr_addr(v___x_2265_);
v___x_2268_ = lean_usize_dec_eq(v___x_2266_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; 
lean_inc_ref(v_arg_2260_);
lean_dec_ref_known(v_e_2255_, 2);
v___x_2269_ = l_Lean_Expr_app___override(v___x_2265_, v_arg_2260_);
return v___x_2269_;
}
else
{
size_t v___x_2270_; size_t v___x_2271_; uint8_t v___x_2272_; 
v___x_2270_ = lean_ptr_addr(v_arg_2260_);
v___x_2271_ = lean_ptr_addr(v_arg_2260_);
v___x_2272_ = lean_usize_dec_eq(v___x_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; 
lean_inc_ref(v_arg_2260_);
lean_dec_ref_known(v_e_2255_, 2);
v___x_2273_ = l_Lean_Expr_app___override(v___x_2265_, v_arg_2260_);
return v___x_2273_;
}
else
{
lean_dec_ref(v___x_2265_);
return v_e_2255_;
}
}
}
else
{
size_t v___x_2274_; size_t v___x_2275_; uint8_t v___x_2276_; 
v___x_2274_ = lean_ptr_addr(v_fn_2259_);
v___x_2275_ = lean_ptr_addr(v_fn_2259_);
v___x_2276_ = lean_usize_dec_eq(v___x_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; 
lean_inc_ref(v_fn_2259_);
lean_dec_ref_known(v_e_2255_, 2);
v___x_2277_ = l_Lean_Expr_app___override(v_fn_2259_, v_v_2258_);
return v___x_2277_;
}
else
{
size_t v___x_2278_; size_t v___x_2279_; uint8_t v___x_2280_; 
v___x_2278_ = lean_ptr_addr(v_arg_2260_);
v___x_2279_ = lean_ptr_addr(v_v_2258_);
v___x_2280_ = lean_usize_dec_eq(v___x_2278_, v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; 
lean_inc_ref(v_fn_2259_);
lean_dec_ref_known(v_e_2255_, 2);
v___x_2281_ = l_Lean_Expr_app___override(v_fn_2259_, v_v_2258_);
return v___x_2281_;
}
else
{
lean_dec_ref(v_v_2258_);
return v_e_2255_;
}
}
}
}
else
{
lean_dec_ref(v_v_2258_);
return v_e_2255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg___boxed(lean_object* v_e_2282_, lean_object* v_i_2283_, lean_object* v_n_2284_, lean_object* v_v_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(v_e_2282_, v_i_2283_, v_n_2284_, v_v_2285_);
lean_dec(v_n_2284_);
lean_dec(v_i_2283_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(lean_object* v_rhs_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
uint8_t v___x_2303_; 
v___x_2303_ = l_Lean_Expr_hasMVar(v_rhs_2292_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_dec_ref(v_rhs_2292_);
v___x_2304_ = lean_box(0);
v___x_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
return v___x_2305_;
}
else
{
lean_object* v_n_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_n_2306_ = l_Lean_Expr_getAppNumArgs(v_rhs_2292_);
v___x_2307_ = lean_unsigned_to_nat(7u);
v___x_2308_ = lean_nat_dec_lt(v___x_2307_, v_n_2306_);
if (v___x_2308_ == 0)
{
lean_dec(v_n_2306_);
lean_dec_ref(v_rhs_2292_);
goto v___jp_2300_;
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2309_ = l_Lean_Expr_getAppFn(v_rhs_2292_);
v___x_2310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___closed__1));
v___x_2311_ = l_Lean_Expr_isConstOf(v___x_2309_, v___x_2310_);
lean_dec_ref(v___x_2309_);
if (v___x_2311_ == 0)
{
lean_dec(v_n_2306_);
lean_dec_ref(v_rhs_2292_);
goto v___jp_2300_;
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v_prog_2315_; lean_object* v___x_2316_; 
v___x_2312_ = lean_nat_sub(v_n_2306_, v___x_2307_);
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = lean_nat_sub(v___x_2312_, v___x_2313_);
lean_dec(v___x_2312_);
v_prog_2315_ = l_Lean_Expr_getRevArg_x21(v_rhs_2292_, v___x_2314_);
lean_inc_ref(v_prog_2315_);
v___x_2316_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_prog_2315_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2347_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2347_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2347_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
size_t v___x_2321_; size_t v___x_2322_; uint8_t v___x_2323_; 
v___x_2321_ = lean_ptr_addr(v_prog_2315_);
lean_dec_ref(v_prog_2315_);
v___x_2322_ = lean_ptr_addr(v_a_2317_);
v___x_2323_ = lean_usize_dec_eq(v___x_2321_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_del_object(v___x_2319_);
v___x_2324_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_setAppArg(v_rhs_2292_, v___x_2307_, v_n_2306_, v_a_2317_);
lean_dec(v_n_2306_);
v___x_2325_ = l_Lean_Meta_Sym_shareCommon(v___x_2324_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2330_, 0, v_a_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2330_);
v___x_2332_ = v___x_2328_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
v_a_2335_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2325_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2325_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2345_; 
lean_dec(v_a_2317_);
lean_dec(v_n_2306_);
lean_dec_ref(v_rhs_2292_);
v___x_2343_ = lean_box(0);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2343_);
v___x_2345_ = v___x_2319_;
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
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec_ref(v_prog_2315_);
lean_dec(v_n_2306_);
lean_dec_ref(v_rhs_2292_);
v_a_2348_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2316_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2316_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
}
v___jp_2300_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = lean_box(0);
v___x_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg___boxed(lean_object* v_rhs_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_rhs_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f(lean_object* v_rhs_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_rhs_2365_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___boxed(lean_object* v_rhs_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f(v_rhs_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(lean_object* v_goal_2393_, lean_object* v_target_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = l_Lean_Expr_cleanupAnnotations(v_target_2394_);
v___x_2411_ = l_Lean_Expr_isApp(v___x_2410_);
if (v___x_2411_ == 0)
{
lean_dec_ref(v___x_2410_);
lean_dec(v_goal_2393_);
goto v___jp_2407_;
}
else
{
lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2410_);
v___x_2413_ = l_Lean_Expr_isApp(v___x_2412_);
if (v___x_2413_ == 0)
{
lean_dec_ref(v___x_2412_);
lean_dec_ref(v___x_2410_);
lean_dec(v_goal_2393_);
goto v___jp_2407_;
}
else
{
lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2412_);
v___x_2415_ = l_Lean_Expr_isApp(v___x_2414_);
if (v___x_2415_ == 0)
{
lean_dec_ref(v___x_2414_);
lean_dec_ref(v___x_2412_);
lean_dec_ref(v___x_2410_);
lean_dec(v_goal_2393_);
goto v___jp_2407_;
}
else
{
lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2414_);
v___x_2417_ = l_Lean_Expr_isApp(v___x_2416_);
if (v___x_2417_ == 0)
{
lean_dec_ref(v___x_2416_);
lean_dec_ref(v___x_2414_);
lean_dec_ref(v___x_2412_);
lean_dec_ref(v___x_2410_);
lean_dec(v_goal_2393_);
goto v___jp_2407_;
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2416_);
v___x_2419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10));
v___x_2420_ = l_Lean_Expr_isConstOf(v___x_2418_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_dec_ref(v___x_2418_);
lean_dec_ref(v___x_2416_);
lean_dec_ref(v___x_2414_);
lean_dec_ref(v___x_2412_);
lean_dec_ref(v___x_2410_);
lean_dec(v_goal_2393_);
goto v___jp_2407_;
}
else
{
lean_object* v_arg_2421_; lean_object* v_arg_2422_; lean_object* v_arg_2423_; lean_object* v_arg_2424_; lean_object* v___x_2425_; 
v_arg_2421_ = lean_ctor_get(v___x_2410_, 1);
lean_inc_ref(v_arg_2421_);
lean_dec_ref(v___x_2410_);
v_arg_2422_ = lean_ctor_get(v___x_2412_, 1);
lean_inc_ref(v_arg_2422_);
lean_dec_ref(v___x_2412_);
v_arg_2423_ = lean_ctor_get(v___x_2414_, 1);
lean_inc_ref(v_arg_2423_);
lean_dec_ref(v___x_2414_);
v_arg_2424_ = lean_ctor_get(v___x_2416_, 1);
lean_inc_ref_n(v_arg_2424_, 2);
lean_dec_ref(v___x_2416_);
v___x_2425_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v_arg_2424_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2427_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
lean_inc_ref(v_arg_2422_);
v___x_2427_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v_arg_2422_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2429_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
lean_inc_ref(v_arg_2421_);
v___x_2429_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v_arg_2421_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2431_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc_n(v_a_2430_, 2);
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateWPProg_x3f___redArg(v_a_2430_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2488_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2488_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2488_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___y_2437_; lean_object* v___y_2473_; 
if (lean_obj_tag(v_a_2432_) == 0)
{
v___y_2473_ = v_a_2430_;
goto v___jp_2472_;
}
else
{
lean_object* v_val_2487_; 
lean_dec(v_a_2430_);
v_val_2487_ = lean_ctor_get(v_a_2432_, 0);
lean_inc(v_val_2487_);
lean_dec_ref_known(v_a_2432_, 1);
v___y_2473_ = v_val_2487_;
goto v___jp_2472_;
}
v___jp_2436_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2438_ = lean_unsigned_to_nat(4u);
v___x_2439_ = lean_mk_empty_array_with_capacity(v___x_2438_);
v___x_2440_ = lean_array_push(v___x_2439_, v_a_2426_);
v___x_2441_ = lean_array_push(v___x_2440_, v_arg_2423_);
v___x_2442_ = lean_array_push(v___x_2441_, v_a_2428_);
v___x_2443_ = lean_array_push(v___x_2442_, v___y_2437_);
v___x_2444_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(v___x_2418_, v___x_2443_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
lean_dec_ref(v___x_2443_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2446_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
lean_dec_ref_known(v___x_2444_, 1);
v___x_2446_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2393_, v_a_2445_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2455_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2449_ = v___x_2446_;
v_isShared_2450_ = v_isSharedCheck_2455_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2455_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2451_, 0, v_a_2447_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2451_);
v___x_2453_ = v___x_2449_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
v_a_2456_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2446_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2446_);
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
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_goal_2393_);
v_a_2464_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2444_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2444_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
v___jp_2472_:
{
size_t v___x_2474_; size_t v___x_2475_; uint8_t v___x_2476_; 
v___x_2474_ = lean_ptr_addr(v_arg_2424_);
lean_dec_ref(v_arg_2424_);
v___x_2475_ = lean_ptr_addr(v_a_2426_);
v___x_2476_ = lean_usize_dec_eq(v___x_2474_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_del_object(v___x_2434_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_arg_2421_);
v___y_2437_ = v___y_2473_;
goto v___jp_2436_;
}
else
{
size_t v___x_2477_; size_t v___x_2478_; uint8_t v___x_2479_; 
v___x_2477_ = lean_ptr_addr(v_arg_2422_);
lean_dec_ref(v_arg_2422_);
v___x_2478_ = lean_ptr_addr(v_a_2428_);
v___x_2479_ = lean_usize_dec_eq(v___x_2477_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_del_object(v___x_2434_);
lean_dec_ref(v_arg_2421_);
v___y_2437_ = v___y_2473_;
goto v___jp_2436_;
}
else
{
size_t v___x_2480_; size_t v___x_2481_; uint8_t v___x_2482_; 
v___x_2480_ = lean_ptr_addr(v_arg_2421_);
lean_dec_ref(v_arg_2421_);
v___x_2481_ = lean_ptr_addr(v___y_2473_);
v___x_2482_ = lean_usize_dec_eq(v___x_2480_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_del_object(v___x_2434_);
v___y_2437_ = v___y_2473_;
goto v___jp_2436_;
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2485_; 
lean_dec_ref(v___y_2473_);
lean_dec(v_a_2428_);
lean_dec(v_a_2426_);
lean_dec_ref(v_arg_2423_);
lean_dec_ref(v___x_2418_);
lean_dec(v_goal_2393_);
v___x_2483_ = lean_box(0);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2483_);
v___x_2485_ = v___x_2434_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2483_);
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
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec(v_a_2430_);
lean_dec(v_a_2428_);
lean_dec(v_a_2426_);
lean_dec_ref(v_arg_2424_);
lean_dec_ref(v_arg_2423_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_arg_2421_);
lean_dec_ref(v___x_2418_);
lean_dec(v_goal_2393_);
v_a_2489_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2431_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2431_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_a_2428_);
lean_dec(v_a_2426_);
lean_dec_ref(v_arg_2424_);
lean_dec_ref(v_arg_2423_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_arg_2421_);
lean_dec_ref(v___x_2418_);
lean_dec(v_goal_2393_);
v_a_2497_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2429_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2429_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_a_2426_);
lean_dec_ref(v_arg_2424_);
lean_dec_ref(v_arg_2423_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_arg_2421_);
lean_dec_ref(v___x_2418_);
lean_dec(v_goal_2393_);
v_a_2505_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2427_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2427_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v_arg_2424_);
lean_dec_ref(v_arg_2423_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_arg_2421_);
lean_dec_ref(v___x_2418_);
lean_dec(v_goal_2393_);
v_a_2513_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2425_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2425_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
}
}
}
v___jp_2407_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_box(0);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f___boxed(lean_object* v_goal_2521_, lean_object* v_target_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(v_goal_2521_, v_target_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec_ref(v_target_2522_);
return v_res_2535_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__0));
v___x_2538_ = l_Lean_stringToMessageData(v___x_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(lean_object* v_goal_2544_, lean_object* v_pre_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2570_ = l_Lean_Expr_cleanupAnnotations(v_pre_2545_);
v___x_2571_ = l_Lean_Expr_isApp(v___x_2570_);
if (v___x_2571_ == 0)
{
lean_dec_ref(v___x_2570_);
lean_dec(v_goal_2544_);
goto v___jp_2558_;
}
else
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2570_);
v___x_2573_ = l_Lean_Expr_isApp(v___x_2572_);
if (v___x_2573_ == 0)
{
lean_dec_ref(v___x_2572_);
lean_dec_ref(v___x_2570_);
lean_dec(v_goal_2544_);
goto v___jp_2558_;
}
else
{
lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2574_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2572_);
lean_dec_ref(v___x_2572_);
v___x_2575_ = l_Lean_Expr_isApp(v___x_2574_);
if (v___x_2575_ == 0)
{
lean_dec_ref(v___x_2574_);
lean_dec_ref(v___x_2570_);
lean_dec(v_goal_2544_);
goto v___jp_2558_;
}
else
{
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2574_);
lean_dec_ref(v___x_2574_);
v___x_2577_ = l_Lean_Expr_isApp(v___x_2576_);
if (v___x_2577_ == 0)
{
lean_dec_ref(v___x_2576_);
lean_dec_ref(v___x_2570_);
lean_dec(v_goal_2544_);
goto v___jp_2558_;
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2578_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2576_);
lean_dec_ref(v___x_2576_);
v___x_2579_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3));
v___x_2580_ = l_Lean_Expr_isConstOf(v___x_2578_, v___x_2579_);
lean_dec_ref(v___x_2578_);
if (v___x_2580_ == 0)
{
lean_dec_ref(v___x_2570_);
lean_dec(v_goal_2544_);
goto v___jp_2558_;
}
else
{
lean_object* v_arg_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v_arg_2581_ = lean_ctor_get(v___x_2570_, 1);
lean_inc_ref(v_arg_2581_);
lean_dec_ref(v___x_2570_);
v___x_2582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__3));
v___x_2583_ = l_Lean_Expr_isAppOf(v_arg_2581_, v___x_2582_);
lean_dec_ref(v_arg_2581_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec(v_goal_2544_);
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
return v___x_2585_;
}
else
{
lean_object* v_backwardRules_2586_; lean_object* v_meetTop_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v_backwardRules_2586_ = lean_ctor_get(v_a_2546_, 0);
v_meetTop_2587_ = lean_ctor_get(v_backwardRules_2586_, 10);
v___x_2588_ = lean_box(0);
lean_inc(v_goal_2544_);
lean_inc_ref(v_meetTop_2587_);
v___x_2589_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_meetTop_2587_, v_goal_2544_, v___x_2588_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2607_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2607_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2607_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
if (lean_obj_tag(v_a_2590_) == 1)
{
lean_object* v_mvarIds_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2606_; 
v_mvarIds_2594_ = lean_ctor_get(v_a_2590_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_a_2590_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2596_ = v_a_2590_;
v_isShared_2597_ = v_isSharedCheck_2606_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_mvarIds_2594_);
lean_dec(v_a_2590_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2606_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
if (lean_obj_tag(v_mvarIds_2594_) == 1)
{
lean_object* v_tail_2598_; 
v_tail_2598_ = lean_ctor_get(v_mvarIds_2594_, 1);
if (lean_obj_tag(v_tail_2598_) == 0)
{
lean_object* v_head_2599_; lean_object* v___x_2601_; 
lean_dec(v_goal_2544_);
v_head_2599_ = lean_ctor_get(v_mvarIds_2594_, 0);
lean_inc(v_head_2599_);
lean_dec_ref_known(v_mvarIds_2594_, 2);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v_head_2599_);
v___x_2601_ = v___x_2596_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_head_2599_);
v___x_2601_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2603_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v___x_2601_);
v___x_2603_ = v___x_2592_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2594_, 2);
lean_del_object(v___x_2596_);
lean_del_object(v___x_2592_);
v___y_2562_ = v_a_2553_;
v___y_2563_ = v_a_2554_;
v___y_2564_ = v_a_2555_;
v___y_2565_ = v_a_2556_;
goto v___jp_2561_;
}
}
else
{
lean_del_object(v___x_2596_);
lean_dec(v_mvarIds_2594_);
lean_del_object(v___x_2592_);
v___y_2562_ = v_a_2553_;
v___y_2563_ = v_a_2554_;
v___y_2564_ = v_a_2555_;
v___y_2565_ = v_a_2556_;
goto v___jp_2561_;
}
}
}
else
{
lean_del_object(v___x_2592_);
lean_dec(v_a_2590_);
v___y_2562_ = v_a_2553_;
v___y_2563_ = v_a_2554_;
v___y_2564_ = v_a_2555_;
v___y_2565_ = v_a_2556_;
goto v___jp_2561_;
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v_goal_2544_);
v_a_2608_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2589_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2589_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
}
}
}
}
v___jp_2558_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
v___jp_2561_:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2566_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__1);
v___x_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_goal_2544_);
v___x_2568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2566_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_2568_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
return v___x_2569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___boxed(lean_object* v_goal_2616_, lean_object* v_pre_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(v_goal_2616_, v_pre_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec_ref(v_pre_2617_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(lean_object* v_goal_2638_, lean_object* v_pre_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2655_ = l_Lean_Expr_cleanupAnnotations(v_pre_2639_);
v___x_2656_ = l_Lean_Expr_isApp(v___x_2655_);
if (v___x_2656_ == 0)
{
lean_dec_ref(v___x_2655_);
lean_dec(v_goal_2638_);
goto v___jp_2652_;
}
else
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2655_);
v___x_2658_ = l_Lean_Expr_isApp(v___x_2657_);
if (v___x_2658_ == 0)
{
lean_dec_ref(v___x_2657_);
lean_dec_ref(v___x_2655_);
lean_dec(v_goal_2638_);
goto v___jp_2652_;
}
else
{
lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2659_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2657_);
lean_dec_ref(v___x_2657_);
v___x_2660_ = l_Lean_Expr_isApp(v___x_2659_);
if (v___x_2660_ == 0)
{
lean_dec_ref(v___x_2659_);
lean_dec_ref(v___x_2655_);
lean_dec(v_goal_2638_);
goto v___jp_2652_;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2661_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2659_);
lean_dec_ref(v___x_2659_);
v___x_2662_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_2663_ = l_Lean_Expr_isConstOf(v___x_2661_, v___x_2662_);
lean_dec_ref(v___x_2661_);
if (v___x_2663_ == 0)
{
lean_dec_ref(v___x_2655_);
lean_dec(v_goal_2638_);
goto v___jp_2652_;
}
else
{
lean_object* v_arg_2664_; uint8_t v___x_2665_; 
v_arg_2664_ = lean_ctor_get(v___x_2655_, 1);
lean_inc_ref(v_arg_2664_);
lean_dec_ref(v___x_2655_);
v___x_2665_ = l_Lean_Expr_isTrue(v_arg_2664_);
lean_dec_ref(v_arg_2664_);
if (v___x_2665_ == 0)
{
lean_object* v_backwardRules_2666_; lean_object* v_ofPropPreIntro_2667_; lean_object* v___x_2668_; 
v_backwardRules_2666_ = lean_ctor_get(v_a_2640_, 0);
v_ofPropPreIntro_2667_ = lean_ctor_get(v_backwardRules_2666_, 3);
lean_inc_ref(v_ofPropPreIntro_2667_);
v___x_2668_ = l_Lean_Elab_Tactic_VCGen_introPre(v_ofPropPreIntro_2667_, v_goal_2638_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2677_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2677_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2677_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_a_2669_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2673_);
v___x_2675_ = v___x_2671_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_a_2678_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2668_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2668_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec(v_goal_2638_);
v___x_2686_ = lean_box(0);
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
return v___x_2687_;
}
}
}
}
}
v___jp_2652_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_box(0);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___boxed(lean_object* v_goal_2688_, lean_object* v_pre_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(v_goal_2688_, v_pre_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2699_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec_ref(v_pre_2689_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(lean_object* v_goal_2703_, lean_object* v_pre_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = l_Lean_Expr_cleanupAnnotations(v_pre_2704_);
v___x_2724_ = l_Lean_Expr_isApp(v___x_2723_);
if (v___x_2724_ == 0)
{
lean_dec_ref(v___x_2723_);
lean_dec(v_goal_2703_);
goto v___jp_2717_;
}
else
{
lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2723_);
lean_dec_ref(v___x_2723_);
v___x_2726_ = l_Lean_Expr_isApp(v___x_2725_);
if (v___x_2726_ == 0)
{
lean_dec_ref(v___x_2725_);
lean_dec(v_goal_2703_);
goto v___jp_2717_;
}
else
{
lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2727_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2725_);
v___x_2728_ = l_Lean_Expr_isApp(v___x_2727_);
if (v___x_2728_ == 0)
{
lean_dec_ref(v___x_2727_);
lean_dec_ref(v___x_2725_);
lean_dec(v_goal_2703_);
goto v___jp_2717_;
}
else
{
lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2729_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2727_);
lean_dec_ref(v___x_2727_);
v___x_2730_ = l_Lean_Expr_isApp(v___x_2729_);
if (v___x_2730_ == 0)
{
lean_dec_ref(v___x_2729_);
lean_dec_ref(v___x_2725_);
lean_dec(v_goal_2703_);
goto v___jp_2717_;
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2731_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2729_);
lean_dec_ref(v___x_2729_);
v___x_2732_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f___closed__3));
v___x_2733_ = l_Lean_Expr_isConstOf(v___x_2731_, v___x_2732_);
lean_dec_ref(v___x_2731_);
if (v___x_2733_ == 0)
{
lean_dec_ref(v___x_2725_);
lean_dec(v_goal_2703_);
goto v___jp_2717_;
}
else
{
lean_object* v_arg_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
v_arg_2734_ = lean_ctor_get(v___x_2725_, 1);
lean_inc_ref(v_arg_2734_);
lean_dec_ref(v___x_2725_);
v___x_2735_ = l_Lean_Expr_cleanupAnnotations(v_arg_2734_);
lean_dec_ref(v_arg_2734_);
v___x_2736_ = l_Lean_Expr_isApp(v___x_2735_);
if (v___x_2736_ == 0)
{
lean_dec_ref(v___x_2735_);
lean_dec(v_goal_2703_);
goto v___jp_2720_;
}
else
{
lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2737_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2735_);
lean_dec_ref(v___x_2735_);
v___x_2738_ = l_Lean_Expr_isApp(v___x_2737_);
if (v___x_2738_ == 0)
{
lean_dec_ref(v___x_2737_);
lean_dec(v_goal_2703_);
goto v___jp_2720_;
}
else
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2737_);
lean_dec_ref(v___x_2737_);
v___x_2740_ = l_Lean_Expr_isApp(v___x_2739_);
if (v___x_2740_ == 0)
{
lean_dec_ref(v___x_2739_);
lean_dec(v_goal_2703_);
goto v___jp_2720_;
}
else
{
lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2741_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2739_);
lean_dec_ref(v___x_2739_);
v___x_2742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_2743_ = l_Lean_Expr_isConstOf(v___x_2741_, v___x_2742_);
lean_dec_ref(v___x_2741_);
if (v___x_2743_ == 0)
{
lean_dec(v_goal_2703_);
goto v___jp_2720_;
}
else
{
lean_object* v_backwardRules_2744_; lean_object* v_ofPropMeetPreIntro_2745_; lean_object* v___x_2746_; 
v_backwardRules_2744_ = lean_ctor_get(v_a_2705_, 0);
v_ofPropMeetPreIntro_2745_ = lean_ctor_get(v_backwardRules_2744_, 4);
lean_inc_ref(v_ofPropMeetPreIntro_2745_);
v___x_2746_ = l_Lean_Elab_Tactic_VCGen_introPre(v_ofPropMeetPreIntro_2745_, v_goal_2703_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2755_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2751_, 0, v_a_2747_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2751_);
v___x_2753_ = v___x_2749_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
v_a_2756_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2746_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2746_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
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
v___jp_2717_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = lean_box(0);
v___x_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
return v___x_2719_;
}
v___jp_2720_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = lean_box(0);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f___boxed(lean_object* v_goal_2764_, lean_object* v_pre_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(v_goal_2764_, v_pre_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
lean_dec(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec_ref(v_pre_2765_);
return v_res_2778_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__0));
v___x_2781_ = l_Lean_stringToMessageData(v___x_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(lean_object* v_goal_2787_, lean_object* v_pre_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__3));
v___x_2811_ = lean_unsigned_to_nat(4u);
v___x_2812_ = l_Lean_Expr_isAppOfArity(v_pre_2788_, v___x_2810_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_dec(v_goal_2787_);
v___x_2813_ = lean_box(0);
v___x_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
return v___x_2814_;
}
else
{
lean_object* v_backwardRules_2815_; lean_object* v_iSupPreIntro_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_backwardRules_2815_ = lean_ctor_get(v_a_2789_, 0);
v_iSupPreIntro_2816_ = lean_ctor_get(v_backwardRules_2815_, 5);
v___x_2817_ = lean_box(0);
lean_inc(v_goal_2787_);
lean_inc_ref(v_iSupPreIntro_2816_);
v___x_2818_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_iSupPreIntro_2816_, v_goal_2787_, v___x_2817_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2836_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_2836_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2836_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
if (lean_obj_tag(v_a_2819_) == 1)
{
lean_object* v_mvarIds_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2835_; 
v_mvarIds_2823_ = lean_ctor_get(v_a_2819_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2825_ = v_a_2819_;
v_isShared_2826_ = v_isSharedCheck_2835_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_mvarIds_2823_);
lean_dec(v_a_2819_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2835_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
if (lean_obj_tag(v_mvarIds_2823_) == 1)
{
lean_object* v_tail_2827_; 
v_tail_2827_ = lean_ctor_get(v_mvarIds_2823_, 1);
if (lean_obj_tag(v_tail_2827_) == 0)
{
lean_object* v_head_2828_; lean_object* v___x_2830_; 
lean_dec(v_goal_2787_);
v_head_2828_ = lean_ctor_get(v_mvarIds_2823_, 0);
lean_inc(v_head_2828_);
lean_dec_ref_known(v_mvarIds_2823_, 2);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v_head_2828_);
v___x_2830_ = v___x_2825_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_head_2828_);
v___x_2830_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2832_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2830_);
v___x_2832_ = v___x_2821_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2823_, 2);
lean_del_object(v___x_2825_);
lean_del_object(v___x_2821_);
v___y_2802_ = v_a_2796_;
v___y_2803_ = v_a_2797_;
v___y_2804_ = v_a_2798_;
v___y_2805_ = v_a_2799_;
goto v___jp_2801_;
}
}
else
{
lean_del_object(v___x_2825_);
lean_dec(v_mvarIds_2823_);
lean_del_object(v___x_2821_);
v___y_2802_ = v_a_2796_;
v___y_2803_ = v_a_2797_;
v___y_2804_ = v_a_2798_;
v___y_2805_ = v_a_2799_;
goto v___jp_2801_;
}
}
}
else
{
lean_del_object(v___x_2821_);
lean_dec(v_a_2819_);
v___y_2802_ = v_a_2796_;
v___y_2803_ = v_a_2797_;
v___y_2804_ = v_a_2798_;
v___y_2805_ = v_a_2799_;
goto v___jp_2801_;
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v_goal_2787_);
v_a_2837_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2818_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2818_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
v___jp_2801_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2806_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___closed__1);
v___x_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2807_, 0, v_goal_2787_);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_2808_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f___boxed(lean_object* v_goal_2845_, lean_object* v_pre_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(v_goal_2845_, v_pre_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec_ref(v_pre_2846_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(lean_object* v_goal_2860_, lean_object* v_00_u03b1_2861_, lean_object* v_pre_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
uint8_t v___x_2875_; 
v___x_2875_ = l_Lean_Expr_isProp(v_00_u03b1_2861_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec(v_goal_2860_);
v___x_2876_ = lean_box(0);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
else
{
lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__3));
v___x_2879_ = l_Lean_Expr_isAppOf(v_pre_2862_, v___x_2878_);
if (v___x_2879_ == 0)
{
lean_object* v_backwardRules_2880_; lean_object* v_propPreIntro_2881_; lean_object* v___x_2882_; 
v_backwardRules_2880_ = lean_ctor_get(v_a_2863_, 0);
v_propPreIntro_2881_ = lean_ctor_get(v_backwardRules_2880_, 2);
lean_inc_ref(v_propPreIntro_2881_);
v___x_2882_ = l_Lean_Elab_Tactic_VCGen_introPre(v_propPreIntro_2881_, v_goal_2860_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2891_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2885_ = v___x_2882_;
v_isShared_2886_ = v_isSharedCheck_2891_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2882_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2891_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v_a_2883_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 0, v___x_2887_);
v___x_2889_ = v___x_2885_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
v_a_2892_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2882_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2882_);
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
else
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
lean_dec(v_goal_2860_);
v___x_2900_ = lean_box(0);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f___boxed(lean_object* v_goal_2902_, lean_object* v_00_u03b1_2903_, lean_object* v_pre_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(v_goal_2902_, v_00_u03b1_2903_, v_pre_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_);
lean_dec(v_a_2915_);
lean_dec_ref(v_a_2914_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec_ref(v_pre_2904_);
lean_dec_ref(v_00_u03b1_2903_);
return v_res_2917_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__0));
v___x_2920_ = l_Lean_stringToMessageData(v___x_2919_);
return v___x_2920_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4(void){
_start:
{
uint8_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = 0;
v___x_2927_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__3));
v___x_2928_ = l_Lean_MessageData_ofConstName(v___x_2927_, v___x_2926_);
return v___x_2928_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5(void){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__4);
v___x_2930_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__1);
v___x_2931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
lean_ctor_set(v___x_2931_, 1, v___x_2929_);
return v___x_2931_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__6));
v___x_2934_ = l_Lean_stringToMessageData(v___x_2933_);
return v___x_2934_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__7);
v___x_2936_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__5);
v___x_2937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v___x_2935_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(lean_object* v_goal_2938_, lean_object* v_pre_2939_, lean_object* v_target_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; uint8_t v___x_3010_; 
v___x_3010_ = l_Lean_Expr_isTrue(v_pre_2939_);
if (v___x_3010_ == 0)
{
v___y_2954_ = v_a_2946_;
v___y_2955_ = v_a_2947_;
v___y_2956_ = v_a_2948_;
v___y_2957_ = v_a_2949_;
v___y_2958_ = v_a_2950_;
v___y_2959_ = v_a_2951_;
goto v___jp_2953_;
}
else
{
lean_object* v_backwardRules_3011_; lean_object* v_truePreIntro_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_dec_ref(v_pre_2939_);
v_backwardRules_3011_ = lean_ctor_get(v_a_2941_, 0);
v_truePreIntro_3012_ = lean_ctor_get(v_backwardRules_3011_, 6);
v___x_3013_ = lean_box(0);
lean_inc_ref(v_truePreIntro_3012_);
v___x_3014_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_truePreIntro_3012_, v_goal_2938_, v___x_3013_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3031_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3017_ = v___x_3014_;
v_isShared_3018_ = v_isSharedCheck_3031_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3031_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
if (lean_obj_tag(v_a_3015_) == 1)
{
lean_object* v_mvarIds_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3030_; 
v_mvarIds_3019_ = lean_ctor_get(v_a_3015_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_a_3015_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3021_ = v_a_3015_;
v_isShared_3022_ = v_isSharedCheck_3030_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_mvarIds_3019_);
lean_dec(v_a_3015_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3030_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
if (lean_obj_tag(v_mvarIds_3019_) == 1)
{
lean_object* v_tail_3023_; 
v_tail_3023_ = lean_ctor_get(v_mvarIds_3019_, 1);
if (lean_obj_tag(v_tail_3023_) == 0)
{
lean_object* v___x_3025_; 
lean_dec_ref(v_target_2940_);
if (v_isShared_3022_ == 0)
{
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_mvarIds_3019_);
v___x_3025_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3027_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3025_);
v___x_3027_ = v___x_3017_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_3019_, 2);
lean_del_object(v___x_3021_);
lean_del_object(v___x_3017_);
v___y_2992_ = v_a_2946_;
v___y_2993_ = v_a_2947_;
v___y_2994_ = v_a_2948_;
v___y_2995_ = v_a_2949_;
v___y_2996_ = v_a_2950_;
v___y_2997_ = v_a_2951_;
goto v___jp_2991_;
}
}
else
{
lean_del_object(v___x_3021_);
lean_dec(v_mvarIds_3019_);
lean_del_object(v___x_3017_);
v___y_2992_ = v_a_2946_;
v___y_2993_ = v_a_2947_;
v___y_2994_ = v_a_2948_;
v___y_2995_ = v_a_2949_;
v___y_2996_ = v_a_2950_;
v___y_2997_ = v_a_2951_;
goto v___jp_2991_;
}
}
}
else
{
lean_del_object(v___x_3017_);
lean_dec(v_a_3015_);
v___y_2992_ = v_a_2946_;
v___y_2993_ = v_a_2947_;
v___y_2994_ = v_a_2948_;
v___y_2995_ = v_a_2949_;
v___y_2996_ = v_a_2950_;
v___y_2997_ = v_a_2951_;
goto v___jp_2991_;
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_target_2940_);
v_a_3032_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3014_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3014_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
v___jp_2953_:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(v_goal_2938_, v_target_2940_, v_pre_2939_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2982_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_2982_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2982_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
if (lean_obj_tag(v_a_2961_) == 1)
{
lean_object* v_val_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2977_; 
v_val_2965_ = lean_ctor_get(v_a_2961_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_a_2961_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2967_ = v_a_2961_;
v_isShared_2968_ = v_isSharedCheck_2977_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_val_2965_);
lean_dec(v_a_2961_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2977_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2969_ = lean_box(0);
v___x_2970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2970_, 0, v_val_2965_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___x_2970_);
v___x_2972_ = v___x_2967_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2974_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2972_);
v___x_2974_ = v___x_2963_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
lean_dec(v_a_2961_);
v___x_2978_ = lean_box(0);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2978_);
v___x_2980_ = v___x_2963_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
v_a_2983_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2960_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2960_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
v___jp_2991_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
v___x_2998_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___closed__8);
v___x_2999_ = l_Lean_indentExpr(v_target_2940_);
v___x_3000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_3000_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_3001_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f___boxed(lean_object* v_goal_3040_, lean_object* v_pre_3041_, lean_object* v_target_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(v_goal_3040_, v_pre_3041_, v_target_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(lean_object* v_scope_3056_, lean_object* v_goal_3057_, lean_object* v_00_u03b1_3058_, lean_object* v_pre_3059_, lean_object* v_target_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v_g_3074_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v_g_3093_; lean_object* v_h_3094_; lean_object* v___x_3102_; 
lean_inc(v_goal_3057_);
v___x_3102_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stripMeetTopPre_x3f(v_goal_3057_, v_pre_3059_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
if (lean_obj_tag(v_a_3103_) == 1)
{
lean_object* v_val_3104_; 
lean_dec_ref(v_target_3060_);
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
v_val_3104_ = lean_ctor_get(v_a_3103_, 0);
lean_inc(v_val_3104_);
lean_dec_ref_known(v_a_3103_, 1);
v_g_3074_ = v_val_3104_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3105_; 
lean_dec(v_a_3103_);
lean_inc(v_goal_3057_);
v___x_3105_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropPreIntro_x3f(v_goal_3057_, v_pre_3059_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
if (lean_obj_tag(v_a_3106_) == 1)
{
lean_object* v_val_3107_; lean_object* v_fst_3108_; lean_object* v_snd_3109_; 
lean_dec_ref(v_target_3060_);
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
v_val_3107_ = lean_ctor_get(v_a_3106_, 0);
lean_inc(v_val_3107_);
lean_dec_ref_known(v_a_3106_, 1);
v_fst_3108_ = lean_ctor_get(v_val_3107_, 0);
lean_inc(v_fst_3108_);
v_snd_3109_ = lean_ctor_get(v_val_3107_, 1);
lean_inc(v_snd_3109_);
lean_dec(v_val_3107_);
v_g_3093_ = v_fst_3108_;
v_h_3094_ = v_snd_3109_;
goto v___jp_3092_;
}
else
{
lean_object* v___x_3110_; 
lean_dec(v_a_3106_);
lean_inc(v_goal_3057_);
v___x_3110_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_ofPropMeetPreIntro_x3f(v_goal_3057_, v_pre_3059_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref_known(v___x_3110_, 1);
if (lean_obj_tag(v_a_3111_) == 1)
{
lean_object* v_val_3112_; lean_object* v_fst_3113_; lean_object* v_snd_3114_; 
lean_dec_ref(v_target_3060_);
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
v_val_3112_ = lean_ctor_get(v_a_3111_, 0);
lean_inc(v_val_3112_);
lean_dec_ref_known(v_a_3111_, 1);
v_fst_3113_ = lean_ctor_get(v_val_3112_, 0);
lean_inc(v_fst_3113_);
v_snd_3114_ = lean_ctor_get(v_val_3112_, 1);
lean_inc(v_snd_3114_);
lean_dec(v_val_3112_);
v_g_3093_ = v_fst_3113_;
v_h_3094_ = v_snd_3114_;
goto v___jp_3092_;
}
else
{
lean_object* v___x_3115_; 
lean_dec(v_a_3111_);
lean_inc(v_goal_3057_);
v___x_3115_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_iSupPreIntro_x3f(v_goal_3057_, v_pre_3059_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref_known(v___x_3115_, 1);
if (lean_obj_tag(v_a_3116_) == 1)
{
lean_object* v_val_3117_; 
lean_dec_ref(v_target_3060_);
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
v_val_3117_ = lean_ctor_get(v_a_3116_, 0);
lean_inc(v_val_3117_);
lean_dec_ref_known(v_a_3116_, 1);
v_g_3074_ = v_val_3117_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3118_; 
lean_dec(v_a_3116_);
lean_inc(v_goal_3057_);
v___x_3118_ = l_Lean_Elab_Tactic_VCGen_introsExcessArgs(v_goal_3057_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
if (lean_obj_tag(v_a_3119_) == 1)
{
lean_object* v_val_3120_; 
lean_dec_ref(v_target_3060_);
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
v_val_3120_ = lean_ctor_get(v_a_3119_, 0);
lean_inc(v_val_3120_);
lean_dec_ref_known(v_a_3119_, 1);
v_g_3074_ = v_val_3120_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3121_; 
lean_dec(v_a_3119_);
lean_inc_ref(v_pre_3059_);
lean_inc(v_goal_3057_);
v___x_3121_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePreToTop_x3f(v_goal_3057_, v_pre_3059_, v_target_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3159_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3159_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3159_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
if (lean_obj_tag(v_a_3122_) == 1)
{
lean_object* v_val_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3137_; 
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
v_val_3126_ = lean_ctor_get(v_a_3122_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_a_3122_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3128_ = v_a_3122_;
v_isShared_3129_ = v_isSharedCheck_3137_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_val_3126_);
lean_dec(v_a_3122_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3137_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v_scope_3056_);
lean_ctor_set(v___x_3130_, 1, v_val_3126_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3130_);
v___x_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3134_; 
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3132_);
v___x_3134_ = v___x_3124_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v___x_3138_; 
lean_del_object(v___x_3124_);
lean_dec(v_a_3122_);
v___x_3138_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_barePreIntro_x3f(v_goal_3057_, v_00_u03b1_3058_, v_pre_3059_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
lean_dec_ref(v_pre_3059_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3150_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3150_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3150_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
if (lean_obj_tag(v_a_3139_) == 1)
{
lean_object* v_val_3143_; lean_object* v_fst_3144_; lean_object* v_snd_3145_; 
lean_del_object(v___x_3141_);
v_val_3143_ = lean_ctor_get(v_a_3139_, 0);
lean_inc(v_val_3143_);
lean_dec_ref_known(v_a_3139_, 1);
v_fst_3144_ = lean_ctor_get(v_val_3143_, 0);
lean_inc(v_fst_3144_);
v_snd_3145_ = lean_ctor_get(v_val_3143_, 1);
lean_inc(v_snd_3145_);
lean_dec(v_val_3143_);
v_g_3093_ = v_fst_3144_;
v_h_3094_ = v_snd_3145_;
goto v___jp_3092_;
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3148_; 
lean_dec(v_a_3139_);
lean_dec_ref(v_scope_3056_);
v___x_3146_ = lean_box(0);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3146_);
v___x_3148_ = v___x_3141_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3146_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_dec_ref(v_scope_3056_);
v_a_3151_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3138_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3138_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
lean_dec_ref(v_scope_3056_);
v_a_3160_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3121_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3121_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref(v_target_3060_);
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
lean_dec_ref(v_scope_3056_);
v_a_3168_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3118_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3118_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
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
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec_ref(v_target_3060_);
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
lean_dec_ref(v_scope_3056_);
v_a_3176_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3115_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3115_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec_ref(v_target_3060_);
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
lean_dec_ref(v_scope_3056_);
v_a_3184_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3110_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3110_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref(v_target_3060_);
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
lean_dec_ref(v_scope_3056_);
v_a_3192_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3105_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3105_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec_ref(v_target_3060_);
lean_dec_ref(v_pre_3059_);
lean_dec(v_goal_3057_);
lean_dec_ref(v_scope_3056_);
v_a_3200_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3102_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3102_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
v___jp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3075_ = lean_box(0);
v___x_3076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3076_, 0, v_g_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3077_, 0, v_scope_3056_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
v___jp_3080_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3086_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3086_, 0, v___y_3083_);
lean_ctor_set(v___x_3086_, 1, v___y_3085_);
lean_ctor_set(v___x_3086_, 2, v___y_3081_);
lean_ctor_set(v___x_3086_, 3, v___y_3084_);
v___x_3087_ = lean_box(0);
v___x_3088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___y_3082_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3086_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
v___jp_3092_:
{
if (lean_obj_tag(v_h_3094_) == 0)
{
lean_object* v_specs_3095_; lean_object* v_lastLiftedPre_x3f_3096_; lean_object* v_nextDeclIdx_3097_; lean_object* v_joinPoints_3098_; 
v_specs_3095_ = lean_ctor_get(v_scope_3056_, 0);
lean_inc_ref(v_specs_3095_);
v_lastLiftedPre_x3f_3096_ = lean_ctor_get(v_scope_3056_, 1);
lean_inc(v_lastLiftedPre_x3f_3096_);
v_nextDeclIdx_3097_ = lean_ctor_get(v_scope_3056_, 2);
lean_inc(v_nextDeclIdx_3097_);
v_joinPoints_3098_ = lean_ctor_get(v_scope_3056_, 3);
lean_inc(v_joinPoints_3098_);
lean_dec_ref(v_scope_3056_);
v___y_3081_ = v_nextDeclIdx_3097_;
v___y_3082_ = v_g_3093_;
v___y_3083_ = v_specs_3095_;
v___y_3084_ = v_joinPoints_3098_;
v___y_3085_ = v_lastLiftedPre_x3f_3096_;
goto v___jp_3080_;
}
else
{
lean_object* v_specs_3099_; lean_object* v_nextDeclIdx_3100_; lean_object* v_joinPoints_3101_; 
v_specs_3099_ = lean_ctor_get(v_scope_3056_, 0);
lean_inc_ref(v_specs_3099_);
v_nextDeclIdx_3100_ = lean_ctor_get(v_scope_3056_, 2);
lean_inc(v_nextDeclIdx_3100_);
v_joinPoints_3101_ = lean_ctor_get(v_scope_3056_, 3);
lean_inc(v_joinPoints_3101_);
lean_dec_ref(v_scope_3056_);
v___y_3081_ = v_nextDeclIdx_3100_;
v___y_3082_ = v_g_3093_;
v___y_3083_ = v_specs_3099_;
v___y_3084_ = v_joinPoints_3101_;
v___y_3085_ = v_h_3094_;
goto v___jp_3080_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f___boxed(lean_object** _args){
lean_object* v_scope_3208_ = _args[0];
lean_object* v_goal_3209_ = _args[1];
lean_object* v_00_u03b1_3210_ = _args[2];
lean_object* v_pre_3211_ = _args[3];
lean_object* v_target_3212_ = _args[4];
lean_object* v_a_3213_ = _args[5];
lean_object* v_a_3214_ = _args[6];
lean_object* v_a_3215_ = _args[7];
lean_object* v_a_3216_ = _args[8];
lean_object* v_a_3217_ = _args[9];
lean_object* v_a_3218_ = _args[10];
lean_object* v_a_3219_ = _args[11];
lean_object* v_a_3220_ = _args[12];
lean_object* v_a_3221_ = _args[13];
lean_object* v_a_3222_ = _args[14];
lean_object* v_a_3223_ = _args[15];
lean_object* v_a_3224_ = _args[16];
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(v_scope_3208_, v_goal_3209_, v_00_u03b1_3210_, v_pre_3211_, v_target_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec(v_a_3217_);
lean_dec_ref(v_a_3216_);
lean_dec(v_a_3215_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec_ref(v_00_u03b1_3210_);
return v_res_3225_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0(void){
_start:
{
lean_object* v___x_3226_; lean_object* v_dummy_3227_; 
v___x_3226_ = lean_box(0);
v_dummy_3227_ = l_Lean_Expr_sort___override(v___x_3226_);
return v_dummy_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(lean_object* v_goal_3228_, lean_object* v_info_3229_, lean_object* v_prog_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v_head_3243_; lean_object* v_args_3244_; lean_object* v_excessArgs_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v_head_3243_ = lean_ctor_get(v_info_3229_, 1);
lean_inc_ref(v_head_3243_);
v_args_3244_ = lean_ctor_get(v_info_3229_, 2);
lean_inc_ref(v_args_3244_);
v_excessArgs_3245_ = lean_ctor_get(v_info_3229_, 3);
lean_inc_ref(v_excessArgs_3245_);
lean_dec_ref(v_info_3229_);
v___x_3246_ = lean_unsigned_to_nat(7u);
v___x_3247_ = lean_array_set(v_args_3244_, v___x_3246_, v_prog_3230_);
v___x_3248_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(v_head_3243_, v___x_3247_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
lean_dec_ref(v___x_3247_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v___x_3250_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(v_a_3249_, v_excessArgs_3245_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
lean_dec_ref(v_excessArgs_3245_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3252_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
lean_inc(v_goal_3228_);
v___x_3252_ = l_Lean_MVarId_getType(v_goal_3228_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v_dummy_3254_; lean_object* v_nargs_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc_n(v_a_3253_, 2);
lean_dec_ref_known(v___x_3252_, 1);
v_dummy_3254_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0);
v_nargs_3255_ = l_Lean_Expr_getAppNumArgs(v_a_3253_);
lean_inc(v_nargs_3255_);
v___x_3256_ = lean_mk_array(v_nargs_3255_, v_dummy_3254_);
v___x_3257_ = lean_unsigned_to_nat(1u);
v___x_3258_ = lean_nat_sub(v_nargs_3255_, v___x_3257_);
lean_dec(v_nargs_3255_);
v___x_3259_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3253_, v___x_3256_, v___x_3258_);
v___x_3260_ = l_Lean_Expr_getAppFn(v_a_3253_);
lean_dec(v_a_3253_);
v___x_3261_ = lean_array_get_size(v___x_3259_);
v___x_3262_ = lean_nat_sub(v___x_3261_, v___x_3257_);
v___x_3263_ = lean_array_set(v___x_3259_, v___x_3262_, v_a_3251_);
lean_dec(v___x_3262_);
v___x_3264_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(v___x_3260_, v___x_3263_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
lean_dec_ref(v___x_3263_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v___x_3266_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v___x_3264_, 1);
v___x_3266_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_3228_, v_a_3265_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
return v___x_3266_;
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v_goal_3228_);
v_a_3267_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3264_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3264_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec(v_a_3251_);
lean_dec(v_goal_3228_);
v_a_3275_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3252_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3252_);
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
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v_goal_3228_);
v_a_3283_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3250_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3250_);
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
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec_ref(v_excessArgs_3245_);
lean_dec(v_goal_3228_);
v_a_3291_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3248_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3248_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___boxed(lean_object* v_goal_3299_, lean_object* v_info_3300_, lean_object* v_prog_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3299_, v_info_3300_, v_prog_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
lean_dec(v_a_3308_);
lean_dec_ref(v_a_3307_);
lean_dec(v_a_3306_);
lean_dec_ref(v_a_3305_);
lean_dec(v_a_3304_);
lean_dec(v_a_3303_);
lean_dec_ref(v_a_3302_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(lean_object* v_goal_3315_, lean_object* v_info_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3316_);
if (lean_obj_tag(v___x_3329_) == 10)
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = l_Lean_Expr_consumeMData(v___x_3329_);
lean_dec_ref_known(v___x_3329_, 2);
v___x_3331_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3315_, v_info_3316_, v___x_3330_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3340_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3340_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3340_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3336_; lean_object* v___x_3338_; 
v___x_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3336_, 0, v_a_3332_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v___x_3336_);
v___x_3338_ = v___x_3334_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
v_a_3341_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3331_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3331_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
lean_dec_ref(v___x_3329_);
lean_dec_ref(v_info_3316_);
lean_dec(v_goal_3315_);
v___x_3349_ = lean_box(0);
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
return v___x_3350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f___boxed(lean_object* v_goal_3351_, lean_object* v_info_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(v_goal_3351_, v_info_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpReduceHead_x3f(lean_object* v_goal_3366_, lean_object* v_info_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3367_);
v___x_3381_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v___x_3380_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3415_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3415_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3415_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
if (lean_obj_tag(v_a_3382_) == 1)
{
lean_object* v_val_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3410_; 
lean_del_object(v___x_3384_);
v_val_3386_ = lean_ctor_get(v_a_3382_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_a_3382_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3388_ = v_a_3382_;
v_isShared_3389_ = v_isSharedCheck_3410_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_val_3386_);
lean_dec(v_a_3382_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3410_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; 
v___x_3390_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3366_, v_info_3367_, v_val_3386_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3401_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3393_ = v___x_3390_;
v_isShared_3394_ = v_isSharedCheck_3401_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3401_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v_a_3391_);
v___x_3396_ = v___x_3388_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3398_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v___x_3396_);
v___x_3398_ = v___x_3393_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_del_object(v___x_3388_);
v_a_3402_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3390_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3390_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3413_; 
lean_dec(v_a_3382_);
lean_dec_ref(v_info_3367_);
lean_dec(v_goal_3366_);
v___x_3411_ = lean_box(0);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3411_);
v___x_3413_ = v___x_3384_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref(v_info_3367_);
lean_dec(v_goal_3366_);
v_a_3416_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3381_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3381_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpReduceHead_x3f___boxed(lean_object* v_goal_3424_, lean_object* v_info_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpReduceHead_x3f(v_goal_3424_, v_info_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
lean_dec(v_a_3432_);
lean_dec_ref(v_a_3431_);
lean_dec(v_a_3430_);
lean_dec_ref(v_a_3429_);
lean_dec(v_a_3428_);
lean_dec(v_a_3427_);
lean_dec_ref(v_a_3426_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object* v_revArgs_3439_, lean_object* v_start_3440_, lean_object* v_b_3441_, lean_object* v_i_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
uint8_t v___x_3450_; 
v___x_3450_ = lean_nat_dec_le(v_i_3442_, v_start_3440_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v_i_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3451_ = l_Lean_instInhabitedExpr;
v___x_3452_ = lean_unsigned_to_nat(1u);
v_i_3453_ = lean_nat_sub(v_i_3442_, v___x_3452_);
lean_dec(v_i_3442_);
v___x_3454_ = lean_array_get_borrowed(v___x_3451_, v_revArgs_3439_, v_i_3453_);
lean_inc(v___x_3454_);
v___x_3455_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1_spec__1_spec__3___redArg(v_b_3441_, v___x_3454_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v_b_3441_ = v_a_3456_;
v_i_3442_ = v_i_3453_;
goto _start;
}
else
{
lean_dec(v_i_3453_);
return v___x_3455_;
}
}
else
{
lean_object* v___x_3458_; 
lean_dec(v_i_3442_);
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v_b_3441_);
return v___x_3458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_revArgs_3459_, lean_object* v_start_3460_, lean_object* v_b_3461_, lean_object* v_i_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_3459_, v_start_3460_, v_b_3461_, v_i_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v_start_3460_);
lean_dec_ref(v_revArgs_3459_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(lean_object* v_f_3471_, lean_object* v_revArgs_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3485_ = lean_unsigned_to_nat(0u);
v___x_3486_ = lean_array_get_size(v_revArgs_3472_);
v___x_3487_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_3472_, v___x_3485_, v_f_3471_, v___x_3486_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0___boxed(lean_object* v_f_3488_, lean_object* v_revArgs_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_f_3488_, v_revArgs_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v_revArgs_3489_);
return v_res_3502_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__0));
v___x_3505_ = l_Lean_stringToMessageData(v___x_3504_);
return v___x_3505_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__2));
v___x_3508_ = l_Lean_stringToMessageData(v___x_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(lean_object* v_scope_3509_, lean_object* v_goal_3510_, lean_object* v_info_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v___y_3525_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_3511_);
v___x_3532_ = l_Lean_Expr_getAppFn(v___x_3531_);
if (lean_obj_tag(v___x_3532_) == 8)
{
lean_object* v_declName_3533_; lean_object* v_type_3534_; lean_object* v_value_3535_; lean_object* v_body_3536_; uint8_t v_nondep_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v_appArgs_3541_; lean_object* v___x_3542_; 
v_declName_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_declName_3533_);
v_type_3534_ = lean_ctor_get(v___x_3532_, 1);
lean_inc_ref(v_type_3534_);
v_value_3535_ = lean_ctor_get(v___x_3532_, 2);
lean_inc_ref(v_value_3535_);
v_body_3536_ = lean_ctor_get(v___x_3532_, 3);
lean_inc_ref(v_body_3536_);
v_nondep_3537_ = lean_ctor_get_uint8(v___x_3532_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v___x_3532_, 4);
v___x_3538_ = lean_box(0);
v___x_3539_ = l_Lean_Expr_getAppNumArgs(v___x_3531_);
v___x_3540_ = lean_mk_empty_array_with_capacity(v___x_3539_);
lean_dec(v___x_3539_);
lean_inc_ref(v___x_3531_);
v_appArgs_3541_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3531_, v___x_3540_);
v___x_3542_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v_value_3535_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; uint8_t v___x_3600_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3542_, 1);
v___x_3600_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_isDuplicable(v_a_3543_);
if (v___x_3600_ == 0)
{
lean_object* v_toCold_3601_; lean_object* v_options_3602_; lean_object* v_inheritedTraceOptions_3603_; uint8_t v_hasTrace_3604_; uint8_t v___x_3605_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v_name_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; 
v_toCold_3601_ = lean_ctor_get(v_a_3521_, 0);
v_options_3602_ = lean_ctor_get(v_toCold_3601_, 2);
v_inheritedTraceOptions_3603_ = lean_ctor_get(v_toCold_3601_, 11);
v_hasTrace_3604_ = lean_ctor_get_uint8(v_options_3602_, sizeof(void*)*1);
v___x_3605_ = 1;
if (v_hasTrace_3604_ == 0)
{
v___y_3646_ = v_a_3512_;
v___y_3647_ = v_a_3513_;
v___y_3648_ = v_a_3514_;
v___y_3649_ = v_a_3515_;
v___y_3650_ = v_a_3516_;
v___y_3651_ = v_a_3517_;
v___y_3652_ = v_a_3518_;
v___y_3653_ = v_a_3519_;
v___y_3654_ = v_a_3520_;
v___y_3655_ = v_a_3521_;
v___y_3656_ = v_a_3522_;
goto v___jp_3645_;
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; 
v___x_3744_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_3745_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_3746_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3603_, v_options_3602_, v___x_3745_);
if (v___x_3746_ == 0)
{
v___y_3646_ = v_a_3512_;
v___y_3647_ = v_a_3513_;
v___y_3648_ = v_a_3514_;
v___y_3649_ = v_a_3515_;
v___y_3650_ = v_a_3516_;
v___y_3651_ = v_a_3517_;
v___y_3652_ = v_a_3518_;
v___y_3653_ = v_a_3519_;
v___y_3654_ = v_a_3520_;
v___y_3655_ = v_a_3521_;
v___y_3656_ = v_a_3522_;
goto v___jp_3645_;
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3747_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__3);
lean_inc(v_declName_3533_);
v___x_3748_ = l_Lean_MessageData_ofName(v_declName_3533_);
v___x_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3744_, v___x_3749_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_dec_ref_known(v___x_3750_, 1);
v___y_3646_ = v_a_3512_;
v___y_3647_ = v_a_3513_;
v___y_3648_ = v_a_3514_;
v___y_3649_ = v_a_3515_;
v___y_3650_ = v_a_3516_;
v___y_3651_ = v_a_3517_;
v___y_3652_ = v_a_3518_;
v___y_3653_ = v_a_3519_;
v___y_3654_ = v_a_3520_;
v___y_3655_ = v_a_3521_;
v___y_3656_ = v_a_3522_;
goto v___jp_3645_;
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_dec(v_a_3543_);
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v_body_3536_);
lean_dec_ref(v_type_3534_);
lean_dec(v_declName_3533_);
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_info_3511_);
lean_dec(v_goal_3510_);
lean_dec_ref(v_scope_3509_);
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3750_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3750_);
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
v___jp_3606_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = lean_mk_empty_array_with_capacity(v___y_3607_);
v___x_3622_ = lean_array_push(v___x_3621_, v_name_3609_);
v___x_3623_ = l_Lean_Meta_Sym_intros(v___y_3608_, v___x_3622_, v___x_3605_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3623_, 1);
if (lean_obj_tag(v_a_3624_) == 1)
{
lean_object* v_newDecls_3625_; lean_object* v_mvarId_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; uint8_t v___x_3629_; 
lean_dec_ref(v___x_3531_);
v_newDecls_3625_ = lean_ctor_get(v_a_3624_, 0);
lean_inc_ref(v_newDecls_3625_);
v_mvarId_3626_ = lean_ctor_get(v_a_3624_, 1);
lean_inc(v_mvarId_3626_);
lean_dec_ref_known(v_a_3624_, 2);
v___x_3627_ = lean_array_get_size(v_appArgs_3541_);
lean_dec_ref(v_appArgs_3541_);
v___x_3628_ = lean_unsigned_to_nat(0u);
v___x_3629_ = lean_nat_dec_eq(v___x_3627_, v___x_3628_);
if (v___x_3629_ == 0)
{
lean_dec_ref(v_newDecls_3625_);
lean_dec(v_a_3543_);
lean_dec_ref(v_info_3511_);
v___y_3525_ = v_mvarId_3626_;
goto v___jp_3524_;
}
else
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = lean_array_get(v___x_3538_, v_newDecls_3625_, v___x_3628_);
lean_dec_ref(v_newDecls_3625_);
lean_inc(v_mvarId_3626_);
lean_inc_ref(v_scope_3509_);
v___x_3631_ = l_Lean_Elab_Tactic_VCGen_registerJoinPoint(v_scope_3509_, v_mvarId_3626_, v___x_3630_, v_a_3543_, v_info_3511_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
if (lean_obj_tag(v_a_3632_) == 1)
{
lean_dec(v_mvarId_3626_);
lean_dec_ref(v_scope_3509_);
return v___x_3631_;
}
else
{
lean_dec_ref_known(v___x_3631_, 1);
v___y_3525_ = v_mvarId_3626_;
goto v___jp_3524_;
}
}
else
{
lean_dec(v_mvarId_3626_);
lean_dec_ref(v_scope_3509_);
return v___x_3631_;
}
}
}
else
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_dec(v_a_3624_);
lean_dec(v_a_3543_);
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v_info_3511_);
lean_dec_ref(v_scope_3509_);
v___x_3633_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___closed__1);
v___x_3634_ = l_Lean_indentExpr(v___x_3531_);
v___x_3635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3633_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_3635_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
return v___x_3636_;
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec(v_a_3543_);
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_info_3511_);
lean_dec_ref(v_scope_3509_);
v_a_3637_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3623_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3623_);
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
v___jp_3645_:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_body_3536_, v_appArgs_3541_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v_head_3659_; lean_object* v_args_3660_; lean_object* v_excessArgs_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v___x_3657_, 1);
v_head_3659_ = lean_ctor_get(v_info_3511_, 1);
v_args_3660_ = lean_ctor_get(v_info_3511_, 2);
v_excessArgs_3661_ = lean_ctor_get(v_info_3511_, 3);
v___x_3662_ = lean_unsigned_to_nat(7u);
lean_inc_ref(v_args_3660_);
v___x_3663_ = lean_array_set(v_args_3660_, v___x_3662_, v_a_3658_);
lean_inc_ref(v_head_3659_);
v___x_3664_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(v_head_3659_, v___x_3663_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec_ref(v___x_3663_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3666_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3664_, 1);
v___x_3666_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(v_a_3665_, v_excessArgs_3661_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
lean_inc(v_goal_3510_);
v___x_3668_ = l_Lean_MVarId_getType(v_goal_3510_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v_dummy_3670_; lean_object* v_nargs_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc_n(v_a_3669_, 2);
lean_dec_ref_known(v___x_3668_, 1);
v_dummy_3670_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq___closed__0);
v_nargs_3671_ = l_Lean_Expr_getAppNumArgs(v_a_3669_);
lean_inc(v_nargs_3671_);
v___x_3672_ = lean_mk_array(v_nargs_3671_, v_dummy_3670_);
v___x_3673_ = lean_unsigned_to_nat(1u);
v___x_3674_ = lean_nat_sub(v_nargs_3671_, v___x_3673_);
lean_dec(v_nargs_3671_);
v___x_3675_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3669_, v___x_3672_, v___x_3674_);
v___x_3676_ = l_Lean_Expr_getAppFn(v_a_3669_);
lean_dec(v_a_3669_);
v___x_3677_ = lean_array_get_size(v___x_3675_);
v___x_3678_ = lean_nat_sub(v___x_3677_, v___x_3673_);
v___x_3679_ = lean_array_set(v___x_3675_, v___x_3678_, v_a_3667_);
lean_dec(v___x_3678_);
v___x_3680_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__1(v___x_3676_, v___x_3679_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec_ref(v___x_3679_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_a_3681_);
lean_dec_ref_known(v___x_3680_, 1);
lean_inc(v_a_3543_);
lean_inc(v_declName_3533_);
v___x_3682_ = l_Lean_Expr_letE___override(v_declName_3533_, v_type_3534_, v_a_3543_, v_a_3681_, v_nondep_3537_);
v___x_3683_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_3510_, v___x_3682_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; uint8_t v___x_3685_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3683_, 1);
v___x_3685_ = l_Lean_Elab_Tactic_VCGen_isProgramName(v_declName_3533_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_declName_3533_, v___y_3653_, v___y_3655_, v___y_3656_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v___y_3607_ = v___x_3673_;
v___y_3608_ = v_a_3684_;
v_name_3609_ = v_a_3687_;
v___y_3610_ = v___y_3646_;
v___y_3611_ = v___y_3647_;
v___y_3612_ = v___y_3648_;
v___y_3613_ = v___y_3649_;
v___y_3614_ = v___y_3650_;
v___y_3615_ = v___y_3651_;
v___y_3616_ = v___y_3652_;
v___y_3617_ = v___y_3653_;
v___y_3618_ = v___y_3654_;
v___y_3619_ = v___y_3655_;
v___y_3620_ = v___y_3656_;
goto v___jp_3606_;
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec(v_a_3684_);
lean_dec(v_a_3543_);
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_info_3511_);
lean_dec_ref(v_scope_3509_);
v_a_3688_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3686_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3686_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
else
{
v___y_3607_ = v___x_3673_;
v___y_3608_ = v_a_3684_;
v_name_3609_ = v_declName_3533_;
v___y_3610_ = v___y_3646_;
v___y_3611_ = v___y_3647_;
v___y_3612_ = v___y_3648_;
v___y_3613_ = v___y_3649_;
v___y_3614_ = v___y_3650_;
v___y_3615_ = v___y_3651_;
v___y_3616_ = v___y_3652_;
v___y_3617_ = v___y_3653_;
v___y_3618_ = v___y_3654_;
v___y_3619_ = v___y_3655_;
v___y_3620_ = v___y_3656_;
goto v___jp_3606_;
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v_a_3543_);
lean_dec_ref(v_appArgs_3541_);
lean_dec(v_declName_3533_);
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_info_3511_);
lean_dec_ref(v_scope_3509_);
v_a_3696_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3683_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3683_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v_a_3543_);
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v_type_3534_);
lean_dec(v_declName_3533_);
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_info_3511_);
lean_dec(v_goal_3510_);
lean_dec_ref(v_scope_3509_);
v_a_3704_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3680_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3680_);
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
lean_dec(v_a_3667_);
lean_dec(v_a_3543_);
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v_type_3534_);
lean_dec(v_declName_3533_);
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_info_3511_);
lean_dec(v_goal_3510_);
lean_dec_ref(v_scope_3509_);
v_a_3712_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3668_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3668_);
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
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec(v_a_3543_);
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v_type_3534_);
lean_dec(v_declName_3533_);
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_info_3511_);
lean_dec(v_goal_3510_);
lean_dec_ref(v_scope_3509_);
v_a_3720_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3666_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3666_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec(v_a_3543_);
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v_type_3534_);
lean_dec(v_declName_3533_);
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_info_3511_);
lean_dec(v_goal_3510_);
lean_dec_ref(v_scope_3509_);
v_a_3728_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3664_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3664_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec(v_a_3543_);
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v_type_3534_);
lean_dec(v_declName_3533_);
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_info_3511_);
lean_dec(v_goal_3510_);
lean_dec_ref(v_scope_3509_);
v_a_3736_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3657_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3657_);
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
}
else
{
lean_object* v_toCold_3759_; lean_object* v_options_3760_; uint8_t v_hasTrace_3761_; 
lean_dec_ref(v_type_3534_);
lean_dec_ref(v___x_3531_);
v_toCold_3759_ = lean_ctor_get(v_a_3521_, 0);
v_options_3760_ = lean_ctor_get(v_toCold_3759_, 2);
v_hasTrace_3761_ = lean_ctor_get_uint8(v_options_3760_, sizeof(void*)*1);
if (v_hasTrace_3761_ == 0)
{
lean_dec(v_declName_3533_);
v___y_3545_ = v_a_3512_;
v___y_3546_ = v_a_3513_;
v___y_3547_ = v_a_3514_;
v___y_3548_ = v_a_3515_;
v___y_3549_ = v_a_3516_;
v___y_3550_ = v_a_3517_;
v___y_3551_ = v_a_3518_;
v___y_3552_ = v_a_3519_;
v___y_3553_ = v_a_3520_;
v___y_3554_ = v_a_3521_;
v___y_3555_ = v_a_3522_;
goto v___jp_3544_;
}
else
{
lean_object* v_inheritedTraceOptions_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; 
v_inheritedTraceOptions_3762_ = lean_ctor_get(v_toCold_3759_, 11);
v___x_3763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_3764_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_3765_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3762_, v_options_3760_, v___x_3764_);
if (v___x_3765_ == 0)
{
lean_dec(v_declName_3533_);
v___y_3545_ = v_a_3512_;
v___y_3546_ = v_a_3513_;
v___y_3547_ = v_a_3514_;
v___y_3548_ = v_a_3515_;
v___y_3549_ = v_a_3516_;
v___y_3550_ = v_a_3517_;
v___y_3551_ = v_a_3518_;
v___y_3552_ = v_a_3519_;
v___y_3553_ = v_a_3520_;
v___y_3554_ = v_a_3521_;
v___y_3555_ = v_a_3522_;
goto v___jp_3544_;
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3766_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__11);
v___x_3767_ = l_Lean_MessageData_ofName(v_declName_3533_);
v___x_3768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3766_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3763_, v___x_3768_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_dec_ref_known(v___x_3769_, 1);
v___y_3545_ = v_a_3512_;
v___y_3546_ = v_a_3513_;
v___y_3547_ = v_a_3514_;
v___y_3548_ = v_a_3515_;
v___y_3549_ = v_a_3516_;
v___y_3550_ = v_a_3517_;
v___y_3551_ = v_a_3518_;
v___y_3552_ = v_a_3519_;
v___y_3553_ = v_a_3520_;
v___y_3554_ = v_a_3521_;
v___y_3555_ = v_a_3522_;
goto v___jp_3544_;
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec(v_a_3543_);
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v_body_3536_);
lean_dec_ref(v_info_3511_);
lean_dec(v_goal_3510_);
lean_dec_ref(v_scope_3509_);
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3769_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
}
v___jp_3544_:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3556_ = lean_unsigned_to_nat(1u);
v___x_3557_ = lean_mk_empty_array_with_capacity(v___x_3556_);
v___x_3558_ = lean_array_push(v___x_3557_, v_a_3543_);
v___x_3559_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_3536_, v___x_3558_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3561_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v___x_3561_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0(v_a_3560_, v_appArgs_3541_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec_ref(v_appArgs_3541_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3563_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3561_, 1);
v___x_3563_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_3510_, v_info_3511_, v_a_3562_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3575_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3566_ = v___x_3563_;
v_isShared_3567_ = v_isSharedCheck_3575_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3563_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3575_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3573_; 
v___x_3568_ = lean_box(0);
v___x_3569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3569_, 0, v_a_3564_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_scope_3509_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v___x_3571_);
v___x_3573_ = v___x_3566_;
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
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_dec_ref(v_scope_3509_);
v_a_3576_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3563_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3563_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec_ref(v_info_3511_);
lean_dec(v_goal_3510_);
lean_dec_ref(v_scope_3509_);
v_a_3584_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3561_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3561_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v_info_3511_);
lean_dec(v_goal_3510_);
lean_dec_ref(v_scope_3509_);
v_a_3592_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3559_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3559_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_dec_ref(v_appArgs_3541_);
lean_dec_ref(v_body_3536_);
lean_dec_ref(v_type_3534_);
lean_dec(v_declName_3533_);
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_info_3511_);
lean_dec(v_goal_3510_);
lean_dec_ref(v_scope_3509_);
v_a_3778_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3542_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3542_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
else
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
lean_dec_ref(v___x_3532_);
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_info_3511_);
lean_dec(v_goal_3510_);
lean_dec_ref(v_scope_3509_);
v___x_3786_ = lean_box(0);
v___x_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
return v___x_3787_;
}
v___jp_3524_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3526_ = lean_box(0);
v___x_3527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___y_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3528_, 0, v_scope_3509_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
v___x_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
return v___x_3530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f___boxed(lean_object* v_scope_3788_, lean_object* v_goal_3789_, lean_object* v_info_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(v_scope_3788_, v_goal_3789_, v_info_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
lean_dec(v_a_3801_);
lean_dec_ref(v_a_3800_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
lean_dec(v_a_3797_);
lean_dec_ref(v_a_3796_);
lean_dec(v_a_3795_);
lean_dec_ref(v_a_3794_);
lean_dec(v_a_3793_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0(lean_object* v_revArgs_3804_, lean_object* v_start_3805_, lean_object* v_b_3806_, lean_object* v_i_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_3804_, v_start_3805_, v_b_3806_, v_i_3807_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0___boxed(lean_object* v_revArgs_3821_, lean_object* v_start_3822_, lean_object* v_b_3823_, lean_object* v_i_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f_spec__0_spec__0(v_revArgs_3821_, v_start_3822_, v_b_3823_, v_i_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v_start_3822_);
lean_dec_ref(v_revArgs_3821_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0(lean_object* v_arg_3838_, lean_object* v___x_3839_, lean_object* v___x_3840_, uint8_t v___x_3841_, lean_object* v_a_3842_, lean_object* v_fn_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___x_3854_; 
lean_inc_ref(v_arg_3838_);
v___x_3854_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_arg_3838_, v___x_3839_, v___x_3840_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref_known(v___x_3854_, 1);
v___x_3856_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3856_, 0, v___x_3841_);
lean_ctor_set_uint8(v___x_3856_, 1, v___x_3841_);
v___x_3857_ = l_Lean_Meta_Sym_Simp_mkCongr___redArg(v_a_3842_, v_fn_3843_, v_arg_3838_, v___x_3856_, v_a_3855_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
return v___x_3857_;
}
else
{
lean_dec_ref(v_fn_3843_);
lean_dec_ref(v_a_3842_);
lean_dec_ref(v_arg_3838_);
return v___x_3854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0___boxed(lean_object* v_arg_3858_, lean_object* v___x_3859_, lean_object* v___x_3860_, lean_object* v___x_3861_, lean_object* v_a_3862_, lean_object* v_fn_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
uint8_t v___x_22699__boxed_3874_; lean_object* v_res_3875_; 
v___x_22699__boxed_3874_ = lean_unbox(v___x_3861_);
v_res_3875_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0(v_arg_3858_, v___x_3859_, v___x_3860_, v___x_22699__boxed_3874_, v_a_3862_, v_fn_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec(v___x_3860_);
lean_dec(v___x_3859_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1(uint8_t v___x_3879_, lean_object* v_args_3880_, lean_object* v_goal_3881_, lean_object* v___x_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
if (v___x_3879_ == 0)
{
lean_object* v_simpMethods_3895_; 
v_simpMethods_3895_ = lean_ctor_get(v___y_3883_, 2);
if (lean_obj_tag(v_simpMethods_3895_) == 1)
{
lean_object* v_val_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v_val_3896_ = lean_ctor_get(v_simpMethods_3895_, 0);
v___x_3897_ = lean_array_get_size(v_args_3880_);
lean_inc(v_goal_3881_);
v___x_3898_ = l_Lean_MVarId_getType(v_goal_3881_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3988_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3901_ = v___x_3898_;
v_isShared_3902_ = v_isSharedCheck_3988_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3988_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
if (lean_obj_tag(v_a_3899_) == 5)
{
lean_object* v_fn_3903_; lean_object* v_arg_3904_; lean_object* v___x_3905_; lean_object* v_simpState_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___f_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_del_object(v___x_3901_);
v_fn_3903_ = lean_ctor_get(v_a_3899_, 0);
lean_inc_ref(v_fn_3903_);
v_arg_3904_ = lean_ctor_get(v_a_3899_, 1);
lean_inc_ref(v_arg_3904_);
v___x_3905_ = lean_st_ref_get(v___y_3884_);
v_simpState_3906_ = lean_ctor_get(v___x_3905_, 7);
lean_inc_ref(v_simpState_3906_);
lean_dec(v___x_3905_);
v___x_3907_ = lean_nat_add(v___x_3897_, v___x_3882_);
v___x_3908_ = lean_box(v___x_3879_);
v___f_3909_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3909_, 0, v_arg_3904_);
lean_closure_set(v___f_3909_, 1, v___x_3897_);
lean_closure_set(v___f_3909_, 2, v___x_3907_);
lean_closure_set(v___f_3909_, 3, v___x_3908_);
lean_closure_set(v___f_3909_, 4, v_a_3899_);
lean_closure_set(v___f_3909_, 5, v_fn_3903_);
v___x_3910_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___closed__0));
lean_inc(v_val_3896_);
v___x_3911_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___f_3909_, v_val_3896_, v___x_3910_, v_simpState_3906_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v_fst_3913_; lean_object* v_snd_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3975_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
v_fst_3913_ = lean_ctor_get(v_a_3912_, 0);
v_snd_3914_ = lean_ctor_get(v_a_3912_, 1);
v_isSharedCheck_3975_ = !lean_is_exclusive(v_a_3912_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3916_ = v_a_3912_;
v_isShared_3917_ = v_isSharedCheck_3975_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_snd_3914_);
lean_inc(v_fst_3913_);
lean_dec(v_a_3912_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3975_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3918_; lean_object* v_specBackwardRuleCache_3919_; lean_object* v_splitBackwardRuleCache_3920_; lean_object* v_latticeBackwardRuleCache_3921_; lean_object* v_frameBackwardRuleCache_3922_; lean_object* v_frameDB_3923_; lean_object* v_invariants_3924_; lean_object* v_vcs_3925_; lean_object* v_fuel_3926_; lean_object* v_inlineHandledInvariants_3927_; lean_object* v_pendingJoinPoints_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3973_; 
v___x_3918_ = lean_st_ref_take(v___y_3884_);
v_specBackwardRuleCache_3919_ = lean_ctor_get(v___x_3918_, 0);
v_splitBackwardRuleCache_3920_ = lean_ctor_get(v___x_3918_, 1);
v_latticeBackwardRuleCache_3921_ = lean_ctor_get(v___x_3918_, 2);
v_frameBackwardRuleCache_3922_ = lean_ctor_get(v___x_3918_, 3);
v_frameDB_3923_ = lean_ctor_get(v___x_3918_, 4);
v_invariants_3924_ = lean_ctor_get(v___x_3918_, 5);
v_vcs_3925_ = lean_ctor_get(v___x_3918_, 6);
v_fuel_3926_ = lean_ctor_get(v___x_3918_, 8);
v_inlineHandledInvariants_3927_ = lean_ctor_get(v___x_3918_, 9);
v_pendingJoinPoints_3928_ = lean_ctor_get(v___x_3918_, 10);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3973_ == 0)
{
lean_object* v_unused_3974_; 
v_unused_3974_ = lean_ctor_get(v___x_3918_, 7);
lean_dec(v_unused_3974_);
v___x_3930_ = v___x_3918_;
v_isShared_3931_ = v_isSharedCheck_3973_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_pendingJoinPoints_3928_);
lean_inc(v_inlineHandledInvariants_3927_);
lean_inc(v_fuel_3926_);
lean_inc(v_vcs_3925_);
lean_inc(v_invariants_3924_);
lean_inc(v_frameDB_3923_);
lean_inc(v_frameBackwardRuleCache_3922_);
lean_inc(v_latticeBackwardRuleCache_3921_);
lean_inc(v_splitBackwardRuleCache_3920_);
lean_inc(v_specBackwardRuleCache_3919_);
lean_dec(v___x_3918_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3973_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 7, v_snd_3914_);
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_specBackwardRuleCache_3919_);
lean_ctor_set(v_reuseFailAlloc_3972_, 1, v_splitBackwardRuleCache_3920_);
lean_ctor_set(v_reuseFailAlloc_3972_, 2, v_latticeBackwardRuleCache_3921_);
lean_ctor_set(v_reuseFailAlloc_3972_, 3, v_frameBackwardRuleCache_3922_);
lean_ctor_set(v_reuseFailAlloc_3972_, 4, v_frameDB_3923_);
lean_ctor_set(v_reuseFailAlloc_3972_, 5, v_invariants_3924_);
lean_ctor_set(v_reuseFailAlloc_3972_, 6, v_vcs_3925_);
lean_ctor_set(v_reuseFailAlloc_3972_, 7, v_snd_3914_);
lean_ctor_set(v_reuseFailAlloc_3972_, 8, v_fuel_3926_);
lean_ctor_set(v_reuseFailAlloc_3972_, 9, v_inlineHandledInvariants_3927_);
lean_ctor_set(v_reuseFailAlloc_3972_, 10, v_pendingJoinPoints_3928_);
v___x_3933_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_st_ref_put(v___y_3884_, v___x_3933_);
v___x_3935_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_3913_, v_goal_3881_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3963_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3938_ = v___x_3935_;
v_isShared_3939_ = v_isSharedCheck_3963_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3935_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3963_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
switch(lean_obj_tag(v_a_3936_))
{
case 0:
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
lean_del_object(v___x_3916_);
v___x_3940_ = lean_box(0);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3940_);
v___x_3942_ = v___x_3938_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
case 1:
{
lean_object* v___x_3944_; lean_object* v___x_3946_; 
lean_del_object(v___x_3916_);
v___x_3944_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f___closed__2));
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3944_);
v___x_3946_ = v___x_3938_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
default: 
{
lean_object* v_mvarId_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3962_; 
v_mvarId_3948_ = lean_ctor_get(v_a_3936_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_a_3936_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3950_ = v_a_3936_;
v_isShared_3951_ = v_isSharedCheck_3962_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_mvarId_3948_);
lean_dec(v_a_3936_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3962_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3952_; lean_object* v___x_3954_; 
v___x_3952_ = lean_box(0);
if (v_isShared_3917_ == 0)
{
lean_ctor_set_tag(v___x_3916_, 1);
lean_ctor_set(v___x_3916_, 1, v___x_3952_);
lean_ctor_set(v___x_3916_, 0, v_mvarId_3948_);
v___x_3954_ = v___x_3916_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_mvarId_3948_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v___x_3952_);
v___x_3954_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v___x_3956_; 
if (v_isShared_3951_ == 0)
{
lean_ctor_set_tag(v___x_3950_, 1);
lean_ctor_set(v___x_3950_, 0, v___x_3954_);
v___x_3956_ = v___x_3950_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3954_);
v___x_3956_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
lean_object* v___x_3958_; 
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3956_);
v___x_3958_ = v___x_3938_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
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
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_del_object(v___x_3916_);
v_a_3964_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3935_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3935_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3983_; 
lean_dec(v_goal_3881_);
v_a_3976_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3978_ = v___x_3911_;
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3911_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
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
lean_object* v___x_3984_; lean_object* v___x_3986_; 
lean_dec(v_a_3899_);
lean_dec(v_goal_3881_);
v___x_3984_ = lean_box(0);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3984_);
v___x_3986_ = v___x_3901_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3984_);
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
lean_dec(v_goal_3881_);
v_a_3989_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3898_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3898_);
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
lean_object* v___x_3997_; lean_object* v___x_3998_; 
lean_dec(v_goal_3881_);
v___x_3997_ = lean_box(0);
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
return v___x_3998_;
}
}
else
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
lean_dec(v_goal_3881_);
v___x_3999_ = lean_box(0);
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
return v___x_4000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___boxed(lean_object* v___x_4001_, lean_object* v_args_4002_, lean_object* v_goal_4003_, lean_object* v___x_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
uint8_t v___x_22761__boxed_4017_; lean_object* v_res_4018_; 
v___x_22761__boxed_4017_ = lean_unbox(v___x_4001_);
v_res_4018_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1(v___x_22761__boxed_4017_, v_args_4002_, v_goal_4003_, v___x_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___x_4004_);
lean_dec_ref(v_args_4002_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(lean_object* v_goal_4019_, lean_object* v_info_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_){
_start:
{
lean_object* v_args_4033_; lean_object* v_excessArgs_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; uint8_t v___x_4037_; lean_object* v___x_4038_; lean_object* v___y_4039_; lean_object* v___x_4040_; 
v_args_4033_ = lean_ctor_get(v_info_4020_, 2);
lean_inc_ref(v_args_4033_);
v_excessArgs_4034_ = lean_ctor_get(v_info_4020_, 3);
lean_inc_ref(v_excessArgs_4034_);
lean_dec_ref(v_info_4020_);
v___x_4035_ = lean_array_get_size(v_excessArgs_4034_);
lean_dec_ref(v_excessArgs_4034_);
v___x_4036_ = lean_unsigned_to_nat(0u);
v___x_4037_ = lean_nat_dec_eq(v___x_4035_, v___x_4036_);
v___x_4038_ = lean_box(v___x_4037_);
lean_inc(v_goal_4019_);
v___y_4039_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___lam__1___boxed), 16, 4);
lean_closure_set(v___y_4039_, 0, v___x_4038_);
lean_closure_set(v___y_4039_, 1, v_args_4033_);
lean_closure_set(v___y_4039_, 2, v_goal_4019_);
lean_closure_set(v___y_4039_, 3, v___x_4035_);
v___x_4040_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg(v_goal_4019_, v___y_4039_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f___boxed(lean_object* v_goal_4041_, lean_object* v_info_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(v_goal_4041_, v_info_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
lean_dec(v_a_4045_);
lean_dec(v_a_4044_);
lean_dec_ref(v_a_4043_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(lean_object* v_as_x27_4056_, lean_object* v_b_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
if (lean_obj_tag(v_as_x27_4056_) == 0)
{
lean_object* v___x_4067_; 
v___x_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4067_, 0, v_b_4057_);
return v___x_4067_;
}
else
{
lean_object* v_head_4068_; lean_object* v_tail_4069_; lean_object* v___x_4070_; 
v_head_4068_ = lean_ctor_get(v_as_x27_4056_, 0);
v_tail_4069_ = lean_ctor_get(v_as_x27_4056_, 1);
lean_inc(v_head_4068_);
v___x_4070_ = l_Lean_Elab_Tactic_VCGen_simpGoalTelescope___redArg(v_head_4068_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
switch(lean_obj_tag(v_a_4071_))
{
case 0:
{
lean_object* v___x_4072_; 
lean_inc(v_head_4068_);
v___x_4072_ = lean_array_push(v_b_4057_, v_head_4068_);
v_as_x27_4056_ = v_tail_4069_;
v_b_4057_ = v___x_4072_;
goto _start;
}
case 1:
{
v_as_x27_4056_ = v_tail_4069_;
goto _start;
}
default: 
{
lean_object* v_mvarId_4075_; lean_object* v___x_4076_; 
v_mvarId_4075_ = lean_ctor_get(v_a_4071_, 0);
lean_inc(v_mvarId_4075_);
lean_dec_ref_known(v_a_4071_, 1);
v___x_4076_ = lean_array_push(v_b_4057_, v_mvarId_4075_);
v_as_x27_4056_ = v_tail_4069_;
v_b_4057_ = v___x_4076_;
goto _start;
}
}
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_dec_ref(v_b_4057_);
v_a_4078_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4070_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4070_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg___boxed(lean_object* v_as_x27_4086_, lean_object* v_b_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_4086_, v_b_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v_as_x27_4086_);
return v_res_4097_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1(void){
_start:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__0));
v___x_4100_ = l_Lean_stringToMessageData(v___x_4099_);
return v___x_4100_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__4(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__3));
v___x_4105_ = l_Lean_stringToMessageData(v___x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(lean_object* v_goal_4106_, lean_object* v_info_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_){
_start:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4120_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_4107_);
lean_inc_ref(v___x_4120_);
v___x_4121_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v___x_4120_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4191_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4124_ = v___x_4121_;
v_isShared_4125_ = v_isSharedCheck_4191_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4121_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4191_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
if (lean_obj_tag(v_a_4122_) == 1)
{
lean_object* v_val_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4186_; 
lean_del_object(v___x_4124_);
v_val_4126_ = lean_ctor_get(v_a_4122_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v_a_4122_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4128_ = v_a_4122_;
v_isShared_4129_ = v_isSharedCheck_4186_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_val_4126_);
lean_dec(v_a_4122_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4186_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4130_; 
v___x_4130_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_val_4126_, v_info_4107_, v_a_4109_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref_known(v___x_4130_, 1);
v___x_4132_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__1);
v___x_4133_ = l_Lean_indentExpr(v___x_4120_);
lean_inc_ref(v___x_4133_);
v___x_4134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4132_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 0, v___x_4134_);
v___x_4136_ = v___x_4128_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_4131_, v_goal_4106_, v___x_4136_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4138_);
lean_dec_ref_known(v___x_4137_, 1);
if (lean_obj_tag(v_a_4138_) == 1)
{
lean_object* v_mvarIds_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4165_; 
lean_dec_ref(v___x_4133_);
v_mvarIds_4139_ = lean_ctor_get(v_a_4138_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v_a_4138_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4141_ = v_a_4138_;
v_isShared_4142_ = v_isSharedCheck_4165_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_mvarIds_4139_);
lean_dec(v_a_4138_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4165_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__2));
v___x_4144_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_mvarIds_4139_, v___x_4143_, v_a_4108_, v_a_4109_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
lean_dec(v_mvarIds_4139_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4156_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4147_ = v___x_4144_;
v_isShared_4148_ = v_isSharedCheck_4156_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4144_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4156_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; lean_object* v___x_4151_; 
v___x_4149_ = lean_array_to_list(v_a_4145_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v___x_4149_);
v___x_4151_ = v___x_4141_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4149_);
v___x_4151_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_object* v___x_4153_; 
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 0, v___x_4151_);
v___x_4153_ = v___x_4147_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4151_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_del_object(v___x_4141_);
v_a_4157_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4144_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4144_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
}
else
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_dec(v_a_4138_);
v___x_4166_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__4, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___closed__4);
v___x_4167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
lean_ctor_set(v___x_4167_, 1, v___x_4133_);
v___x_4168_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_4167_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
return v___x_4168_;
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_dec_ref(v___x_4133_);
v_a_4169_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4137_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4137_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
}
else
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
lean_del_object(v___x_4128_);
lean_dec_ref(v___x_4120_);
lean_dec(v_goal_4106_);
v_a_4178_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4130_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4130_);
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
else
{
lean_object* v___x_4187_; lean_object* v___x_4189_; 
lean_dec(v_a_4122_);
lean_dec_ref(v___x_4120_);
lean_dec_ref(v_info_4107_);
lean_dec(v_goal_4106_);
v___x_4187_ = lean_box(0);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 0, v___x_4187_);
v___x_4189_ = v___x_4124_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4187_);
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
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec_ref(v___x_4120_);
lean_dec_ref(v_info_4107_);
lean_dec(v_goal_4106_);
v_a_4192_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_4121_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4121_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f___boxed(lean_object* v_goal_4200_, lean_object* v_info_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(v_goal_4200_, v_info_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
lean_dec(v_a_4210_);
lean_dec_ref(v_a_4209_);
lean_dec(v_a_4208_);
lean_dec_ref(v_a_4207_);
lean_dec(v_a_4206_);
lean_dec_ref(v_a_4205_);
lean_dec(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0(lean_object* v_as_4215_, lean_object* v_as_x27_4216_, lean_object* v_b_4217_, lean_object* v_a_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_4216_, v_b_4217_, v___y_4219_, v___y_4220_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0___boxed(lean_object* v_as_4232_, lean_object* v_as_x27_4233_, lean_object* v_b_4234_, lean_object* v_a_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f_spec__0(v_as_4232_, v_as_x27_4233_, v_b_4234_, v_a_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v_as_x27_4233_);
lean_dec(v_as_4232_);
return v_res_4248_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1(void){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__0));
v___x_4251_ = l_Lean_stringToMessageData(v___x_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(lean_object* v_goal_4252_, lean_object* v_info_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_){
_start:
{
lean_object* v___x_4266_; lean_object* v_f_4267_; lean_object* v___x_4268_; 
v___x_4266_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_4253_);
v_f_4267_ = l_Lean_Expr_getAppFn(v___x_4266_);
v___x_4268_ = l_Lean_Expr_fvarId_x3f(v_f_4267_);
lean_dec_ref(v_f_4267_);
if (lean_obj_tag(v___x_4268_) == 1)
{
lean_object* v_val_4269_; uint8_t v___x_4270_; lean_object* v___x_4271_; 
v_val_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc_n(v_val_4269_, 2);
lean_dec_ref_known(v___x_4268_, 1);
v___x_4270_ = 0;
v___x_4271_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_4269_, v___x_4270_, v_a_4261_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4271_) == 0)
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4360_; 
v_a_4272_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4274_ = v___x_4271_;
v_isShared_4275_ = v_isSharedCheck_4360_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4271_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4360_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
if (lean_obj_tag(v_a_4272_) == 1)
{
lean_object* v_val_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4355_; 
lean_del_object(v___x_4274_);
v_val_4276_ = lean_ctor_get(v_a_4272_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v_a_4272_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4278_ = v_a_4272_;
v_isShared_4279_ = v_isSharedCheck_4355_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_val_4276_);
lean_dec(v_a_4272_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4355_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v_toCold_4326_; lean_object* v_options_4327_; uint8_t v_hasTrace_4328_; 
v_toCold_4326_ = lean_ctor_get(v_a_4263_, 0);
v_options_4327_ = lean_ctor_get(v_toCold_4326_, 2);
v_hasTrace_4328_ = lean_ctor_get_uint8(v_options_4327_, sizeof(void*)*1);
if (v_hasTrace_4328_ == 0)
{
lean_dec(v_val_4269_);
v___y_4281_ = v_a_4254_;
v___y_4282_ = v_a_4255_;
v___y_4283_ = v_a_4256_;
v___y_4284_ = v_a_4257_;
v___y_4285_ = v_a_4258_;
v___y_4286_ = v_a_4259_;
v___y_4287_ = v_a_4260_;
v___y_4288_ = v_a_4261_;
v___y_4289_ = v_a_4262_;
v___y_4290_ = v_a_4263_;
v___y_4291_ = v_a_4264_;
goto v___jp_4280_;
}
else
{
lean_object* v_inheritedTraceOptions_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; uint8_t v___x_4332_; 
v_inheritedTraceOptions_4329_ = lean_ctor_get(v_toCold_4326_, 11);
v___x_4330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_4331_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_4332_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4329_, v_options_4327_, v___x_4331_);
if (v___x_4332_ == 0)
{
lean_dec(v_val_4269_);
v___y_4281_ = v_a_4254_;
v___y_4282_ = v_a_4255_;
v___y_4283_ = v_a_4256_;
v___y_4284_ = v_a_4257_;
v___y_4285_ = v_a_4258_;
v___y_4286_ = v_a_4259_;
v___y_4287_ = v_a_4260_;
v___y_4288_ = v_a_4261_;
v___y_4289_ = v_a_4262_;
v___y_4290_ = v_a_4263_;
v___y_4291_ = v_a_4264_;
goto v___jp_4280_;
}
else
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Lean_FVarId_getUserName___redArg(v_val_4269_, v_a_4261_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4333_, 1);
v___x_4335_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___closed__1);
v___x_4336_ = l_Lean_MessageData_ofName(v_a_4334_);
v___x_4337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4335_);
lean_ctor_set(v___x_4337_, 1, v___x_4336_);
v___x_4338_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4330_, v___x_4337_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_dec_ref_known(v___x_4338_, 1);
v___y_4281_ = v_a_4254_;
v___y_4282_ = v_a_4255_;
v___y_4283_ = v_a_4256_;
v___y_4284_ = v_a_4257_;
v___y_4285_ = v_a_4258_;
v___y_4286_ = v_a_4259_;
v___y_4287_ = v_a_4260_;
v___y_4288_ = v_a_4261_;
v___y_4289_ = v_a_4262_;
v___y_4290_ = v_a_4263_;
v___y_4291_ = v_a_4264_;
goto v___jp_4280_;
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_del_object(v___x_4278_);
lean_dec(v_val_4276_);
lean_dec_ref(v___x_4266_);
lean_dec_ref(v_info_4253_);
lean_dec(v_goal_4252_);
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4338_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
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
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_del_object(v___x_4278_);
lean_dec(v_val_4276_);
lean_dec_ref(v___x_4266_);
lean_dec_ref(v_info_4253_);
lean_dec(v_goal_4252_);
v_a_4347_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4333_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4333_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
v___jp_4280_:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4292_ = l_Lean_Expr_getAppNumArgs(v___x_4266_);
v___x_4293_ = lean_mk_empty_array_with_capacity(v___x_4292_);
lean_dec(v___x_4292_);
v___x_4294_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_4266_, v___x_4293_);
v___x_4295_ = l_Lean_Expr_betaRev(v_val_4276_, v___x_4294_, v___x_4270_, v___x_4270_);
lean_dec_ref(v___x_4294_);
v___x_4296_ = l_Lean_Meta_Sym_shareCommonInc(v___x_4295_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4298_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref_known(v___x_4296_, 1);
v___x_4298_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_replaceProgDefEq(v_goal_4252_, v_info_4253_, v_a_4297_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4309_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4301_ = v___x_4298_;
v_isShared_4302_ = v_isSharedCheck_4309_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4298_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4309_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 0, v_a_4299_);
v___x_4304_ = v___x_4278_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4306_; 
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 0, v___x_4304_);
v___x_4306_ = v___x_4301_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_del_object(v___x_4278_);
v_a_4310_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4298_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4298_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_del_object(v___x_4278_);
lean_dec_ref(v_info_4253_);
lean_dec(v_goal_4252_);
v_a_4318_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4296_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4296_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
}
}
else
{
lean_object* v___x_4356_; lean_object* v___x_4358_; 
lean_dec(v_a_4272_);
lean_dec(v_val_4269_);
lean_dec_ref(v___x_4266_);
lean_dec_ref(v_info_4253_);
lean_dec(v_goal_4252_);
v___x_4356_ = lean_box(0);
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 0, v___x_4356_);
v___x_4358_ = v___x_4274_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___x_4356_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
}
else
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4368_; 
lean_dec(v_val_4269_);
lean_dec_ref(v___x_4266_);
lean_dec_ref(v_info_4253_);
lean_dec(v_goal_4252_);
v_a_4361_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4363_ = v___x_4271_;
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4271_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_a_4361_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
else
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
lean_dec(v___x_4268_);
lean_dec_ref(v___x_4266_);
lean_dec_ref(v_info_4253_);
lean_dec(v_goal_4252_);
v___x_4369_ = lean_box(0);
v___x_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4369_);
return v___x_4370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f___boxed(lean_object* v_goal_4371_, lean_object* v_info_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(v_goal_4371_, v_info_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_);
lean_dec(v_a_4383_);
lean_dec_ref(v_a_4382_);
lean_dec(v_a_4381_);
lean_dec_ref(v_a_4380_);
lean_dec(v_a_4379_);
lean_dec_ref(v_a_4378_);
lean_dec(v_a_4377_);
lean_dec_ref(v_a_4376_);
lean_dec(v_a_4375_);
lean_dec(v_a_4374_);
lean_dec_ref(v_a_4373_);
return v_res_4385_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0));
v___x_4388_ = l_Lean_stringToMessageData(v___x_4387_);
return v___x_4388_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2));
v___x_4391_ = l_Lean_stringToMessageData(v___x_4390_);
return v___x_4391_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4393_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4));
v___x_4394_ = l_Lean_stringToMessageData(v___x_4393_);
return v___x_4394_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4396_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6));
v___x_4397_ = l_Lean_stringToMessageData(v___x_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object* v_a_4398_, lean_object* v_a_4399_){
_start:
{
if (lean_obj_tag(v_a_4398_) == 0)
{
lean_object* v___x_4400_; 
v___x_4400_ = l_List_reverse___redArg(v_a_4399_);
return v___x_4400_;
}
else
{
lean_object* v_head_4401_; lean_object* v_tail_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4430_; 
v_head_4401_ = lean_ctor_get(v_a_4398_, 0);
v_tail_4402_ = lean_ctor_get(v_a_4398_, 1);
v_isSharedCheck_4430_ = !lean_is_exclusive(v_a_4398_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4404_ = v_a_4398_;
v_isShared_4405_ = v_isSharedCheck_4430_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_tail_4402_);
lean_inc(v_head_4401_);
lean_dec(v_a_4398_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4430_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___y_4407_; 
switch(lean_obj_tag(v_head_4401_))
{
case 0:
{
lean_object* v_declName_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v_declName_4412_ = lean_ctor_get(v_head_4401_, 0);
lean_inc(v_declName_4412_);
lean_dec_ref_known(v_head_4401_, 1);
v___x_4413_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_4414_ = l_Lean_MessageData_ofName(v_declName_4412_);
v___x_4415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4413_);
lean_ctor_set(v___x_4415_, 1, v___x_4414_);
v___y_4407_ = v___x_4415_;
goto v___jp_4406_;
}
case 1:
{
lean_object* v_fvarId_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v_fvarId_4416_ = lean_ctor_get(v_head_4401_, 0);
lean_inc(v_fvarId_4416_);
lean_dec_ref_known(v_head_4401_, 1);
v___x_4417_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_4418_ = l_Lean_mkFVar(v_fvarId_4416_);
v___x_4419_ = l_Lean_MessageData_ofExpr(v___x_4418_);
v___x_4420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4417_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
v___y_4407_ = v___x_4420_;
goto v___jp_4406_;
}
default: 
{
lean_object* v_ref_4421_; lean_object* v_proof_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v_ref_4421_ = lean_ctor_get(v_head_4401_, 1);
lean_inc(v_ref_4421_);
v_proof_4422_ = lean_ctor_get(v_head_4401_, 2);
lean_inc_ref(v_proof_4422_);
lean_dec_ref_known(v_head_4401_, 3);
v___x_4423_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_4424_ = l_Lean_MessageData_ofSyntax(v_ref_4421_);
v___x_4425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4423_);
lean_ctor_set(v___x_4425_, 1, v___x_4424_);
v___x_4426_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_4427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4425_);
lean_ctor_set(v___x_4427_, 1, v___x_4426_);
v___x_4428_ = l_Lean_MessageData_ofExpr(v_proof_4422_);
v___x_4429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4427_);
lean_ctor_set(v___x_4429_, 1, v___x_4428_);
v___y_4407_ = v___x_4429_;
goto v___jp_4406_;
}
}
v___jp_4406_:
{
lean_object* v___x_4409_; 
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 1, v_a_4399_);
lean_ctor_set(v___x_4404_, 0, v___y_4407_);
v___x_4409_ = v___x_4404_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___y_4407_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v_a_4399_);
v___x_4409_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
v_a_4398_ = v_tail_4402_;
v_a_4399_ = v___x_4409_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t v_sz_4431_, size_t v_i_4432_, lean_object* v_bs_4433_){
_start:
{
uint8_t v___x_4434_; 
v___x_4434_ = lean_usize_dec_lt(v_i_4432_, v_sz_4431_);
if (v___x_4434_ == 0)
{
return v_bs_4433_;
}
else
{
lean_object* v_v_4435_; lean_object* v_proof_4436_; lean_object* v___x_4437_; lean_object* v_bs_x27_4438_; size_t v___x_4439_; size_t v___x_4440_; lean_object* v___x_4441_; 
v_v_4435_ = lean_array_uget_borrowed(v_bs_4433_, v_i_4432_);
v_proof_4436_ = lean_ctor_get(v_v_4435_, 1);
lean_inc_ref(v_proof_4436_);
v___x_4437_ = lean_unsigned_to_nat(0u);
v_bs_x27_4438_ = lean_array_uset(v_bs_4433_, v_i_4432_, v___x_4437_);
v___x_4439_ = ((size_t)1ULL);
v___x_4440_ = lean_usize_add(v_i_4432_, v___x_4439_);
v___x_4441_ = lean_array_uset(v_bs_x27_4438_, v_i_4432_, v_proof_4436_);
v_i_4432_ = v___x_4440_;
v_bs_4433_ = v___x_4441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object* v_sz_4443_, lean_object* v_i_4444_, lean_object* v_bs_4445_){
_start:
{
size_t v_sz_boxed_4446_; size_t v_i_boxed_4447_; lean_object* v_res_4448_; 
v_sz_boxed_4446_ = lean_unbox_usize(v_sz_4443_);
lean_dec(v_sz_4443_);
v_i_boxed_4447_ = lean_unbox_usize(v_i_4444_);
lean_dec(v_i_4444_);
v_res_4448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_boxed_4446_, v_i_boxed_4447_, v_bs_4445_);
return v_res_4448_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1(void){
_start:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0));
v___x_4451_ = l_Lean_stringToMessageData(v___x_4450_);
return v___x_4451_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3(void){
_start:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2));
v___x_4454_ = l_Lean_stringToMessageData(v___x_4453_);
return v___x_4454_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5(void){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4));
v___x_4457_ = l_Lean_stringToMessageData(v___x_4456_);
return v___x_4457_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7(void){
_start:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4459_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6));
v___x_4460_ = l_Lean_stringToMessageData(v___x_4459_);
return v___x_4460_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9(void){
_start:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4462_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8));
v___x_4463_ = l_Lean_stringToMessageData(v___x_4462_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object* v_prog_4464_, lean_object* v_monad_4465_, lean_object* v_thms_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_){
_start:
{
uint8_t v_errorOnMissingSpec_4473_; 
v_errorOnMissingSpec_4473_ = lean_ctor_get_uint8(v_a_4467_, sizeof(void*)*5 + 1);
if (v_errorOnMissingSpec_4473_ == 0)
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4474_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_4474_, 0, v_prog_4464_);
lean_ctor_set(v___x_4474_, 1, v_monad_4465_);
lean_ctor_set(v___x_4474_, 2, v_thms_4466_);
v___x_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
v___x_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4475_);
return v___x_4476_;
}
else
{
lean_object* v___x_4477_; lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4477_ = lean_array_get_size(v_thms_4466_);
v___x_4478_ = lean_unsigned_to_nat(0u);
v___x_4479_ = lean_nat_dec_eq(v___x_4477_, v___x_4478_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; size_t v_sz_4489_; size_t v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4480_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1);
v___x_4481_ = l_Lean_MessageData_ofExpr(v_prog_4464_);
v___x_4482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4480_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
v___x_4483_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3);
v___x_4484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4482_);
lean_ctor_set(v___x_4484_, 1, v___x_4483_);
v___x_4485_ = l_Lean_MessageData_ofExpr(v_monad_4465_);
v___x_4486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4484_);
lean_ctor_set(v___x_4486_, 1, v___x_4485_);
v___x_4487_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5);
v___x_4488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4486_);
lean_ctor_set(v___x_4488_, 1, v___x_4487_);
v_sz_4489_ = lean_array_size(v_thms_4466_);
v___x_4490_ = ((size_t)0ULL);
v___x_4491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_4489_, v___x_4490_, v_thms_4466_);
v___x_4492_ = lean_array_to_list(v___x_4491_);
v___x_4493_ = lean_box(0);
v___x_4494_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1(v___x_4492_, v___x_4493_);
v___x_4495_ = l_Lean_MessageData_ofList(v___x_4494_);
v___x_4496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4488_);
lean_ctor_set(v___x_4496_, 1, v___x_4495_);
v___x_4497_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_4498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4496_);
lean_ctor_set(v___x_4498_, 1, v___x_4497_);
v___x_4499_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_4498_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_);
return v___x_4499_;
}
else
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
lean_dec_ref(v_thms_4466_);
lean_dec_ref(v_monad_4465_);
v___x_4500_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9);
v___x_4501_ = l_Lean_MessageData_ofExpr(v_prog_4464_);
v___x_4502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4500_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
v___x_4503_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_4504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4502_);
lean_ctor_set(v___x_4504_, 1, v___x_4503_);
v___x_4505_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_4504_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_);
return v___x_4505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object* v_prog_4506_, lean_object* v_monad_4507_, lean_object* v_thms_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_4506_, v_monad_4507_, v_thms_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
lean_dec_ref(v_a_4509_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec(lean_object* v_prog_4516_, lean_object* v_monad_4517_, lean_object* v_thms_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
lean_object* v___x_4531_; 
v___x_4531_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_4516_, v_monad_4517_, v_thms_4518_, v_a_4519_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object* v_prog_4532_, lean_object* v_monad_4533_, lean_object* v_thms_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec(v_prog_4532_, v_monad_4533_, v_thms_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
lean_dec(v_a_4545_);
lean_dec_ref(v_a_4544_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
lean_dec(v_a_4539_);
lean_dec_ref(v_a_4538_);
lean_dec(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
return v_res_4547_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1(void){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4549_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__0));
v___x_4550_ = l_Lean_stringToMessageData(v___x_4549_);
return v___x_4550_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3(void){
_start:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__2));
v___x_4553_ = l_Lean_stringToMessageData(v___x_4552_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(lean_object* v_prog_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_){
_start:
{
lean_object* v_untilPat_x3f_4563_; 
v_untilPat_x3f_4563_ = lean_ctor_get(v_a_4555_, 4);
if (lean_obj_tag(v_untilPat_x3f_4563_) == 1)
{
lean_object* v_val_4564_; uint8_t v___x_4565_; lean_object* v___x_4566_; 
v_val_4564_ = lean_ctor_get(v_untilPat_x3f_4563_, 0);
v___x_4565_ = 1;
lean_inc_ref(v_prog_4554_);
lean_inc(v_val_4564_);
v___x_4566_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_val_4564_, v_prog_4554_, v___x_4565_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4614_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4569_ = v___x_4566_;
v_isShared_4570_ = v_isSharedCheck_4614_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v___x_4566_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4614_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
if (lean_obj_tag(v_a_4567_) == 0)
{
uint8_t v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4574_; 
lean_dec_ref(v_prog_4554_);
v___x_4571_ = 0;
v___x_4572_ = lean_box(v___x_4571_);
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 0, v___x_4572_);
v___x_4574_ = v___x_4569_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4572_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
else
{
lean_object* v_toCold_4576_; lean_object* v_options_4577_; uint8_t v_hasTrace_4578_; 
lean_dec_ref_known(v_a_4567_, 1);
v_toCold_4576_ = lean_ctor_get(v_a_4560_, 0);
v_options_4577_ = lean_ctor_get(v_toCold_4576_, 2);
v_hasTrace_4578_ = lean_ctor_get_uint8(v_options_4577_, sizeof(void*)*1);
if (v_hasTrace_4578_ == 0)
{
lean_object* v___x_4579_; lean_object* v___x_4581_; 
lean_dec_ref(v_prog_4554_);
v___x_4579_ = lean_box(v___x_4565_);
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 0, v___x_4579_);
v___x_4581_ = v___x_4569_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4579_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
else
{
lean_object* v_inheritedTraceOptions_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; uint8_t v___x_4586_; 
v_inheritedTraceOptions_4583_ = lean_ctor_get(v_toCold_4576_, 11);
v___x_4584_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_4585_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_4586_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4583_, v_options_4577_, v___x_4585_);
if (v___x_4586_ == 0)
{
lean_object* v___x_4587_; lean_object* v___x_4589_; 
lean_dec_ref(v_prog_4554_);
v___x_4587_ = lean_box(v___x_4565_);
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 0, v___x_4587_);
v___x_4589_ = v___x_4569_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4587_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
else
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
lean_del_object(v___x_4569_);
v___x_4591_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__1);
v___x_4592_ = l_Lean_MessageData_ofExpr(v_prog_4554_);
v___x_4593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4591_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
v___x_4594_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___closed__3);
v___x_4595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4593_);
lean_ctor_set(v___x_4595_, 1, v___x_4594_);
v___x_4596_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4584_, v___x_4595_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4604_; 
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4604_ == 0)
{
lean_object* v_unused_4605_; 
v_unused_4605_ = lean_ctor_get(v___x_4596_, 0);
lean_dec(v_unused_4605_);
v___x_4598_ = v___x_4596_;
v_isShared_4599_ = v_isSharedCheck_4604_;
goto v_resetjp_4597_;
}
else
{
lean_dec(v___x_4596_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4604_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4600_; lean_object* v___x_4602_; 
v___x_4600_ = lean_box(v___x_4565_);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 0, v___x_4600_);
v___x_4602_ = v___x_4598_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4600_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
else
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
v_a_4606_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4596_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4596_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
v___x_4611_ = v___x_4608_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4606_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
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
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
lean_dec_ref(v_prog_4554_);
v_a_4615_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4566_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4566_);
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
else
{
uint8_t v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
lean_dec_ref(v_prog_4554_);
v___x_4623_ = 0;
v___x_4624_ = lean_box(v___x_4623_);
v___x_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4624_);
return v___x_4625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg___boxed(lean_object* v_prog_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v_prog_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
lean_dec(v_a_4633_);
lean_dec_ref(v_a_4632_);
lean_dec(v_a_4631_);
lean_dec_ref(v_a_4630_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
lean_dec_ref(v_a_4627_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern(lean_object* v_prog_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
lean_object* v___x_4649_; 
v___x_4649_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v_prog_4636_, v_a_4637_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
return v___x_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___boxed(lean_object* v_prog_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern(v_prog_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_);
lean_dec(v_a_4661_);
lean_dec_ref(v_a_4660_);
lean_dec(v_a_4659_);
lean_dec_ref(v_a_4658_);
lean_dec(v_a_4657_);
lean_dec_ref(v_a_4656_);
lean_dec(v_a_4655_);
lean_dec_ref(v_a_4654_);
lean_dec(v_a_4653_);
lean_dec(v_a_4652_);
lean_dec_ref(v_a_4651_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(lean_object* v_k_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v_b_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v___x_4678_; 
lean_inc(v___y_4676_);
lean_inc_ref(v___y_4675_);
lean_inc(v___y_4674_);
lean_inc_ref(v___y_4673_);
lean_inc(v___y_4671_);
lean_inc_ref(v___y_4670_);
lean_inc(v___y_4669_);
lean_inc_ref(v___y_4668_);
lean_inc(v___y_4667_);
lean_inc(v___y_4666_);
lean_inc_ref(v___y_4665_);
v___x_4678_ = lean_apply_13(v_k_4664_, v_b_4672_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, lean_box(0));
return v___x_4678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v_b_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(v_k_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v_b_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v___y_4682_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
return v_res_4693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(lean_object* v_name_4694_, lean_object* v_type_4695_, lean_object* v_val_4696_, lean_object* v_k_4697_, uint8_t v_nondep_4698_, uint8_t v_kind_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
lean_object* v___f_4712_; lean_object* v___x_4713_; 
lean_inc(v___y_4706_);
lean_inc_ref(v___y_4705_);
lean_inc(v___y_4704_);
lean_inc_ref(v___y_4703_);
lean_inc(v___y_4702_);
lean_inc(v___y_4701_);
lean_inc_ref(v___y_4700_);
v___f_4712_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_4712_, 0, v_k_4697_);
lean_closure_set(v___f_4712_, 1, v___y_4700_);
lean_closure_set(v___f_4712_, 2, v___y_4701_);
lean_closure_set(v___f_4712_, 3, v___y_4702_);
lean_closure_set(v___f_4712_, 4, v___y_4703_);
lean_closure_set(v___f_4712_, 5, v___y_4704_);
lean_closure_set(v___f_4712_, 6, v___y_4705_);
lean_closure_set(v___f_4712_, 7, v___y_4706_);
v___x_4713_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_4694_, v_type_4695_, v_val_4696_, v___f_4712_, v_nondep_4698_, v_kind_4699_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
if (lean_obj_tag(v___x_4713_) == 0)
{
return v___x_4713_;
}
else
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
v_a_4714_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4716_ = v___x_4713_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4713_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4719_; 
if (v_isShared_4717_ == 0)
{
v___x_4719_ = v___x_4716_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4714_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_name_4722_ = _args[0];
lean_object* v_type_4723_ = _args[1];
lean_object* v_val_4724_ = _args[2];
lean_object* v_k_4725_ = _args[3];
lean_object* v_nondep_4726_ = _args[4];
lean_object* v_kind_4727_ = _args[5];
lean_object* v___y_4728_ = _args[6];
lean_object* v___y_4729_ = _args[7];
lean_object* v___y_4730_ = _args[8];
lean_object* v___y_4731_ = _args[9];
lean_object* v___y_4732_ = _args[10];
lean_object* v___y_4733_ = _args[11];
lean_object* v___y_4734_ = _args[12];
lean_object* v___y_4735_ = _args[13];
lean_object* v___y_4736_ = _args[14];
lean_object* v___y_4737_ = _args[15];
lean_object* v___y_4738_ = _args[16];
lean_object* v___y_4739_ = _args[17];
_start:
{
uint8_t v_nondep_boxed_4740_; uint8_t v_kind_boxed_4741_; lean_object* v_res_4742_; 
v_nondep_boxed_4740_ = lean_unbox(v_nondep_4726_);
v_kind_boxed_4741_ = lean_unbox(v_kind_4727_);
v_res_4742_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4722_, v_type_4723_, v_val_4724_, v_k_4725_, v_nondep_boxed_4740_, v_kind_boxed_4741_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0(lean_object* v_00_u03b1_4743_, lean_object* v_name_4744_, lean_object* v_type_4745_, lean_object* v_val_4746_, lean_object* v_k_4747_, uint8_t v_nondep_4748_, uint8_t v_kind_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v___x_4762_; 
v___x_4762_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4744_, v_type_4745_, v_val_4746_, v_k_4747_, v_nondep_4748_, v_kind_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_4763_ = _args[0];
lean_object* v_name_4764_ = _args[1];
lean_object* v_type_4765_ = _args[2];
lean_object* v_val_4766_ = _args[3];
lean_object* v_k_4767_ = _args[4];
lean_object* v_nondep_4768_ = _args[5];
lean_object* v_kind_4769_ = _args[6];
lean_object* v___y_4770_ = _args[7];
lean_object* v___y_4771_ = _args[8];
lean_object* v___y_4772_ = _args[9];
lean_object* v___y_4773_ = _args[10];
lean_object* v___y_4774_ = _args[11];
lean_object* v___y_4775_ = _args[12];
lean_object* v___y_4776_ = _args[13];
lean_object* v___y_4777_ = _args[14];
lean_object* v___y_4778_ = _args[15];
lean_object* v___y_4779_ = _args[16];
lean_object* v___y_4780_ = _args[17];
lean_object* v___y_4781_ = _args[18];
_start:
{
uint8_t v_nondep_boxed_4782_; uint8_t v_kind_boxed_4783_; lean_object* v_res_4784_; 
v_nondep_boxed_4782_ = lean_unbox(v_nondep_4768_);
v_kind_boxed_4783_ = lean_unbox(v_kind_4769_);
v_res_4784_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0(v_00_u03b1_4763_, v_name_4764_, v_type_4765_, v_val_4766_, v_k_4767_, v_nondep_boxed_4782_, v_kind_boxed_4783_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec(v___y_4772_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0___boxed(lean_object* v_acc_4785_, lean_object* v_declInfos_4786_, lean_object* v_k_4787_, lean_object* v_fv_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
lean_object* v_res_4801_; 
v_res_4801_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0(v_acc_4785_, v_declInfos_4786_, v_k_4787_, v_fv_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec(v___y_4793_);
lean_dec_ref(v___y_4792_);
lean_dec(v___y_4791_);
lean_dec(v___y_4790_);
lean_dec_ref(v___y_4789_);
return v_res_4801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(lean_object* v_declInfos_4802_, lean_object* v_k_4803_, lean_object* v_acc_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_){
_start:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; uint8_t v___x_4819_; 
v___x_4817_ = lean_array_get_size(v_acc_4804_);
v___x_4818_ = lean_array_get_size(v_declInfos_4802_);
v___x_4819_ = lean_nat_dec_lt(v___x_4817_, v___x_4818_);
if (v___x_4819_ == 0)
{
lean_object* v___x_4820_; 
lean_dec_ref(v_declInfos_4802_);
lean_inc(v_a_4815_);
lean_inc_ref(v_a_4814_);
lean_inc(v_a_4813_);
lean_inc_ref(v_a_4812_);
lean_inc(v_a_4811_);
lean_inc_ref(v_a_4810_);
lean_inc(v_a_4809_);
lean_inc_ref(v_a_4808_);
lean_inc(v_a_4807_);
lean_inc(v_a_4806_);
lean_inc_ref(v_a_4805_);
v___x_4820_ = lean_apply_13(v_k_4803_, v_acc_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, lean_box(0));
return v___x_4820_;
}
else
{
lean_object* v___x_4821_; lean_object* v_snd_4822_; lean_object* v_fst_4823_; lean_object* v_fst_4824_; lean_object* v_snd_4825_; lean_object* v___f_4826_; uint8_t v___x_4827_; uint8_t v___x_4828_; lean_object* v___x_4829_; 
v___x_4821_ = lean_array_fget_borrowed(v_declInfos_4802_, v___x_4817_);
v_snd_4822_ = lean_ctor_get(v___x_4821_, 1);
v_fst_4823_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_fst_4823_);
v_fst_4824_ = lean_ctor_get(v_snd_4822_, 0);
lean_inc(v_fst_4824_);
v_snd_4825_ = lean_ctor_get(v_snd_4822_, 1);
lean_inc(v_snd_4825_);
v___f_4826_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4826_, 0, v_acc_4804_);
lean_closure_set(v___f_4826_, 1, v_declInfos_4802_);
lean_closure_set(v___f_4826_, 2, v_k_4803_);
v___x_4827_ = 0;
v___x_4828_ = 0;
v___x_4829_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_fst_4823_, v_fst_4824_, v_snd_4825_, v___f_4826_, v___x_4827_, v___x_4828_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_);
return v___x_4829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___lam__0(lean_object* v_acc_4830_, lean_object* v_declInfos_4831_, lean_object* v_k_4832_, lean_object* v_fv_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = lean_array_push(v_acc_4830_, v_fv_4833_);
v___x_4847_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4831_, v_k_4832_, v___x_4846_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop___boxed(lean_object* v_declInfos_4848_, lean_object* v_k_4849_, lean_object* v_acc_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4848_, v_k_4849_, v_acc_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_);
lean_dec(v_a_4861_);
lean_dec_ref(v_a_4860_);
lean_dec(v_a_4859_);
lean_dec_ref(v_a_4858_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_match__1_splitter___redArg(lean_object* v_x_4864_, lean_object* v_h__1_4865_){
_start:
{
lean_object* v_snd_4866_; lean_object* v_fst_4867_; lean_object* v_fst_4868_; lean_object* v_snd_4869_; lean_object* v___x_4870_; 
v_snd_4866_ = lean_ctor_get(v_x_4864_, 1);
lean_inc(v_snd_4866_);
v_fst_4867_ = lean_ctor_get(v_x_4864_, 0);
lean_inc(v_fst_4867_);
lean_dec_ref(v_x_4864_);
v_fst_4868_ = lean_ctor_get(v_snd_4866_, 0);
lean_inc(v_fst_4868_);
v_snd_4869_ = lean_ctor_get(v_snd_4866_, 1);
lean_inc(v_snd_4869_);
lean_dec(v_snd_4866_);
v___x_4870_ = lean_apply_3(v_h__1_4865_, v_fst_4867_, v_fst_4868_, v_snd_4869_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop_match__1_splitter(lean_object* v_motive_4871_, lean_object* v_x_4872_, lean_object* v_h__1_4873_){
_start:
{
lean_object* v_snd_4874_; lean_object* v_fst_4875_; lean_object* v_fst_4876_; lean_object* v_snd_4877_; lean_object* v___x_4878_; 
v_snd_4874_ = lean_ctor_get(v_x_4872_, 1);
lean_inc(v_snd_4874_);
v_fst_4875_ = lean_ctor_get(v_x_4872_, 0);
lean_inc(v_fst_4875_);
lean_dec_ref(v_x_4872_);
v_fst_4876_ = lean_ctor_get(v_snd_4874_, 0);
lean_inc(v_fst_4876_);
v_snd_4877_ = lean_ctor_get(v_snd_4874_, 1);
lean_inc(v_snd_4877_);
lean_dec(v_snd_4874_);
v___x_4878_ = lean_apply_3(v_h__1_4873_, v_fst_4875_, v_fst_4876_, v_snd_4877_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND(lean_object* v_declInfos_4881_, lean_object* v_k_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_){
_start:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___closed__0));
v___x_4896_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_declInfos_4881_, v_k_4882_, v___x_4895_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND___boxed(lean_object* v_declInfos_4897_, lean_object* v_k_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND(v_declInfos_4897_, v_k_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
lean_dec(v_a_4909_);
lean_dec_ref(v_a_4908_);
lean_dec(v_a_4907_);
lean_dec_ref(v_a_4906_);
lean_dec(v_a_4905_);
lean_dec_ref(v_a_4904_);
lean_dec(v_a_4903_);
lean_dec_ref(v_a_4902_);
lean_dec(v_a_4901_);
lean_dec(v_a_4900_);
lean_dec_ref(v_a_4899_);
return v_res_4911_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0(lean_object* v_x_4912_){
_start:
{
uint8_t v___x_4913_; 
v___x_4913_ = 0;
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0___boxed(lean_object* v_x_4914_){
_start:
{
uint8_t v_res_4915_; lean_object* v_r_4916_; 
v_res_4915_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__0(v_x_4914_);
lean_dec(v_x_4914_);
v_r_4916_ = lean_box(v_res_4915_);
return v_r_4916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1(lean_object* v_frameStx_4917_, lean_object* v___x_4918_, uint8_t v___x_4919_, lean_object* v___x_4920_, lean_object* v_fvs_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_){
_start:
{
lean_object* v___x_4929_; 
v___x_4929_ = l_Lean_Elab_Term_elabTermEnsuringType(v_frameStx_4917_, v___x_4918_, v___x_4919_, v___x_4919_, v___x_4920_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; uint8_t v___x_4931_; lean_object* v___x_4932_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_a_4930_);
lean_dec_ref_known(v___x_4929_, 1);
v___x_4931_ = 0;
v___x_4932_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4931_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_);
if (lean_obj_tag(v___x_4932_) == 0)
{
uint8_t v___x_4933_; lean_object* v___x_4934_; 
lean_dec_ref_known(v___x_4932_, 1);
v___x_4933_ = 1;
v___x_4934_ = l_Lean_Meta_mkLetFVars(v_fvs_4921_, v_a_4930_, v___x_4919_, v___x_4919_, v___x_4933_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_);
return v___x_4934_;
}
else
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4942_; 
lean_dec(v_a_4930_);
v_a_4935_ = lean_ctor_get(v___x_4932_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4932_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4937_ = v___x_4932_;
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v___x_4932_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4940_; 
if (v_isShared_4938_ == 0)
{
v___x_4940_ = v___x_4937_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_a_4935_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
}
else
{
return v___x_4929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1___boxed(lean_object* v_frameStx_4943_, lean_object* v___x_4944_, lean_object* v___x_4945_, lean_object* v___x_4946_, lean_object* v_fvs_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
uint8_t v___x_13346__boxed_4955_; lean_object* v_res_4956_; 
v___x_13346__boxed_4955_ = lean_unbox(v___x_4945_);
v_res_4956_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1(v_frameStx_4943_, v___x_4944_, v___x_13346__boxed_4955_, v___x_4946_, v_fvs_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_);
lean_dec(v___y_4953_);
lean_dec_ref(v___y_4952_);
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
lean_dec_ref(v_fvs_4947_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2(lean_object* v_resourceTy_4962_, lean_object* v_frameStx_4963_, lean_object* v___f_4964_, lean_object* v_fvs_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_){
_start:
{
lean_object* v___x_4978_; uint8_t v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___f_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4978_, 0, v_resourceTy_4962_);
v___x_4979_ = 1;
v___x_4980_ = lean_box(0);
v___x_4981_ = lean_box(v___x_4979_);
v___f_4982_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4982_, 0, v_frameStx_4963_);
lean_closure_set(v___f_4982_, 1, v___x_4978_);
lean_closure_set(v___f_4982_, 2, v___x_4981_);
lean_closure_set(v___f_4982_, 3, v___x_4980_);
lean_closure_set(v___f_4982_, 4, v_fvs_4965_);
v___x_4983_ = lean_box(0);
v___x_4984_ = lean_box(1);
v___x_4985_ = 0;
v___x_4986_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__0));
v___x_4987_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_4987_, 0, v___x_4980_);
lean_ctor_set(v___x_4987_, 1, v___x_4983_);
lean_ctor_set(v___x_4987_, 2, v___x_4980_);
lean_ctor_set(v___x_4987_, 3, v___f_4964_);
lean_ctor_set(v___x_4987_, 4, v___x_4984_);
lean_ctor_set(v___x_4987_, 5, v___x_4984_);
lean_ctor_set(v___x_4987_, 6, v___x_4980_);
lean_ctor_set(v___x_4987_, 7, v___x_4986_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*8, v___x_4979_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*8 + 1, v___x_4979_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*8 + 2, v___x_4979_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*8 + 3, v___x_4979_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*8 + 4, v___x_4985_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*8 + 5, v___x_4985_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*8 + 6, v___x_4985_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*8 + 7, v___x_4985_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*8 + 8, v___x_4979_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*8 + 9, v___x_4985_);
v___x_4988_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___closed__1));
v___x_4989_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_4982_, v___x_4987_, v___x_4988_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v_a_4990_; lean_object* v_fst_4991_; lean_object* v___x_4992_; 
v_a_4990_ = lean_ctor_get(v___x_4989_, 0);
lean_inc(v_a_4990_);
lean_dec_ref_known(v___x_4989_, 1);
v_fst_4991_ = lean_ctor_get(v_a_4990_, 0);
lean_inc(v_fst_4991_);
lean_dec(v_a_4990_);
v___x_4992_ = l_Lean_Meta_Sym_instantiateMVarsS(v_fst_4991_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
return v___x_4992_;
}
else
{
lean_object* v_a_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5000_; 
v_a_4993_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4995_ = v___x_4989_;
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4989_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4996_ == 0)
{
v___x_4998_ = v___x_4995_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___boxed(lean_object* v_resourceTy_5001_, lean_object* v_frameStx_5002_, lean_object* v___f_5003_, lean_object* v_fvs_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_){
_start:
{
lean_object* v_res_5017_; 
v_res_5017_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2(v_resourceTy_5001_, v_frameStx_5002_, v___f_5003_, v_fvs_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_);
lean_dec(v___y_5015_);
lean_dec_ref(v___y_5014_);
lean_dec(v___y_5013_);
lean_dec_ref(v___y_5012_);
lean_dec(v___y_5011_);
lean_dec_ref(v___y_5010_);
lean_dec(v___y_5009_);
lean_dec_ref(v___y_5008_);
lean_dec(v___y_5007_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(lean_object* v_as_5018_, size_t v_sz_5019_, size_t v_i_5020_, lean_object* v_b_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
lean_object* v_a_5028_; uint8_t v___x_5032_; 
v___x_5032_ = lean_usize_dec_lt(v_i_5020_, v_sz_5019_);
if (v___x_5032_ == 0)
{
lean_object* v___x_5033_; 
v___x_5033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5033_, 0, v_b_5021_);
return v___x_5033_;
}
else
{
lean_object* v_snd_5034_; lean_object* v_fst_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5081_; 
v_snd_5034_ = lean_ctor_get(v_b_5021_, 1);
v_fst_5035_ = lean_ctor_get(v_b_5021_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v_b_5021_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5037_ = v_b_5021_;
v_isShared_5038_ = v_isSharedCheck_5081_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_snd_5034_);
lean_inc(v_fst_5035_);
lean_dec(v_b_5021_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5081_;
goto v_resetjp_5036_;
}
v_resetjp_5036_:
{
lean_object* v_array_5039_; lean_object* v_start_5040_; lean_object* v_stop_5041_; uint8_t v___x_5042_; 
v_array_5039_ = lean_ctor_get(v_snd_5034_, 0);
v_start_5040_ = lean_ctor_get(v_snd_5034_, 1);
v_stop_5041_ = lean_ctor_get(v_snd_5034_, 2);
v___x_5042_ = lean_nat_dec_lt(v_start_5040_, v_stop_5041_);
if (v___x_5042_ == 0)
{
lean_object* v___x_5044_; 
if (v_isShared_5038_ == 0)
{
v___x_5044_ = v___x_5037_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_fst_5035_);
lean_ctor_set(v_reuseFailAlloc_5046_, 1, v_snd_5034_);
v___x_5044_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
lean_object* v___x_5045_; 
v___x_5045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5044_);
return v___x_5045_;
}
}
else
{
lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5077_; 
lean_inc(v_stop_5041_);
lean_inc(v_start_5040_);
lean_inc_ref(v_array_5039_);
v_isSharedCheck_5077_ = !lean_is_exclusive(v_snd_5034_);
if (v_isSharedCheck_5077_ == 0)
{
lean_object* v_unused_5078_; lean_object* v_unused_5079_; lean_object* v_unused_5080_; 
v_unused_5078_ = lean_ctor_get(v_snd_5034_, 2);
lean_dec(v_unused_5078_);
v_unused_5079_ = lean_ctor_get(v_snd_5034_, 1);
lean_dec(v_unused_5079_);
v_unused_5080_ = lean_ctor_get(v_snd_5034_, 0);
lean_dec(v_unused_5080_);
v___x_5048_ = v_snd_5034_;
v_isShared_5049_ = v_isSharedCheck_5077_;
goto v_resetjp_5047_;
}
else
{
lean_dec(v_snd_5034_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5077_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v_a_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5055_; 
v_a_5050_ = lean_array_uget_borrowed(v_as_5018_, v_i_5020_);
v___x_5051_ = lean_array_fget(v_array_5039_, v_start_5040_);
v___x_5052_ = lean_unsigned_to_nat(1u);
v___x_5053_ = lean_nat_add(v_start_5040_, v___x_5052_);
lean_dec(v_start_5040_);
if (v_isShared_5049_ == 0)
{
lean_ctor_set(v___x_5048_, 1, v___x_5053_);
v___x_5055_ = v___x_5048_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_array_5039_);
lean_ctor_set(v_reuseFailAlloc_5076_, 1, v___x_5053_);
lean_ctor_set(v_reuseFailAlloc_5076_, 2, v_stop_5041_);
v___x_5055_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
if (lean_obj_tag(v_a_5050_) == 1)
{
lean_object* v_val_5056_; lean_object* v___x_5057_; 
v_val_5056_ = lean_ctor_get(v_a_5050_, 0);
lean_inc(v___y_5025_);
lean_inc_ref(v___y_5024_);
lean_inc(v___y_5023_);
lean_inc_ref(v___y_5022_);
lean_inc(v___x_5051_);
v___x_5057_ = lean_infer_type(v___x_5051_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; lean_object* v___x_5060_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
lean_dec_ref_known(v___x_5057_, 1);
if (v_isShared_5038_ == 0)
{
lean_ctor_set(v___x_5037_, 1, v___x_5051_);
lean_ctor_set(v___x_5037_, 0, v_a_5058_);
v___x_5060_ = v___x_5037_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
lean_ctor_set(v_reuseFailAlloc_5064_, 1, v___x_5051_);
v___x_5060_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
lean_inc(v_val_5056_);
v___x_5061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5061_, 0, v_val_5056_);
lean_ctor_set(v___x_5061_, 1, v___x_5060_);
v___x_5062_ = lean_array_push(v_fst_5035_, v___x_5061_);
v___x_5063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5062_);
lean_ctor_set(v___x_5063_, 1, v___x_5055_);
v_a_5028_ = v___x_5063_;
goto v___jp_5027_;
}
}
else
{
lean_object* v_a_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5072_; 
lean_dec_ref(v___x_5055_);
lean_dec(v___x_5051_);
lean_del_object(v___x_5037_);
lean_dec(v_fst_5035_);
v_a_5065_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5067_ = v___x_5057_;
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v___x_5057_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_5068_ == 0)
{
v___x_5070_ = v___x_5067_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5065_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
else
{
lean_object* v___x_5074_; 
lean_dec(v___x_5051_);
if (v_isShared_5038_ == 0)
{
lean_ctor_set(v___x_5037_, 1, v___x_5055_);
v___x_5074_ = v___x_5037_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_fst_5035_);
lean_ctor_set(v_reuseFailAlloc_5075_, 1, v___x_5055_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
v_a_5028_ = v___x_5074_;
goto v___jp_5027_;
}
}
}
}
}
}
}
v___jp_5027_:
{
size_t v___x_5029_; size_t v___x_5030_; 
v___x_5029_ = ((size_t)1ULL);
v___x_5030_ = lean_usize_add(v_i_5020_, v___x_5029_);
v_i_5020_ = v___x_5030_;
v_b_5021_ = v_a_5028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg___boxed(lean_object* v_as_5082_, lean_object* v_sz_5083_, lean_object* v_i_5084_, lean_object* v_b_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_){
_start:
{
size_t v_sz_boxed_5091_; size_t v_i_boxed_5092_; lean_object* v_res_5093_; 
v_sz_boxed_5091_ = lean_unbox_usize(v_sz_5083_);
lean_dec(v_sz_5083_);
v_i_boxed_5092_ = lean_unbox_usize(v_i_5084_);
lean_dec(v_i_5084_);
v_res_5093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_as_5082_, v_sz_boxed_5091_, v_i_boxed_5092_, v_b_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_);
lean_dec(v___y_5089_);
lean_dec_ref(v___y_5088_);
lean_dec(v___y_5087_);
lean_dec_ref(v___y_5086_);
lean_dec_ref(v_as_5082_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(lean_object* v_resourceTy_5097_, lean_object* v_entry_5098_, lean_object* v_res_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v___y_5113_; lean_object* v_args_5122_; lean_object* v_varNames_5123_; lean_object* v_frameStx_5124_; lean_object* v___x_5125_; lean_object* v_decls_5126_; lean_object* v___x_5127_; lean_object* v___f_5128_; lean_object* v___f_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; size_t v_sz_5132_; size_t v___x_5133_; lean_object* v___x_5134_; 
v_args_5122_ = lean_ctor_get(v_res_5099_, 1);
lean_inc_ref(v_args_5122_);
lean_dec_ref(v_res_5099_);
v_varNames_5123_ = lean_ctor_get(v_entry_5098_, 1);
lean_inc_ref(v_varNames_5123_);
v_frameStx_5124_ = lean_ctor_get(v_entry_5098_, 2);
lean_inc(v_frameStx_5124_);
lean_dec_ref(v_entry_5098_);
v___x_5125_ = lean_unsigned_to_nat(0u);
v_decls_5126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__0));
v___x_5127_ = lean_array_get_size(v_args_5122_);
v___f_5128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___closed__1));
v___f_5129_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___lam__2___boxed), 16, 3);
lean_closure_set(v___f_5129_, 0, v_resourceTy_5097_);
lean_closure_set(v___f_5129_, 1, v_frameStx_5124_);
lean_closure_set(v___f_5129_, 2, v___f_5128_);
v___x_5130_ = l_Array_toSubarray___redArg(v_args_5122_, v___x_5125_, v___x_5127_);
v___x_5131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5131_, 0, v_decls_5126_);
lean_ctor_set(v___x_5131_, 1, v___x_5130_);
v_sz_5132_ = lean_array_size(v_varNames_5123_);
v___x_5133_ = ((size_t)0ULL);
v___x_5134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_varNames_5123_, v_sz_5132_, v___x_5133_, v___x_5131_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
lean_dec_ref(v_varNames_5123_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; lean_object* v_fst_5136_; lean_object* v___x_5137_; uint8_t v_transparency_5138_; uint8_t v___x_5139_; uint8_t v___x_5140_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5134_, 1);
v_fst_5136_ = lean_ctor_get(v_a_5135_, 0);
lean_inc(v_fst_5136_);
lean_dec(v_a_5135_);
v___x_5137_ = l_Lean_Meta_Context_config(v_a_5107_);
v_transparency_5138_ = lean_ctor_get_uint8(v___x_5137_, 9);
lean_dec_ref(v___x_5137_);
v___x_5139_ = 1;
v___x_5140_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_5138_, v___x_5139_);
if (v___x_5140_ == 0)
{
lean_object* v_keyedConfig_5141_; uint8_t v_trackZetaDelta_5142_; lean_object* v_zetaDeltaSet_5143_; lean_object* v_lctx_5144_; lean_object* v_localInstances_5145_; lean_object* v_defEqCtx_x3f_5146_; lean_object* v_synthPendingDepth_5147_; lean_object* v_customCanUnfoldPredicate_x3f_5148_; uint8_t v_univApprox_5149_; uint8_t v_inTypeClassResolution_5150_; uint8_t v_cacheInferType_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; 
v_keyedConfig_5141_ = lean_ctor_get(v_a_5107_, 0);
v_trackZetaDelta_5142_ = lean_ctor_get_uint8(v_a_5107_, sizeof(void*)*7);
v_zetaDeltaSet_5143_ = lean_ctor_get(v_a_5107_, 1);
v_lctx_5144_ = lean_ctor_get(v_a_5107_, 2);
v_localInstances_5145_ = lean_ctor_get(v_a_5107_, 3);
v_defEqCtx_x3f_5146_ = lean_ctor_get(v_a_5107_, 4);
v_synthPendingDepth_5147_ = lean_ctor_get(v_a_5107_, 5);
v_customCanUnfoldPredicate_x3f_5148_ = lean_ctor_get(v_a_5107_, 6);
v_univApprox_5149_ = lean_ctor_get_uint8(v_a_5107_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5150_ = lean_ctor_get_uint8(v_a_5107_, sizeof(void*)*7 + 2);
v_cacheInferType_5151_ = lean_ctor_get_uint8(v_a_5107_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_5141_);
v___x_5152_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_5139_, v_keyedConfig_5141_);
lean_inc(v_customCanUnfoldPredicate_x3f_5148_);
lean_inc(v_synthPendingDepth_5147_);
lean_inc(v_defEqCtx_x3f_5146_);
lean_inc_ref(v_localInstances_5145_);
lean_inc_ref(v_lctx_5144_);
lean_inc(v_zetaDeltaSet_5143_);
v___x_5153_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5153_, 0, v___x_5152_);
lean_ctor_set(v___x_5153_, 1, v_zetaDeltaSet_5143_);
lean_ctor_set(v___x_5153_, 2, v_lctx_5144_);
lean_ctor_set(v___x_5153_, 3, v_localInstances_5145_);
lean_ctor_set(v___x_5153_, 4, v_defEqCtx_x3f_5146_);
lean_ctor_set(v___x_5153_, 5, v_synthPendingDepth_5147_);
lean_ctor_set(v___x_5153_, 6, v_customCanUnfoldPredicate_x3f_5148_);
lean_ctor_set_uint8(v___x_5153_, sizeof(void*)*7, v_trackZetaDelta_5142_);
lean_ctor_set_uint8(v___x_5153_, sizeof(void*)*7 + 1, v_univApprox_5149_);
lean_ctor_set_uint8(v___x_5153_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5150_);
lean_ctor_set_uint8(v___x_5153_, sizeof(void*)*7 + 3, v_cacheInferType_5151_);
v___x_5154_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_fst_5136_, v___f_5129_, v_decls_5126_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v___x_5153_, v_a_5108_, v_a_5109_, v_a_5110_);
lean_dec_ref_known(v___x_5153_, 7);
v___y_5113_ = v___x_5154_;
goto v___jp_5112_;
}
else
{
lean_object* v___x_5155_; 
v___x_5155_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_withLetDeclsDND_loop(v_fst_5136_, v___f_5129_, v_decls_5126_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
v___y_5113_ = v___x_5155_;
goto v___jp_5112_;
}
}
else
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
lean_dec_ref(v___f_5129_);
v_a_5156_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5134_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5134_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
v___jp_5112_:
{
if (lean_obj_tag(v___y_5113_) == 0)
{
return v___y_5113_;
}
else
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
v_a_5114_ = lean_ctor_get(v___y_5113_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___y_5113_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___y_5113_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___y_5113_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame___boxed(lean_object* v_resourceTy_5164_, lean_object* v_entry_5165_, lean_object* v_res_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(v_resourceTy_5164_, v_entry_5165_, v_res_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_);
lean_dec(v_a_5177_);
lean_dec_ref(v_a_5176_);
lean_dec(v_a_5175_);
lean_dec_ref(v_a_5174_);
lean_dec(v_a_5173_);
lean_dec_ref(v_a_5172_);
lean_dec(v_a_5171_);
lean_dec_ref(v_a_5170_);
lean_dec(v_a_5169_);
lean_dec(v_a_5168_);
lean_dec_ref(v_a_5167_);
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0(lean_object* v_as_5180_, size_t v_sz_5181_, size_t v_i_5182_, lean_object* v_b_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_){
_start:
{
lean_object* v___x_5196_; 
v___x_5196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___redArg(v_as_5180_, v_sz_5181_, v_i_5182_, v_b_5183_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
return v___x_5196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0___boxed(lean_object* v_as_5197_, lean_object* v_sz_5198_, lean_object* v_i_5199_, lean_object* v_b_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_){
_start:
{
size_t v_sz_boxed_5213_; size_t v_i_boxed_5214_; lean_object* v_res_5215_; 
v_sz_boxed_5213_ = lean_unbox_usize(v_sz_5198_);
lean_dec(v_sz_5198_);
v_i_boxed_5214_ = lean_unbox_usize(v_i_5199_);
lean_dec(v_i_5199_);
v_res_5215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame_spec__0(v_as_5197_, v_sz_boxed_5213_, v_i_boxed_5214_, v_b_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_);
lean_dec(v___y_5211_);
lean_dec_ref(v___y_5210_);
lean_dec(v___y_5209_);
lean_dec_ref(v___y_5208_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
lean_dec(v___y_5203_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
lean_dec_ref(v_as_5197_);
return v_res_5215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(lean_object* v___x_5216_, lean_object* v___x_5217_, lean_object* v_as_5218_, size_t v_sz_5219_, size_t v_i_5220_, lean_object* v_b_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
lean_object* v_a_5230_; uint8_t v___x_5234_; 
v___x_5234_ = lean_usize_dec_lt(v_i_5220_, v_sz_5219_);
if (v___x_5234_ == 0)
{
lean_object* v___x_5235_; 
lean_dec_ref(v___x_5217_);
v___x_5235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5235_, 0, v_b_5221_);
return v___x_5235_;
}
else
{
lean_object* v___x_5236_; lean_object* v_a_5237_; lean_object* v___x_5238_; uint8_t v_retired_5239_; 
v___x_5236_ = l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default;
v_a_5237_ = lean_array_uget_borrowed(v_as_5218_, v_i_5220_);
v___x_5238_ = lean_array_get_borrowed(v___x_5236_, v___x_5216_, v_a_5237_);
v_retired_5239_ = lean_ctor_get_uint8(v___x_5238_, sizeof(void*)*4);
if (v_retired_5239_ == 0)
{
lean_object* v_pat_5240_; lean_object* v_srcIdx_5241_; lean_object* v___x_5242_; 
v_pat_5240_ = lean_ctor_get(v___x_5238_, 0);
v_srcIdx_5241_ = lean_ctor_get(v___x_5238_, 3);
lean_inc_ref(v___x_5217_);
lean_inc_ref(v_pat_5240_);
v___x_5242_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pat_5240_, v___x_5217_, v___x_5234_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v_a_5243_; 
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
lean_inc(v_a_5243_);
lean_dec_ref_known(v___x_5242_, 1);
if (lean_obj_tag(v_a_5243_) == 1)
{
if (lean_obj_tag(v_b_5221_) == 0)
{
lean_object* v_val_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5252_; 
v_val_5244_ = lean_ctor_get(v_a_5243_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v_a_5243_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5246_ = v_a_5243_;
v_isShared_5247_ = v_isSharedCheck_5252_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_val_5244_);
lean_dec(v_a_5243_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5252_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v___x_5248_; lean_object* v___x_5250_; 
lean_inc(v___x_5238_);
v___x_5248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5238_);
lean_ctor_set(v___x_5248_, 1, v_val_5244_);
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 0, v___x_5248_);
v___x_5250_ = v___x_5246_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v___x_5248_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
v_a_5230_ = v___x_5250_;
goto v___jp_5229_;
}
}
}
else
{
lean_object* v_val_5253_; lean_object* v_fst_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5272_; 
v_val_5253_ = lean_ctor_get(v_b_5221_, 0);
lean_inc(v_val_5253_);
v_fst_5254_ = lean_ctor_get(v_val_5253_, 0);
v_isSharedCheck_5272_ = !lean_is_exclusive(v_val_5253_);
if (v_isSharedCheck_5272_ == 0)
{
lean_object* v_unused_5273_; 
v_unused_5273_ = lean_ctor_get(v_val_5253_, 1);
lean_dec(v_unused_5273_);
v___x_5256_ = v_val_5253_;
v_isShared_5257_ = v_isSharedCheck_5272_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_fst_5254_);
lean_dec(v_val_5253_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5272_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v_val_5258_; lean_object* v_srcIdx_5259_; uint8_t v___x_5260_; 
v_val_5258_ = lean_ctor_get(v_a_5243_, 0);
lean_inc(v_val_5258_);
lean_dec_ref_known(v_a_5243_, 1);
v_srcIdx_5259_ = lean_ctor_get(v_fst_5254_, 3);
lean_inc(v_srcIdx_5259_);
lean_dec(v_fst_5254_);
v___x_5260_ = lean_nat_dec_lt(v_srcIdx_5241_, v_srcIdx_5259_);
lean_dec(v_srcIdx_5259_);
if (v___x_5260_ == 0)
{
lean_dec(v_val_5258_);
lean_del_object(v___x_5256_);
v_a_5230_ = v_b_5221_;
goto v___jp_5229_;
}
else
{
lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5270_; 
v_isSharedCheck_5270_ = !lean_is_exclusive(v_b_5221_);
if (v_isSharedCheck_5270_ == 0)
{
lean_object* v_unused_5271_; 
v_unused_5271_ = lean_ctor_get(v_b_5221_, 0);
lean_dec(v_unused_5271_);
v___x_5262_ = v_b_5221_;
v_isShared_5263_ = v_isSharedCheck_5270_;
goto v_resetjp_5261_;
}
else
{
lean_dec(v_b_5221_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5270_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
lean_inc(v___x_5238_);
if (v_isShared_5257_ == 0)
{
lean_ctor_set(v___x_5256_, 1, v_val_5258_);
lean_ctor_set(v___x_5256_, 0, v___x_5238_);
v___x_5265_ = v___x_5256_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v___x_5238_);
lean_ctor_set(v_reuseFailAlloc_5269_, 1, v_val_5258_);
v___x_5265_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
lean_object* v___x_5267_; 
if (v_isShared_5263_ == 0)
{
lean_ctor_set(v___x_5262_, 0, v___x_5265_);
v___x_5267_ = v___x_5262_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v___x_5265_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
v_a_5230_ = v___x_5267_;
goto v___jp_5229_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_5243_);
v_a_5230_ = v_b_5221_;
goto v___jp_5229_;
}
}
else
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5281_; 
lean_dec(v_b_5221_);
lean_dec_ref(v___x_5217_);
v_a_5274_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5276_ = v___x_5242_;
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5242_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5279_; 
if (v_isShared_5277_ == 0)
{
v___x_5279_ = v___x_5276_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5274_);
v___x_5279_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
return v___x_5279_;
}
}
}
}
else
{
v_a_5230_ = v_b_5221_;
goto v___jp_5229_;
}
}
v___jp_5229_:
{
size_t v___x_5231_; size_t v___x_5232_; 
v___x_5231_ = ((size_t)1ULL);
v___x_5232_ = lean_usize_add(v_i_5220_, v___x_5231_);
v_i_5220_ = v___x_5232_;
v_b_5221_ = v_a_5230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object* v___x_5282_, lean_object* v___x_5283_, lean_object* v_as_5284_, lean_object* v_sz_5285_, lean_object* v_i_5286_, lean_object* v_b_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
size_t v_sz_boxed_5295_; size_t v_i_boxed_5296_; lean_object* v_res_5297_; 
v_sz_boxed_5295_ = lean_unbox_usize(v_sz_5285_);
lean_dec(v_sz_5285_);
v_i_boxed_5296_ = lean_unbox_usize(v_i_5286_);
lean_dec(v_i_5286_);
v_res_5297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v___x_5282_, v___x_5283_, v_as_5284_, v_sz_boxed_5295_, v_i_boxed_5296_, v_b_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
lean_dec(v___y_5291_);
lean_dec_ref(v___y_5290_);
lean_dec(v___y_5289_);
lean_dec_ref(v___y_5288_);
lean_dec_ref(v_as_5284_);
lean_dec_ref(v___x_5282_);
return v_res_5297_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1(void){
_start:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; 
v___x_5299_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__0));
v___x_5300_ = l_Lean_stringToMessageData(v___x_5299_);
return v___x_5300_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3(void){
_start:
{
lean_object* v___x_5302_; lean_object* v___x_5303_; 
v___x_5302_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__2));
v___x_5303_ = l_Lean_stringToMessageData(v___x_5302_);
return v___x_5303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(lean_object* v_fp_5304_, lean_object* v_info_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_){
_start:
{
lean_object* v___x_5318_; lean_object* v_frameDB_5319_; lean_object* v_tree_5320_; lean_object* v_entries_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5460_; 
v___x_5318_ = lean_st_ref_get(v_a_5307_);
v_frameDB_5319_ = lean_ctor_get(v___x_5318_, 4);
lean_inc_ref(v_frameDB_5319_);
lean_dec(v___x_5318_);
v_tree_5320_ = lean_ctor_get(v_frameDB_5319_, 0);
v_entries_5321_ = lean_ctor_get(v_frameDB_5319_, 1);
v_isSharedCheck_5460_ = !lean_is_exclusive(v_frameDB_5319_);
if (v_isSharedCheck_5460_ == 0)
{
v___x_5323_ = v_frameDB_5319_;
v_isShared_5324_ = v_isSharedCheck_5460_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_entries_5321_);
lean_inc(v_tree_5320_);
lean_dec(v_frameDB_5319_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5460_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5325_; lean_object* v___x_5326_; uint8_t v___x_5327_; 
v___x_5325_ = lean_array_get_size(v_entries_5321_);
v___x_5326_ = lean_unsigned_to_nat(0u);
v___x_5327_ = lean_nat_dec_eq(v___x_5325_, v___x_5326_);
if (v___x_5327_ == 0)
{
uint8_t v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v_mctx_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; size_t v_sz_5334_; size_t v___x_5335_; lean_object* v___x_5336_; 
v___x_5328_ = 1;
v___x_5329_ = lean_box(0);
v___x_5330_ = lean_st_ref_get(v_a_5314_);
v_mctx_5331_ = lean_ctor_get(v___x_5330_, 0);
lean_inc_ref(v_mctx_5331_);
lean_dec(v___x_5330_);
v___x_5332_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5305_);
v___x_5333_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_5331_, v_tree_5320_, v___x_5332_);
lean_dec_ref(v_tree_5320_);
lean_dec_ref(v_mctx_5331_);
v_sz_5334_ = lean_array_size(v___x_5333_);
v___x_5335_ = ((size_t)0ULL);
lean_inc_ref(v___x_5332_);
v___x_5336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v_entries_5321_, v___x_5332_, v___x_5333_, v_sz_5334_, v___x_5335_, v___x_5329_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_);
lean_dec_ref(v___x_5333_);
lean_dec_ref(v_entries_5321_);
if (lean_obj_tag(v___x_5336_) == 0)
{
lean_object* v_a_5337_; lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5449_; 
v_a_5337_ = lean_ctor_get(v___x_5336_, 0);
v_isSharedCheck_5449_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5449_ == 0)
{
v___x_5339_ = v___x_5336_;
v_isShared_5340_ = v_isSharedCheck_5449_;
goto v_resetjp_5338_;
}
else
{
lean_inc(v_a_5337_);
lean_dec(v___x_5336_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5449_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
if (lean_obj_tag(v_a_5337_) == 1)
{
lean_object* v_val_5341_; lean_object* v___x_5343_; uint8_t v_isShared_5344_; uint8_t v_isSharedCheck_5445_; 
lean_del_object(v___x_5339_);
v_val_5341_ = lean_ctor_get(v_a_5337_, 0);
v_isSharedCheck_5445_ = !lean_is_exclusive(v_a_5337_);
if (v_isSharedCheck_5445_ == 0)
{
v___x_5343_ = v_a_5337_;
v_isShared_5344_ = v_isSharedCheck_5445_;
goto v_resetjp_5342_;
}
else
{
lean_inc(v_val_5341_);
lean_dec(v_a_5337_);
v___x_5343_ = lean_box(0);
v_isShared_5344_ = v_isSharedCheck_5445_;
goto v_resetjp_5342_;
}
v_resetjp_5342_:
{
lean_object* v_fst_5345_; lean_object* v_snd_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5444_; 
v_fst_5345_ = lean_ctor_get(v_val_5341_, 0);
v_snd_5346_ = lean_ctor_get(v_val_5341_, 1);
v_isSharedCheck_5444_ = !lean_is_exclusive(v_val_5341_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5348_ = v_val_5341_;
v_isShared_5349_ = v_isSharedCheck_5444_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_snd_5346_);
lean_inc(v_fst_5345_);
lean_dec(v_val_5341_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5444_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5350_; lean_object* v_frameDB_5351_; lean_object* v_specBackwardRuleCache_5352_; lean_object* v_splitBackwardRuleCache_5353_; lean_object* v_latticeBackwardRuleCache_5354_; lean_object* v_frameBackwardRuleCache_5355_; lean_object* v_invariants_5356_; lean_object* v_vcs_5357_; lean_object* v_simpState_5358_; lean_object* v_fuel_5359_; lean_object* v_inlineHandledInvariants_5360_; lean_object* v_pendingJoinPoints_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5443_; 
v___x_5350_ = lean_st_ref_take(v_a_5307_);
v_frameDB_5351_ = lean_ctor_get(v___x_5350_, 4);
v_specBackwardRuleCache_5352_ = lean_ctor_get(v___x_5350_, 0);
v_splitBackwardRuleCache_5353_ = lean_ctor_get(v___x_5350_, 1);
v_latticeBackwardRuleCache_5354_ = lean_ctor_get(v___x_5350_, 2);
v_frameBackwardRuleCache_5355_ = lean_ctor_get(v___x_5350_, 3);
v_invariants_5356_ = lean_ctor_get(v___x_5350_, 5);
v_vcs_5357_ = lean_ctor_get(v___x_5350_, 6);
v_simpState_5358_ = lean_ctor_get(v___x_5350_, 7);
v_fuel_5359_ = lean_ctor_get(v___x_5350_, 8);
v_inlineHandledInvariants_5360_ = lean_ctor_get(v___x_5350_, 9);
v_pendingJoinPoints_5361_ = lean_ctor_get(v___x_5350_, 10);
v_isSharedCheck_5443_ = !lean_is_exclusive(v___x_5350_);
if (v_isSharedCheck_5443_ == 0)
{
v___x_5363_ = v___x_5350_;
v_isShared_5364_ = v_isSharedCheck_5443_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_pendingJoinPoints_5361_);
lean_inc(v_inlineHandledInvariants_5360_);
lean_inc(v_fuel_5359_);
lean_inc(v_simpState_5358_);
lean_inc(v_vcs_5357_);
lean_inc(v_invariants_5356_);
lean_inc(v_frameDB_5351_);
lean_inc(v_frameBackwardRuleCache_5355_);
lean_inc(v_latticeBackwardRuleCache_5354_);
lean_inc(v_splitBackwardRuleCache_5353_);
lean_inc(v_specBackwardRuleCache_5352_);
lean_dec(v___x_5350_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5443_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v_tree_5365_; lean_object* v_entries_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5442_; 
v_tree_5365_ = lean_ctor_get(v_frameDB_5351_, 0);
v_entries_5366_ = lean_ctor_get(v_frameDB_5351_, 1);
v_isSharedCheck_5442_ = !lean_is_exclusive(v_frameDB_5351_);
if (v_isSharedCheck_5442_ == 0)
{
v___x_5368_ = v_frameDB_5351_;
v_isShared_5369_ = v_isSharedCheck_5442_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_entries_5366_);
lean_inc(v_tree_5365_);
lean_dec(v_frameDB_5351_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5442_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
lean_object* v_pat_5370_; lean_object* v_varNames_5371_; lean_object* v_frameStx_5372_; lean_object* v_srcIdx_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5377_; 
v_pat_5370_ = lean_ctor_get(v_fst_5345_, 0);
v_varNames_5371_ = lean_ctor_get(v_fst_5345_, 1);
v_frameStx_5372_ = lean_ctor_get(v_fst_5345_, 2);
v_srcIdx_5373_ = lean_ctor_get(v_fst_5345_, 3);
lean_inc(v_srcIdx_5373_);
lean_inc(v_frameStx_5372_);
lean_inc_ref(v_varNames_5371_);
lean_inc_ref(v_pat_5370_);
v___x_5374_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_5374_, 0, v_pat_5370_);
lean_ctor_set(v___x_5374_, 1, v_varNames_5371_);
lean_ctor_set(v___x_5374_, 2, v_frameStx_5372_);
lean_ctor_set(v___x_5374_, 3, v_srcIdx_5373_);
lean_ctor_set_uint8(v___x_5374_, sizeof(void*)*4, v___x_5328_);
v___x_5375_ = lean_array_set(v_entries_5366_, v_srcIdx_5373_, v___x_5374_);
if (v_isShared_5369_ == 0)
{
lean_ctor_set(v___x_5368_, 1, v___x_5375_);
v___x_5377_ = v___x_5368_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v_tree_5365_);
lean_ctor_set(v_reuseFailAlloc_5441_, 1, v___x_5375_);
v___x_5377_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
lean_object* v___x_5379_; 
if (v_isShared_5364_ == 0)
{
lean_ctor_set(v___x_5363_, 4, v___x_5377_);
v___x_5379_ = v___x_5363_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_specBackwardRuleCache_5352_);
lean_ctor_set(v_reuseFailAlloc_5440_, 1, v_splitBackwardRuleCache_5353_);
lean_ctor_set(v_reuseFailAlloc_5440_, 2, v_latticeBackwardRuleCache_5354_);
lean_ctor_set(v_reuseFailAlloc_5440_, 3, v_frameBackwardRuleCache_5355_);
lean_ctor_set(v_reuseFailAlloc_5440_, 4, v___x_5377_);
lean_ctor_set(v_reuseFailAlloc_5440_, 5, v_invariants_5356_);
lean_ctor_set(v_reuseFailAlloc_5440_, 6, v_vcs_5357_);
lean_ctor_set(v_reuseFailAlloc_5440_, 7, v_simpState_5358_);
lean_ctor_set(v_reuseFailAlloc_5440_, 8, v_fuel_5359_);
lean_ctor_set(v_reuseFailAlloc_5440_, 9, v_inlineHandledInvariants_5360_);
lean_ctor_set(v_reuseFailAlloc_5440_, 10, v_pendingJoinPoints_5361_);
v___x_5379_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
lean_object* v___x_5380_; lean_object* v_mkResourceTy_5381_; lean_object* v___x_5382_; 
v___x_5380_ = lean_st_ref_put(v_a_5307_, v___x_5379_);
v_mkResourceTy_5381_ = lean_ctor_get(v_fp_5304_, 3);
lean_inc_ref(v_mkResourceTy_5381_);
lean_dec_ref(v_fp_5304_);
lean_inc(v_a_5316_);
lean_inc_ref(v_a_5315_);
lean_inc(v_a_5314_);
lean_inc_ref(v_a_5313_);
v___x_5382_ = lean_apply_6(v_mkResourceTy_5381_, v_info_5305_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, lean_box(0));
if (lean_obj_tag(v___x_5382_) == 0)
{
lean_object* v_a_5383_; lean_object* v___x_5384_; 
v_a_5383_ = lean_ctor_get(v___x_5382_, 0);
lean_inc(v_a_5383_);
lean_dec_ref_known(v___x_5382_, 1);
v___x_5384_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_elabFrame(v_a_5383_, v_fst_5345_, v_snd_5346_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_);
if (lean_obj_tag(v___x_5384_) == 0)
{
lean_object* v_a_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5423_; 
v_a_5385_ = lean_ctor_get(v___x_5384_, 0);
v_isSharedCheck_5423_ = !lean_is_exclusive(v___x_5384_);
if (v_isSharedCheck_5423_ == 0)
{
v___x_5387_ = v___x_5384_;
v_isShared_5388_ = v_isSharedCheck_5423_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_a_5385_);
lean_dec(v___x_5384_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5423_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
lean_object* v_toCold_5396_; lean_object* v_options_5397_; uint8_t v_hasTrace_5398_; 
v_toCold_5396_ = lean_ctor_get(v_a_5315_, 0);
v_options_5397_ = lean_ctor_get(v_toCold_5396_, 2);
v_hasTrace_5398_ = lean_ctor_get_uint8(v_options_5397_, sizeof(void*)*1);
if (v_hasTrace_5398_ == 0)
{
lean_del_object(v___x_5348_);
lean_dec_ref(v___x_5332_);
lean_del_object(v___x_5323_);
goto v___jp_5389_;
}
else
{
lean_object* v_inheritedTraceOptions_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; uint8_t v___x_5402_; 
v_inheritedTraceOptions_5399_ = lean_ctor_get(v_toCold_5396_, 11);
v___x_5400_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_5401_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_5402_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5399_, v_options_5397_, v___x_5401_);
if (v___x_5402_ == 0)
{
lean_del_object(v___x_5348_);
lean_dec_ref(v___x_5332_);
lean_del_object(v___x_5323_);
goto v___jp_5389_;
}
else
{
lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5406_; 
v___x_5403_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1, &l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__1);
v___x_5404_ = l_Lean_MessageData_ofExpr(v___x_5332_);
if (v_isShared_5349_ == 0)
{
lean_ctor_set_tag(v___x_5348_, 7);
lean_ctor_set(v___x_5348_, 1, v___x_5404_);
lean_ctor_set(v___x_5348_, 0, v___x_5403_);
v___x_5406_ = v___x_5348_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5403_);
lean_ctor_set(v_reuseFailAlloc_5422_, 1, v___x_5404_);
v___x_5406_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
lean_object* v___x_5407_; lean_object* v___x_5409_; 
v___x_5407_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___closed__3);
if (v_isShared_5324_ == 0)
{
lean_ctor_set_tag(v___x_5323_, 7);
lean_ctor_set(v___x_5323_, 1, v___x_5407_);
lean_ctor_set(v___x_5323_, 0, v___x_5406_);
v___x_5409_ = v___x_5323_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v___x_5406_);
lean_ctor_set(v_reuseFailAlloc_5421_, 1, v___x_5407_);
v___x_5409_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; 
lean_inc(v_a_5385_);
v___x_5410_ = l_Lean_indentExpr(v_a_5385_);
v___x_5411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5409_);
lean_ctor_set(v___x_5411_, 1, v___x_5410_);
v___x_5412_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5400_, v___x_5411_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_);
if (lean_obj_tag(v___x_5412_) == 0)
{
lean_dec_ref_known(v___x_5412_, 1);
goto v___jp_5389_;
}
else
{
lean_object* v_a_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5420_; 
lean_del_object(v___x_5387_);
lean_dec(v_a_5385_);
lean_del_object(v___x_5343_);
v_a_5413_ = lean_ctor_get(v___x_5412_, 0);
v_isSharedCheck_5420_ = !lean_is_exclusive(v___x_5412_);
if (v_isSharedCheck_5420_ == 0)
{
v___x_5415_ = v___x_5412_;
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_a_5413_);
lean_dec(v___x_5412_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v___x_5418_; 
if (v_isShared_5416_ == 0)
{
v___x_5418_ = v___x_5415_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
v___x_5418_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
return v___x_5418_;
}
}
}
}
}
}
}
v___jp_5389_:
{
lean_object* v___x_5391_; 
if (v_isShared_5344_ == 0)
{
lean_ctor_set(v___x_5343_, 0, v_a_5385_);
v___x_5391_ = v___x_5343_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5385_);
v___x_5391_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
lean_object* v___x_5393_; 
if (v_isShared_5388_ == 0)
{
lean_ctor_set(v___x_5387_, 0, v___x_5391_);
v___x_5393_ = v___x_5387_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v___x_5391_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
return v___x_5393_;
}
}
}
}
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
lean_del_object(v___x_5348_);
lean_del_object(v___x_5343_);
lean_dec_ref(v___x_5332_);
lean_del_object(v___x_5323_);
v_a_5424_ = lean_ctor_get(v___x_5384_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5384_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5384_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5384_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
else
{
lean_object* v_a_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5439_; 
lean_del_object(v___x_5348_);
lean_dec(v_snd_5346_);
lean_dec(v_fst_5345_);
lean_del_object(v___x_5343_);
lean_dec_ref(v___x_5332_);
lean_del_object(v___x_5323_);
v_a_5432_ = lean_ctor_get(v___x_5382_, 0);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5382_);
if (v_isSharedCheck_5439_ == 0)
{
v___x_5434_ = v___x_5382_;
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_dec(v___x_5382_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v___x_5437_; 
if (v_isShared_5435_ == 0)
{
v___x_5437_ = v___x_5434_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_a_5432_);
v___x_5437_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
return v___x_5437_;
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
lean_object* v___x_5447_; 
lean_dec(v_a_5337_);
lean_dec_ref(v___x_5332_);
lean_del_object(v___x_5323_);
lean_dec_ref(v_info_5305_);
lean_dec_ref(v_fp_5304_);
if (v_isShared_5340_ == 0)
{
lean_ctor_set(v___x_5339_, 0, v___x_5329_);
v___x_5447_ = v___x_5339_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v___x_5329_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
}
}
else
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5457_; 
lean_dec_ref(v___x_5332_);
lean_del_object(v___x_5323_);
lean_dec_ref(v_info_5305_);
lean_dec_ref(v_fp_5304_);
v_a_5450_ = lean_ctor_get(v___x_5336_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5452_ = v___x_5336_;
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5336_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5455_; 
if (v_isShared_5453_ == 0)
{
v___x_5455_ = v___x_5452_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_a_5450_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
return v___x_5455_;
}
}
}
}
else
{
lean_object* v___x_5458_; lean_object* v___x_5459_; 
lean_del_object(v___x_5323_);
lean_dec_ref(v_entries_5321_);
lean_dec_ref(v_tree_5320_);
lean_dec_ref(v_info_5305_);
lean_dec_ref(v_fp_5304_);
v___x_5458_ = lean_box(0);
v___x_5459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5459_, 0, v___x_5458_);
return v___x_5459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_matchFrame_x3f___boxed(lean_object* v_fp_5461_, lean_object* v_info_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_){
_start:
{
lean_object* v_res_5475_; 
v_res_5475_ = l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(v_fp_5461_, v_info_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_);
lean_dec(v_a_5473_);
lean_dec_ref(v_a_5472_);
lean_dec(v_a_5471_);
lean_dec_ref(v_a_5470_);
lean_dec(v_a_5469_);
lean_dec_ref(v_a_5468_);
lean_dec(v_a_5467_);
lean_dec_ref(v_a_5466_);
lean_dec(v_a_5465_);
lean_dec(v_a_5464_);
lean_dec_ref(v_a_5463_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0(lean_object* v___x_5476_, lean_object* v___x_5477_, lean_object* v_as_5478_, size_t v_sz_5479_, size_t v_i_5480_, lean_object* v_b_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_){
_start:
{
lean_object* v___x_5494_; 
v___x_5494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___redArg(v___x_5476_, v___x_5477_, v_as_5478_, v_sz_5479_, v_i_5480_, v_b_5481_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_);
return v___x_5494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0___boxed(lean_object** _args){
lean_object* v___x_5495_ = _args[0];
lean_object* v___x_5496_ = _args[1];
lean_object* v_as_5497_ = _args[2];
lean_object* v_sz_5498_ = _args[3];
lean_object* v_i_5499_ = _args[4];
lean_object* v_b_5500_ = _args[5];
lean_object* v___y_5501_ = _args[6];
lean_object* v___y_5502_ = _args[7];
lean_object* v___y_5503_ = _args[8];
lean_object* v___y_5504_ = _args[9];
lean_object* v___y_5505_ = _args[10];
lean_object* v___y_5506_ = _args[11];
lean_object* v___y_5507_ = _args[12];
lean_object* v___y_5508_ = _args[13];
lean_object* v___y_5509_ = _args[14];
lean_object* v___y_5510_ = _args[15];
lean_object* v___y_5511_ = _args[16];
lean_object* v___y_5512_ = _args[17];
_start:
{
size_t v_sz_boxed_5513_; size_t v_i_boxed_5514_; lean_object* v_res_5515_; 
v_sz_boxed_5513_ = lean_unbox_usize(v_sz_5498_);
lean_dec(v_sz_5498_);
v_i_boxed_5514_ = lean_unbox_usize(v_i_5499_);
lean_dec(v_i_5499_);
v_res_5515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_matchFrame_x3f_spec__0(v___x_5495_, v___x_5496_, v_as_5497_, v_sz_boxed_5513_, v_i_boxed_5514_, v_b_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_);
lean_dec(v___y_5511_);
lean_dec_ref(v___y_5510_);
lean_dec(v___y_5509_);
lean_dec_ref(v___y_5508_);
lean_dec(v___y_5507_);
lean_dec_ref(v___y_5506_);
lean_dec(v___y_5505_);
lean_dec_ref(v___y_5504_);
lean_dec(v___y_5503_);
lean_dec(v___y_5502_);
lean_dec_ref(v___y_5501_);
lean_dec_ref(v_as_5497_);
lean_dec_ref(v___x_5495_);
return v_res_5515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1___redArg(lean_object* v_f_5516_, lean_object* v_a_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_){
_start:
{
lean_object* v___y_5526_; lean_object* v___x_5529_; uint8_t v_debug_5530_; 
v___x_5529_ = lean_st_ref_get(v___y_5519_);
v_debug_5530_ = lean_ctor_get_uint8(v___x_5529_, sizeof(void*)*13);
lean_dec(v___x_5529_);
if (v_debug_5530_ == 0)
{
v___y_5526_ = v___y_5519_;
goto v___jp_5525_;
}
else
{
lean_object* v___x_5531_; 
v___x_5531_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_5516_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_);
if (lean_obj_tag(v___x_5531_) == 0)
{
lean_object* v___x_5532_; 
lean_dec_ref_known(v___x_5531_, 1);
v___x_5532_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_);
if (lean_obj_tag(v___x_5532_) == 0)
{
lean_dec_ref_known(v___x_5532_, 1);
v___y_5526_ = v___y_5519_;
goto v___jp_5525_;
}
else
{
lean_object* v_a_5533_; lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5540_; 
lean_dec_ref(v_a_5517_);
lean_dec_ref(v_f_5516_);
v_a_5533_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5540_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5540_ == 0)
{
v___x_5535_ = v___x_5532_;
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
else
{
lean_inc(v_a_5533_);
lean_dec(v___x_5532_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v___x_5538_; 
if (v_isShared_5536_ == 0)
{
v___x_5538_ = v___x_5535_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_a_5533_);
v___x_5538_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
return v___x_5538_;
}
}
}
}
else
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5548_; 
lean_dec_ref(v_a_5517_);
lean_dec_ref(v_f_5516_);
v_a_5541_ = lean_ctor_get(v___x_5531_, 0);
v_isSharedCheck_5548_ = !lean_is_exclusive(v___x_5531_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5543_ = v___x_5531_;
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5531_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5546_; 
if (v_isShared_5544_ == 0)
{
v___x_5546_ = v___x_5543_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5541_);
v___x_5546_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
return v___x_5546_;
}
}
}
}
v___jp_5525_:
{
lean_object* v___x_5527_; lean_object* v___x_5528_; 
v___x_5527_ = l_Lean_Expr_app___override(v_f_5516_, v_a_5517_);
v___x_5528_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_5527_, v___y_5526_);
return v___x_5528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_5549_, lean_object* v_a_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_){
_start:
{
lean_object* v_res_5558_; 
v_res_5558_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1___redArg(v_f_5549_, v_a_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_);
lean_dec(v___y_5556_);
lean_dec_ref(v___y_5555_);
lean_dec(v___y_5554_);
lean_dec_ref(v___y_5553_);
lean_dec(v___y_5552_);
lean_dec_ref(v___y_5551_);
return v_res_5558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0(lean_object* v_args_5559_, lean_object* v_endIdx_5560_, lean_object* v_b_5561_, lean_object* v_i_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_){
_start:
{
uint8_t v___x_5573_; 
v___x_5573_ = lean_nat_dec_le(v_endIdx_5560_, v_i_5562_);
if (v___x_5573_ == 0)
{
lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; 
v___x_5574_ = l_Lean_instInhabitedExpr;
v___x_5575_ = lean_array_get_borrowed(v___x_5574_, v_args_5559_, v_i_5562_);
lean_inc(v___x_5575_);
v___x_5576_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1___redArg(v_b_5561_, v___x_5575_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_);
if (lean_obj_tag(v___x_5576_) == 0)
{
lean_object* v_a_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; 
v_a_5577_ = lean_ctor_get(v___x_5576_, 0);
lean_inc(v_a_5577_);
lean_dec_ref_known(v___x_5576_, 1);
v___x_5578_ = lean_unsigned_to_nat(1u);
v___x_5579_ = lean_nat_add(v_i_5562_, v___x_5578_);
lean_dec(v_i_5562_);
v_b_5561_ = v_a_5577_;
v_i_5562_ = v___x_5579_;
goto _start;
}
else
{
lean_dec(v_i_5562_);
return v___x_5576_;
}
}
else
{
lean_object* v___x_5581_; 
lean_dec(v_i_5562_);
v___x_5581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5581_, 0, v_b_5561_);
return v___x_5581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0___boxed(lean_object* v_args_5582_, lean_object* v_endIdx_5583_, lean_object* v_b_5584_, lean_object* v_i_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_){
_start:
{
lean_object* v_res_5596_; 
v_res_5596_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0(v_args_5582_, v_endIdx_5583_, v_b_5584_, v_i_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
lean_dec(v___y_5592_);
lean_dec_ref(v___y_5591_);
lean_dec(v___y_5590_);
lean_dec_ref(v___y_5589_);
lean_dec(v___y_5588_);
lean_dec_ref(v___y_5587_);
lean_dec(v___y_5586_);
lean_dec(v_endIdx_5583_);
lean_dec_ref(v_args_5582_);
return v_res_5596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0(lean_object* v_f_5597_, lean_object* v_args_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_){
_start:
{
lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; 
v___x_5609_ = lean_unsigned_to_nat(0u);
v___x_5610_ = lean_array_get_size(v_args_5598_);
v___x_5611_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0(v_args_5598_, v___x_5610_, v_f_5597_, v___x_5609_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_);
return v___x_5611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0___boxed(lean_object* v_f_5612_, lean_object* v_args_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_){
_start:
{
lean_object* v_res_5624_; 
v_res_5624_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0(v_f_5612_, v_args_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_);
lean_dec(v___y_5622_);
lean_dec_ref(v___y_5621_);
lean_dec(v___y_5620_);
lean_dec_ref(v___y_5619_);
lean_dec(v___y_5618_);
lean_dec_ref(v___y_5617_);
lean_dec(v___y_5616_);
lean_dec_ref(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec_ref(v_args_5613_);
return v_res_5624_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1___redArg(lean_object* v_x_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_){
_start:
{
if (lean_obj_tag(v_x_5625_) == 0)
{
lean_object* v___x_5631_; lean_object* v___x_5632_; 
v___x_5631_ = lean_box(0);
v___x_5632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5631_);
return v___x_5632_;
}
else
{
lean_object* v_head_5633_; lean_object* v_tail_5634_; lean_object* v___x_5635_; 
v_head_5633_ = lean_ctor_get(v_x_5625_, 0);
lean_inc_n(v_head_5633_, 2);
v_tail_5634_ = lean_ctor_get(v_x_5625_, 1);
lean_inc(v_tail_5634_);
lean_dec_ref_known(v_x_5625_, 2);
v___x_5635_ = l_Lean_MVarId_getType(v_head_5633_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_);
if (lean_obj_tag(v___x_5635_) == 0)
{
lean_object* v_a_5636_; lean_object* v___x_5638_; uint8_t v_isShared_5639_; uint8_t v_isSharedCheck_5647_; 
v_a_5636_ = lean_ctor_get(v___x_5635_, 0);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5635_);
if (v_isSharedCheck_5647_ == 0)
{
v___x_5638_ = v___x_5635_;
v_isShared_5639_ = v_isSharedCheck_5647_;
goto v_resetjp_5637_;
}
else
{
lean_inc(v_a_5636_);
lean_dec(v___x_5635_);
v___x_5638_ = lean_box(0);
v_isShared_5639_ = v_isSharedCheck_5647_;
goto v_resetjp_5637_;
}
v_resetjp_5637_:
{
lean_object* v___x_5640_; uint8_t v___x_5641_; 
v___x_5640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10));
v___x_5641_ = l_Lean_Expr_isAppOf(v_a_5636_, v___x_5640_);
lean_dec(v_a_5636_);
if (v___x_5641_ == 0)
{
lean_del_object(v___x_5638_);
lean_dec(v_head_5633_);
v_x_5625_ = v_tail_5634_;
goto _start;
}
else
{
lean_object* v___x_5643_; lean_object* v___x_5645_; 
lean_dec(v_tail_5634_);
v___x_5643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5643_, 0, v_head_5633_);
if (v_isShared_5639_ == 0)
{
lean_ctor_set(v___x_5638_, 0, v___x_5643_);
v___x_5645_ = v___x_5638_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v___x_5643_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
}
else
{
lean_object* v_a_5648_; lean_object* v___x_5650_; uint8_t v_isShared_5651_; uint8_t v_isSharedCheck_5655_; 
lean_dec(v_tail_5634_);
lean_dec(v_head_5633_);
v_a_5648_ = lean_ctor_get(v___x_5635_, 0);
v_isSharedCheck_5655_ = !lean_is_exclusive(v___x_5635_);
if (v_isSharedCheck_5655_ == 0)
{
v___x_5650_ = v___x_5635_;
v_isShared_5651_ = v_isSharedCheck_5655_;
goto v_resetjp_5649_;
}
else
{
lean_inc(v_a_5648_);
lean_dec(v___x_5635_);
v___x_5650_ = lean_box(0);
v_isShared_5651_ = v_isSharedCheck_5655_;
goto v_resetjp_5649_;
}
v_resetjp_5649_:
{
lean_object* v___x_5653_; 
if (v_isShared_5651_ == 0)
{
v___x_5653_ = v___x_5650_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5654_; 
v_reuseFailAlloc_5654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5654_, 0, v_a_5648_);
v___x_5653_ = v_reuseFailAlloc_5654_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
return v___x_5653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1___redArg___boxed(lean_object* v_x_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_){
_start:
{
lean_object* v_res_5662_; 
v_res_5662_ = l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1___redArg(v_x_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
lean_dec(v___y_5658_);
lean_dec_ref(v___y_5657_);
return v_res_5662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2___redArg(lean_object* v_msg_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_){
_start:
{
lean_object* v_ref_5669_; lean_object* v___x_5670_; lean_object* v_a_5671_; lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5679_; 
v_ref_5669_ = lean_ctor_get(v___y_5666_, 2);
v___x_5670_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1_spec__1(v_msg_5663_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_);
v_a_5671_ = lean_ctor_get(v___x_5670_, 0);
v_isSharedCheck_5679_ = !lean_is_exclusive(v___x_5670_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5673_ = v___x_5670_;
v_isShared_5674_ = v_isSharedCheck_5679_;
goto v_resetjp_5672_;
}
else
{
lean_inc(v_a_5671_);
lean_dec(v___x_5670_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5679_;
goto v_resetjp_5672_;
}
v_resetjp_5672_:
{
lean_object* v___x_5675_; lean_object* v___x_5677_; 
lean_inc(v_ref_5669_);
v___x_5675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5675_, 0, v_ref_5669_);
lean_ctor_set(v___x_5675_, 1, v_a_5671_);
if (v_isShared_5674_ == 0)
{
lean_ctor_set_tag(v___x_5673_, 1);
lean_ctor_set(v___x_5673_, 0, v___x_5675_);
v___x_5677_ = v___x_5673_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v___x_5675_);
v___x_5677_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
return v___x_5677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2___redArg___boxed(lean_object* v_msg_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_){
_start:
{
lean_object* v_res_5686_; 
v_res_5686_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2___redArg(v_msg_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
lean_dec(v___y_5684_);
lean_dec_ref(v___y_5683_);
lean_dec(v___y_5682_);
lean_dec_ref(v___y_5681_);
return v_res_5686_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__1(void){
_start:
{
lean_object* v___x_5688_; lean_object* v___x_5689_; 
v___x_5688_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__0));
v___x_5689_ = l_Lean_stringToMessageData(v___x_5688_);
return v___x_5689_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__3(void){
_start:
{
lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5691_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__2));
v___x_5692_ = l_Lean_stringToMessageData(v___x_5691_);
return v___x_5692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint(lean_object* v_info_5693_, lean_object* v_specRule_5694_, lean_object* v_le_5695_, lean_object* v_W_5696_, lean_object* v_excessStates_5697_, lean_object* v_frame_5698_, lean_object* v_splitLatticeOp_x3f_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_){
_start:
{
lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; uint8_t v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; 
v___x_5710_ = l_Lean_Expr_appFn_x21(v_le_5695_);
v___x_5711_ = l_Lean_Expr_appArg_x21(v___x_5710_);
lean_dec_ref(v___x_5710_);
v___x_5712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5711_);
v___x_5713_ = 0;
v___x_5714_ = lean_box(0);
v___x_5715_ = l_Lean_Meta_mkFreshExprMVar(v___x_5712_, v___x_5713_, v___x_5714_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_);
if (lean_obj_tag(v___x_5715_) == 0)
{
lean_object* v_a_5716_; lean_object* v___x_5717_; 
v_a_5716_ = lean_ctor_get(v___x_5715_, 0);
lean_inc(v_a_5716_);
lean_dec_ref_known(v___x_5715_, 1);
v___x_5717_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0(v_W_5696_, v_excessStates_5697_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_);
if (lean_obj_tag(v___x_5717_) == 0)
{
lean_object* v_a_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; 
v_a_5718_ = lean_ctor_get(v___x_5717_, 0);
lean_inc_n(v_a_5718_, 2);
lean_dec_ref_known(v___x_5717_, 1);
v___x_5719_ = lean_unsigned_to_nat(2u);
v___x_5720_ = lean_mk_empty_array_with_capacity(v___x_5719_);
lean_inc(v_a_5716_);
v___x_5721_ = lean_array_push(v___x_5720_, v_a_5716_);
v___x_5722_ = lean_array_push(v___x_5721_, v_a_5718_);
v___x_5723_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0(v_le_5695_, v___x_5722_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_);
lean_dec_ref(v___x_5722_);
if (lean_obj_tag(v___x_5723_) == 0)
{
lean_object* v_a_5724_; lean_object* v___x_5725_; 
v_a_5724_ = lean_ctor_get(v___x_5723_, 0);
lean_inc(v_a_5724_);
lean_dec_ref_known(v___x_5723_, 1);
v___x_5725_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_5724_, v___x_5714_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_);
if (lean_obj_tag(v___x_5725_) == 0)
{
lean_object* v_a_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; 
v_a_5726_ = lean_ctor_get(v___x_5725_, 0);
lean_inc(v_a_5726_);
lean_dec_ref_known(v___x_5725_, 1);
v___x_5727_ = l_Lean_Expr_mvarId_x21(v_a_5726_);
v___x_5728_ = l_Lean_Meta_Sym_BackwardRule_apply(v___x_5727_, v_specRule_5694_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_);
if (lean_obj_tag(v___x_5728_) == 0)
{
lean_object* v_a_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5789_; 
v_a_5729_ = lean_ctor_get(v___x_5728_, 0);
v_isSharedCheck_5789_ = !lean_is_exclusive(v___x_5728_);
if (v_isSharedCheck_5789_ == 0)
{
v___x_5731_ = v___x_5728_;
v_isShared_5732_ = v_isSharedCheck_5789_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_a_5729_);
lean_dec(v___x_5728_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5789_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
if (lean_obj_tag(v_a_5729_) == 1)
{
lean_object* v_mvarIds_5733_; lean_object* v___x_5734_; 
lean_del_object(v___x_5731_);
v_mvarIds_5733_ = lean_ctor_get(v_a_5729_, 0);
lean_inc_n(v_mvarIds_5733_, 2);
lean_dec_ref_known(v_a_5729_, 1);
v___x_5734_ = l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1___redArg(v_mvarIds_5733_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_);
if (lean_obj_tag(v___x_5734_) == 0)
{
lean_object* v_a_5735_; 
v_a_5735_ = lean_ctor_get(v___x_5734_, 0);
lean_inc(v_a_5735_);
lean_dec_ref_known(v___x_5734_, 1);
if (lean_obj_tag(v_a_5735_) == 1)
{
lean_object* v_val_5736_; lean_object* v___x_5737_; 
v_val_5736_ = lean_ctor_get(v_a_5735_, 0);
lean_inc(v_val_5736_);
lean_dec_ref_known(v_a_5735_, 1);
v___x_5737_ = l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(v_a_5718_);
if (lean_obj_tag(v___x_5737_) == 1)
{
lean_object* v_val_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5766_; 
v_val_5738_ = lean_ctor_get(v___x_5737_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v___x_5737_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5740_ = v___x_5737_;
v_isShared_5741_ = v_isSharedCheck_5766_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_val_5738_);
lean_dec(v___x_5737_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5766_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v___x_5742_; 
lean_inc(v_val_5736_);
v___x_5742_ = l_Lean_MVarId_getType(v_val_5736_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_);
if (lean_obj_tag(v___x_5742_) == 0)
{
lean_object* v_a_5743_; lean_object* v___x_5745_; uint8_t v_isShared_5746_; uint8_t v_isSharedCheck_5757_; 
v_a_5743_ = lean_ctor_get(v___x_5742_, 0);
v_isSharedCheck_5757_ = !lean_is_exclusive(v___x_5742_);
if (v_isSharedCheck_5757_ == 0)
{
v___x_5745_ = v___x_5742_;
v_isShared_5746_ = v_isSharedCheck_5757_;
goto v_resetjp_5744_;
}
else
{
lean_inc(v_a_5743_);
lean_dec(v___x_5742_);
v___x_5745_ = lean_box(0);
v_isShared_5746_ = v_isSharedCheck_5757_;
goto v_resetjp_5744_;
}
v_resetjp_5744_:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5752_; 
v___x_5747_ = l_Lean_Expr_mvarId_x21(v_a_5716_);
lean_dec(v_a_5716_);
v___x_5748_ = l_Lean_Expr_appArg_x21(v_a_5743_);
lean_dec(v_a_5743_);
v___x_5749_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_5749_, 0, v_frame_5698_);
lean_ctor_set(v___x_5749_, 1, v___x_5747_);
lean_ctor_set(v___x_5749_, 2, v_val_5738_);
lean_ctor_set(v___x_5749_, 3, v___x_5748_);
lean_ctor_set(v___x_5749_, 4, v_val_5736_);
lean_ctor_set(v___x_5749_, 5, v_a_5726_);
lean_ctor_set(v___x_5749_, 6, v_splitLatticeOp_x3f_5699_);
v___x_5750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5749_);
lean_ctor_set(v___x_5750_, 1, v_mvarIds_5733_);
if (v_isShared_5741_ == 0)
{
lean_ctor_set(v___x_5740_, 0, v___x_5750_);
v___x_5752_ = v___x_5740_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v___x_5750_);
v___x_5752_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
lean_object* v___x_5754_; 
if (v_isShared_5746_ == 0)
{
lean_ctor_set(v___x_5745_, 0, v___x_5752_);
v___x_5754_ = v___x_5745_;
goto v_reusejp_5753_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v___x_5752_);
v___x_5754_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5753_;
}
v_reusejp_5753_:
{
return v___x_5754_;
}
}
}
}
else
{
lean_object* v_a_5758_; lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5765_; 
lean_del_object(v___x_5740_);
lean_dec(v_val_5738_);
lean_dec(v_val_5736_);
lean_dec(v_mvarIds_5733_);
lean_dec(v_a_5726_);
lean_dec(v_a_5716_);
lean_dec_ref(v_splitLatticeOp_x3f_5699_);
lean_dec(v_frame_5698_);
v_a_5758_ = lean_ctor_get(v___x_5742_, 0);
v_isSharedCheck_5765_ = !lean_is_exclusive(v___x_5742_);
if (v_isSharedCheck_5765_ == 0)
{
v___x_5760_ = v___x_5742_;
v_isShared_5761_ = v_isSharedCheck_5765_;
goto v_resetjp_5759_;
}
else
{
lean_inc(v_a_5758_);
lean_dec(v___x_5742_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5765_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v___x_5763_; 
if (v_isShared_5761_ == 0)
{
v___x_5763_ = v___x_5760_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5764_; 
v_reuseFailAlloc_5764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5764_, 0, v_a_5758_);
v___x_5763_ = v_reuseFailAlloc_5764_;
goto v_reusejp_5762_;
}
v_reusejp_5762_:
{
return v___x_5763_;
}
}
}
}
}
else
{
lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; 
lean_dec(v___x_5737_);
lean_dec(v_val_5736_);
lean_dec(v_mvarIds_5733_);
lean_dec(v_a_5726_);
lean_dec(v_a_5716_);
lean_dec_ref(v_splitLatticeOp_x3f_5699_);
lean_dec(v_frame_5698_);
v___x_5767_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__1);
v___x_5768_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5693_);
v___x_5769_ = l_Lean_indentExpr(v___x_5768_);
v___x_5770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5770_, 0, v___x_5767_);
lean_ctor_set(v___x_5770_, 1, v___x_5769_);
v___x_5771_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2___redArg(v___x_5770_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_);
return v___x_5771_;
}
}
else
{
lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; 
lean_dec(v_a_5735_);
lean_dec(v_mvarIds_5733_);
lean_dec(v_a_5726_);
lean_dec(v_a_5718_);
lean_dec(v_a_5716_);
lean_dec_ref(v_splitLatticeOp_x3f_5699_);
lean_dec(v_frame_5698_);
v___x_5772_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___closed__3);
v___x_5773_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5693_);
v___x_5774_ = l_Lean_indentExpr(v___x_5773_);
v___x_5775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5775_, 0, v___x_5772_);
lean_ctor_set(v___x_5775_, 1, v___x_5774_);
v___x_5776_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2___redArg(v___x_5775_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_);
return v___x_5776_;
}
}
else
{
lean_object* v_a_5777_; lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5784_; 
lean_dec(v_mvarIds_5733_);
lean_dec(v_a_5726_);
lean_dec(v_a_5718_);
lean_dec(v_a_5716_);
lean_dec_ref(v_splitLatticeOp_x3f_5699_);
lean_dec(v_frame_5698_);
v_a_5777_ = lean_ctor_get(v___x_5734_, 0);
v_isSharedCheck_5784_ = !lean_is_exclusive(v___x_5734_);
if (v_isSharedCheck_5784_ == 0)
{
v___x_5779_ = v___x_5734_;
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
else
{
lean_inc(v_a_5777_);
lean_dec(v___x_5734_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v___x_5782_; 
if (v_isShared_5780_ == 0)
{
v___x_5782_ = v___x_5779_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_a_5777_);
v___x_5782_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
return v___x_5782_;
}
}
}
}
else
{
lean_object* v___x_5785_; lean_object* v___x_5787_; 
lean_dec(v_a_5729_);
lean_dec(v_a_5726_);
lean_dec(v_a_5718_);
lean_dec(v_a_5716_);
lean_dec_ref(v_splitLatticeOp_x3f_5699_);
lean_dec(v_frame_5698_);
v___x_5785_ = lean_box(0);
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 0, v___x_5785_);
v___x_5787_ = v___x_5731_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5788_; 
v_reuseFailAlloc_5788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5788_, 0, v___x_5785_);
v___x_5787_ = v_reuseFailAlloc_5788_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
return v___x_5787_;
}
}
}
}
else
{
lean_object* v_a_5790_; lean_object* v___x_5792_; uint8_t v_isShared_5793_; uint8_t v_isSharedCheck_5797_; 
lean_dec(v_a_5726_);
lean_dec(v_a_5718_);
lean_dec(v_a_5716_);
lean_dec_ref(v_splitLatticeOp_x3f_5699_);
lean_dec(v_frame_5698_);
v_a_5790_ = lean_ctor_get(v___x_5728_, 0);
v_isSharedCheck_5797_ = !lean_is_exclusive(v___x_5728_);
if (v_isSharedCheck_5797_ == 0)
{
v___x_5792_ = v___x_5728_;
v_isShared_5793_ = v_isSharedCheck_5797_;
goto v_resetjp_5791_;
}
else
{
lean_inc(v_a_5790_);
lean_dec(v___x_5728_);
v___x_5792_ = lean_box(0);
v_isShared_5793_ = v_isSharedCheck_5797_;
goto v_resetjp_5791_;
}
v_resetjp_5791_:
{
lean_object* v___x_5795_; 
if (v_isShared_5793_ == 0)
{
v___x_5795_ = v___x_5792_;
goto v_reusejp_5794_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v_a_5790_);
v___x_5795_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5794_;
}
v_reusejp_5794_:
{
return v___x_5795_;
}
}
}
}
else
{
lean_object* v_a_5798_; lean_object* v___x_5800_; uint8_t v_isShared_5801_; uint8_t v_isSharedCheck_5805_; 
lean_dec(v_a_5718_);
lean_dec(v_a_5716_);
lean_dec_ref(v_splitLatticeOp_x3f_5699_);
lean_dec(v_frame_5698_);
lean_dec_ref(v_specRule_5694_);
v_a_5798_ = lean_ctor_get(v___x_5725_, 0);
v_isSharedCheck_5805_ = !lean_is_exclusive(v___x_5725_);
if (v_isSharedCheck_5805_ == 0)
{
v___x_5800_ = v___x_5725_;
v_isShared_5801_ = v_isSharedCheck_5805_;
goto v_resetjp_5799_;
}
else
{
lean_inc(v_a_5798_);
lean_dec(v___x_5725_);
v___x_5800_ = lean_box(0);
v_isShared_5801_ = v_isSharedCheck_5805_;
goto v_resetjp_5799_;
}
v_resetjp_5799_:
{
lean_object* v___x_5803_; 
if (v_isShared_5801_ == 0)
{
v___x_5803_ = v___x_5800_;
goto v_reusejp_5802_;
}
else
{
lean_object* v_reuseFailAlloc_5804_; 
v_reuseFailAlloc_5804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5804_, 0, v_a_5798_);
v___x_5803_ = v_reuseFailAlloc_5804_;
goto v_reusejp_5802_;
}
v_reusejp_5802_:
{
return v___x_5803_;
}
}
}
}
else
{
lean_object* v_a_5806_; lean_object* v___x_5808_; uint8_t v_isShared_5809_; uint8_t v_isSharedCheck_5813_; 
lean_dec(v_a_5718_);
lean_dec(v_a_5716_);
lean_dec_ref(v_splitLatticeOp_x3f_5699_);
lean_dec(v_frame_5698_);
lean_dec_ref(v_specRule_5694_);
v_a_5806_ = lean_ctor_get(v___x_5723_, 0);
v_isSharedCheck_5813_ = !lean_is_exclusive(v___x_5723_);
if (v_isSharedCheck_5813_ == 0)
{
v___x_5808_ = v___x_5723_;
v_isShared_5809_ = v_isSharedCheck_5813_;
goto v_resetjp_5807_;
}
else
{
lean_inc(v_a_5806_);
lean_dec(v___x_5723_);
v___x_5808_ = lean_box(0);
v_isShared_5809_ = v_isSharedCheck_5813_;
goto v_resetjp_5807_;
}
v_resetjp_5807_:
{
lean_object* v___x_5811_; 
if (v_isShared_5809_ == 0)
{
v___x_5811_ = v___x_5808_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v_a_5806_);
v___x_5811_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5810_;
}
v_reusejp_5810_:
{
return v___x_5811_;
}
}
}
}
else
{
lean_object* v_a_5814_; lean_object* v___x_5816_; uint8_t v_isShared_5817_; uint8_t v_isSharedCheck_5821_; 
lean_dec(v_a_5716_);
lean_dec_ref(v_splitLatticeOp_x3f_5699_);
lean_dec(v_frame_5698_);
lean_dec_ref(v_le_5695_);
lean_dec_ref(v_specRule_5694_);
v_a_5814_ = lean_ctor_get(v___x_5717_, 0);
v_isSharedCheck_5821_ = !lean_is_exclusive(v___x_5717_);
if (v_isSharedCheck_5821_ == 0)
{
v___x_5816_ = v___x_5717_;
v_isShared_5817_ = v_isSharedCheck_5821_;
goto v_resetjp_5815_;
}
else
{
lean_inc(v_a_5814_);
lean_dec(v___x_5717_);
v___x_5816_ = lean_box(0);
v_isShared_5817_ = v_isSharedCheck_5821_;
goto v_resetjp_5815_;
}
v_resetjp_5815_:
{
lean_object* v___x_5819_; 
if (v_isShared_5817_ == 0)
{
v___x_5819_ = v___x_5816_;
goto v_reusejp_5818_;
}
else
{
lean_object* v_reuseFailAlloc_5820_; 
v_reuseFailAlloc_5820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_a_5814_);
v___x_5819_ = v_reuseFailAlloc_5820_;
goto v_reusejp_5818_;
}
v_reusejp_5818_:
{
return v___x_5819_;
}
}
}
}
else
{
lean_object* v_a_5822_; lean_object* v___x_5824_; uint8_t v_isShared_5825_; uint8_t v_isSharedCheck_5829_; 
lean_dec_ref(v_splitLatticeOp_x3f_5699_);
lean_dec(v_frame_5698_);
lean_dec_ref(v_W_5696_);
lean_dec_ref(v_le_5695_);
lean_dec_ref(v_specRule_5694_);
v_a_5822_ = lean_ctor_get(v___x_5715_, 0);
v_isSharedCheck_5829_ = !lean_is_exclusive(v___x_5715_);
if (v_isSharedCheck_5829_ == 0)
{
v___x_5824_ = v___x_5715_;
v_isShared_5825_ = v_isSharedCheck_5829_;
goto v_resetjp_5823_;
}
else
{
lean_inc(v_a_5822_);
lean_dec(v___x_5715_);
v___x_5824_ = lean_box(0);
v_isShared_5825_ = v_isSharedCheck_5829_;
goto v_resetjp_5823_;
}
v_resetjp_5823_:
{
lean_object* v___x_5827_; 
if (v_isShared_5825_ == 0)
{
v___x_5827_ = v___x_5824_;
goto v_reusejp_5826_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v_a_5822_);
v___x_5827_ = v_reuseFailAlloc_5828_;
goto v_reusejp_5826_;
}
v_reusejp_5826_:
{
return v___x_5827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint___boxed(lean_object** _args){
lean_object* v_info_5830_ = _args[0];
lean_object* v_specRule_5831_ = _args[1];
lean_object* v_le_5832_ = _args[2];
lean_object* v_W_5833_ = _args[3];
lean_object* v_excessStates_5834_ = _args[4];
lean_object* v_frame_5835_ = _args[5];
lean_object* v_splitLatticeOp_x3f_5836_ = _args[6];
lean_object* v_a_5837_ = _args[7];
lean_object* v_a_5838_ = _args[8];
lean_object* v_a_5839_ = _args[9];
lean_object* v_a_5840_ = _args[10];
lean_object* v_a_5841_ = _args[11];
lean_object* v_a_5842_ = _args[12];
lean_object* v_a_5843_ = _args[13];
lean_object* v_a_5844_ = _args[14];
lean_object* v_a_5845_ = _args[15];
lean_object* v_a_5846_ = _args[16];
_start:
{
lean_object* v_res_5847_; 
v_res_5847_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint(v_info_5830_, v_specRule_5831_, v_le_5832_, v_W_5833_, v_excessStates_5834_, v_frame_5835_, v_splitLatticeOp_x3f_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_);
lean_dec(v_a_5845_);
lean_dec_ref(v_a_5844_);
lean_dec(v_a_5843_);
lean_dec_ref(v_a_5842_);
lean_dec(v_a_5841_);
lean_dec_ref(v_a_5840_);
lean_dec(v_a_5839_);
lean_dec_ref(v_a_5838_);
lean_dec(v_a_5837_);
lean_dec_ref(v_excessStates_5834_);
lean_dec_ref(v_info_5830_);
return v_res_5847_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1(lean_object* v_x_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_){
_start:
{
lean_object* v___x_5859_; 
v___x_5859_ = l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1___redArg(v_x_5848_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_);
return v___x_5859_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1___boxed(lean_object* v_x_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_){
_start:
{
lean_object* v_res_5871_; 
v_res_5871_ = l_List_findM_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__1(v_x_5860_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_);
lean_dec(v___y_5869_);
lean_dec_ref(v___y_5868_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec(v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec(v___y_5863_);
lean_dec_ref(v___y_5862_);
lean_dec(v___y_5861_);
return v_res_5871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2(lean_object* v_00_u03b1_5872_, lean_object* v_msg_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_){
_start:
{
lean_object* v___x_5884_; 
v___x_5884_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2___redArg(v_msg_5873_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_);
return v___x_5884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2___boxed(lean_object* v_00_u03b1_5885_, lean_object* v_msg_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_){
_start:
{
lean_object* v_res_5897_; 
v_res_5897_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__2(v_00_u03b1_5885_, v_msg_5886_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_);
lean_dec(v___y_5895_);
lean_dec_ref(v___y_5894_);
lean_dec(v___y_5893_);
lean_dec_ref(v___y_5892_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec(v___y_5889_);
lean_dec_ref(v___y_5888_);
lean_dec(v___y_5887_);
return v_res_5897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1(lean_object* v_f_5898_, lean_object* v_a_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_){
_start:
{
lean_object* v___x_5910_; 
v___x_5910_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1___redArg(v_f_5898_, v_a_5899_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_);
return v___x_5910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1___boxed(lean_object* v_f_5911_, lean_object* v_a_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_){
_start:
{
lean_object* v_res_5923_; 
v_res_5923_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint_spec__0_spec__0_spec__1(v_f_5911_, v_a_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_, v___y_5920_, v___y_5921_);
lean_dec(v___y_5921_);
lean_dec_ref(v___y_5920_);
lean_dec(v___y_5919_);
lean_dec_ref(v___y_5918_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
lean_dec(v___y_5915_);
lean_dec_ref(v___y_5914_);
lean_dec(v___y_5913_);
return v_res_5923_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__1(void){
_start:
{
lean_object* v___x_5925_; lean_object* v___x_5926_; 
v___x_5925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__0));
v___x_5926_ = l_Lean_stringToMessageData(v___x_5925_);
return v___x_5926_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__3(void){
_start:
{
lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5928_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__2));
v___x_5929_ = l_Lean_stringToMessageData(v___x_5928_);
return v___x_5929_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__5(void){
_start:
{
lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5931_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__4));
v___x_5932_ = l_Lean_stringToMessageData(v___x_5931_);
return v___x_5932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule(lean_object* v_goal_5933_, lean_object* v_info_5934_, lean_object* v_fp_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_, lean_object* v_a_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_){
_start:
{
lean_object* v___x_5948_; lean_object* v___x_5949_; 
v___x_5948_ = lean_box(0);
lean_inc_ref(v_info_5934_);
v___x_5949_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_5935_, v_info_5934_, v_a_5937_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_);
if (lean_obj_tag(v___x_5949_) == 0)
{
lean_object* v_a_5950_; lean_object* v___x_5951_; 
v_a_5950_ = lean_ctor_get(v___x_5949_, 0);
lean_inc(v_a_5950_);
lean_dec_ref_known(v___x_5949_, 1);
v___x_5951_ = l_Lean_MVarId_getType(v_goal_5933_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_);
if (lean_obj_tag(v___x_5951_) == 0)
{
lean_object* v_a_5952_; lean_object* v___x_5953_; 
v_a_5952_ = lean_ctor_get(v___x_5951_, 0);
lean_inc(v_a_5952_);
lean_dec_ref_known(v___x_5951_, 1);
v___x_5953_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_5952_, v___x_5948_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_);
if (lean_obj_tag(v___x_5953_) == 0)
{
lean_object* v_a_5954_; lean_object* v_rule_5955_; lean_object* v_splitVCIdx_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; 
v_a_5954_ = lean_ctor_get(v___x_5953_, 0);
lean_inc(v_a_5954_);
lean_dec_ref_known(v___x_5953_, 1);
v_rule_5955_ = lean_ctor_get(v_a_5950_, 0);
v_splitVCIdx_5956_ = lean_ctor_get(v_a_5950_, 1);
v___x_5957_ = l_Lean_Expr_mvarId_x21(v_a_5954_);
v___x_5958_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__1);
v___x_5959_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_5934_);
v___x_5960_ = l_Lean_indentExpr(v___x_5959_);
lean_inc_ref(v___x_5960_);
v___x_5961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5958_);
lean_ctor_set(v___x_5961_, 1, v___x_5960_);
v___x_5962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5961_);
lean_inc_ref(v_rule_5955_);
v___x_5963_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_5955_, v___x_5957_, v___x_5962_, v_a_5936_, v_a_5937_, v_a_5938_, v_a_5939_, v_a_5940_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_);
if (lean_obj_tag(v___x_5963_) == 0)
{
lean_object* v_a_5964_; 
v_a_5964_ = lean_ctor_get(v___x_5963_, 0);
lean_inc(v_a_5964_);
lean_dec_ref_known(v___x_5963_, 1);
if (lean_obj_tag(v_a_5964_) == 1)
{
lean_object* v_mvarIds_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; 
lean_dec_ref(v___x_5960_);
v_mvarIds_5965_ = lean_ctor_get(v_a_5964_, 0);
lean_inc(v_mvarIds_5965_);
lean_dec_ref_known(v_a_5964_, 1);
v___x_5966_ = lean_array_mk(v_mvarIds_5965_);
v___x_5967_ = lean_array_get_borrowed(v___x_5948_, v___x_5966_, v_splitVCIdx_5956_);
lean_inc(v___x_5967_);
v___x_5968_ = l_Lean_MVarId_getType(v___x_5967_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_);
if (lean_obj_tag(v___x_5968_) == 0)
{
lean_object* v_a_5969_; lean_object* v___x_5971_; uint8_t v_isShared_5972_; uint8_t v_isSharedCheck_6004_; 
v_a_5969_ = lean_ctor_get(v___x_5968_, 0);
v_isSharedCheck_6004_ = !lean_is_exclusive(v___x_5968_);
if (v_isSharedCheck_6004_ == 0)
{
v___x_5971_ = v___x_5968_;
v_isShared_5972_ = v_isSharedCheck_6004_;
goto v_resetjp_5970_;
}
else
{
lean_inc(v_a_5969_);
lean_dec(v___x_5968_);
v___x_5971_ = lean_box(0);
v_isShared_5972_ = v_isSharedCheck_6004_;
goto v_resetjp_5970_;
}
v_resetjp_5970_:
{
lean_object* v___y_5974_; lean_object* v___y_5975_; lean_object* v___y_5976_; lean_object* v___y_5977_; lean_object* v___x_5982_; uint8_t v___x_5983_; 
v___x_5982_ = l_Lean_Expr_cleanupAnnotations(v_a_5969_);
v___x_5983_ = l_Lean_Expr_isApp(v___x_5982_);
if (v___x_5983_ == 0)
{
lean_dec_ref(v___x_5982_);
lean_del_object(v___x_5971_);
lean_dec_ref(v___x_5966_);
lean_dec(v_a_5954_);
lean_dec(v_a_5950_);
lean_dec_ref(v_info_5934_);
v___y_5974_ = v_a_5943_;
v___y_5975_ = v_a_5944_;
v___y_5976_ = v_a_5945_;
v___y_5977_ = v_a_5946_;
goto v___jp_5973_;
}
else
{
lean_object* v___x_5984_; uint8_t v___x_5985_; 
v___x_5984_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5982_);
v___x_5985_ = l_Lean_Expr_isApp(v___x_5984_);
if (v___x_5985_ == 0)
{
lean_dec_ref(v___x_5984_);
lean_dec_ref(v___x_5982_);
lean_del_object(v___x_5971_);
lean_dec_ref(v___x_5966_);
lean_dec(v_a_5954_);
lean_dec(v_a_5950_);
lean_dec_ref(v_info_5934_);
v___y_5974_ = v_a_5943_;
v___y_5975_ = v_a_5944_;
v___y_5976_ = v_a_5945_;
v___y_5977_ = v_a_5946_;
goto v___jp_5973_;
}
else
{
lean_object* v___x_5986_; uint8_t v___x_5987_; 
v___x_5986_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5984_);
lean_dec_ref(v___x_5984_);
v___x_5987_ = l_Lean_Expr_isApp(v___x_5986_);
if (v___x_5987_ == 0)
{
lean_dec_ref(v___x_5986_);
lean_dec_ref(v___x_5982_);
lean_del_object(v___x_5971_);
lean_dec_ref(v___x_5966_);
lean_dec(v_a_5954_);
lean_dec(v_a_5950_);
lean_dec_ref(v_info_5934_);
v___y_5974_ = v_a_5943_;
v___y_5975_ = v_a_5944_;
v___y_5976_ = v_a_5945_;
v___y_5977_ = v_a_5946_;
goto v___jp_5973_;
}
else
{
lean_object* v___x_5988_; uint8_t v___x_5989_; 
v___x_5988_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5986_);
lean_dec_ref(v___x_5986_);
v___x_5989_ = l_Lean_Expr_isApp(v___x_5988_);
if (v___x_5989_ == 0)
{
lean_dec_ref(v___x_5988_);
lean_dec_ref(v___x_5982_);
lean_del_object(v___x_5971_);
lean_dec_ref(v___x_5966_);
lean_dec(v_a_5954_);
lean_dec(v_a_5950_);
lean_dec_ref(v_info_5934_);
v___y_5974_ = v_a_5943_;
v___y_5975_ = v_a_5944_;
v___y_5976_ = v_a_5945_;
v___y_5977_ = v_a_5946_;
goto v___jp_5973_;
}
else
{
lean_object* v___x_5990_; lean_object* v___x_5991_; uint8_t v___x_5992_; 
v___x_5990_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5988_);
lean_dec_ref(v___x_5988_);
v___x_5991_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10));
v___x_5992_ = l_Lean_Expr_isConstOf(v___x_5990_, v___x_5991_);
lean_dec_ref(v___x_5990_);
if (v___x_5992_ == 0)
{
lean_dec_ref(v___x_5982_);
lean_del_object(v___x_5971_);
lean_dec_ref(v___x_5966_);
lean_dec(v_a_5954_);
lean_dec(v_a_5950_);
lean_dec_ref(v_info_5934_);
v___y_5974_ = v_a_5943_;
v___y_5975_ = v_a_5944_;
v___y_5976_ = v_a_5945_;
v___y_5977_ = v_a_5946_;
goto v___jp_5973_;
}
else
{
lean_object* v_arg_5993_; lean_object* v_excessArgs_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6002_; 
lean_dec(v_a_5969_);
v_arg_5993_ = lean_ctor_get(v___x_5982_, 1);
lean_inc_ref(v_arg_5993_);
lean_dec_ref(v___x_5982_);
v_excessArgs_5994_ = lean_ctor_get(v_info_5934_, 3);
lean_inc_ref(v_excessArgs_5994_);
lean_dec_ref(v_info_5934_);
v___x_5995_ = lean_array_get_size(v_excessArgs_5994_);
lean_dec_ref(v_excessArgs_5994_);
v___x_5996_ = l_Lean_Expr_stripArgsN(v_arg_5993_, v___x_5995_);
lean_dec_ref(v_arg_5993_);
v___x_5997_ = l_Lean_Expr_appArg_x21(v___x_5996_);
lean_dec_ref(v___x_5996_);
v___x_5998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5966_);
lean_ctor_set(v___x_5998_, 1, v___x_5997_);
v___x_5999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5999_, 0, v_a_5950_);
lean_ctor_set(v___x_5999_, 1, v___x_5998_);
v___x_6000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6000_, 0, v_a_5954_);
lean_ctor_set(v___x_6000_, 1, v___x_5999_);
if (v_isShared_5972_ == 0)
{
lean_ctor_set(v___x_5971_, 0, v___x_6000_);
v___x_6002_ = v___x_5971_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6003_; 
v_reuseFailAlloc_6003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6003_, 0, v___x_6000_);
v___x_6002_ = v_reuseFailAlloc_6003_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
return v___x_6002_;
}
}
}
}
}
}
v___jp_5973_:
{
lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; 
v___x_5978_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__3);
v___x_5979_ = l_Lean_indentExpr(v_a_5969_);
v___x_5980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5980_, 0, v___x_5978_);
lean_ctor_set(v___x_5980_, 1, v___x_5979_);
v___x_5981_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_5980_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_);
return v___x_5981_;
}
}
}
else
{
lean_object* v_a_6005_; lean_object* v___x_6007_; uint8_t v_isShared_6008_; uint8_t v_isSharedCheck_6012_; 
lean_dec_ref(v___x_5966_);
lean_dec(v_a_5954_);
lean_dec(v_a_5950_);
lean_dec_ref(v_info_5934_);
v_a_6005_ = lean_ctor_get(v___x_5968_, 0);
v_isSharedCheck_6012_ = !lean_is_exclusive(v___x_5968_);
if (v_isSharedCheck_6012_ == 0)
{
v___x_6007_ = v___x_5968_;
v_isShared_6008_ = v_isSharedCheck_6012_;
goto v_resetjp_6006_;
}
else
{
lean_inc(v_a_6005_);
lean_dec(v___x_5968_);
v___x_6007_ = lean_box(0);
v_isShared_6008_ = v_isSharedCheck_6012_;
goto v_resetjp_6006_;
}
v_resetjp_6006_:
{
lean_object* v___x_6010_; 
if (v_isShared_6008_ == 0)
{
v___x_6010_ = v___x_6007_;
goto v_reusejp_6009_;
}
else
{
lean_object* v_reuseFailAlloc_6011_; 
v_reuseFailAlloc_6011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_a_6005_);
v___x_6010_ = v_reuseFailAlloc_6011_;
goto v_reusejp_6009_;
}
v_reusejp_6009_:
{
return v___x_6010_;
}
}
}
}
else
{
lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; 
lean_dec(v_a_5964_);
lean_dec(v_a_5954_);
lean_dec(v_a_5950_);
lean_dec_ref(v_info_5934_);
v___x_6013_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___closed__5);
v___x_6014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6013_);
lean_ctor_set(v___x_6014_, 1, v___x_5960_);
v___x_6015_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_6014_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_);
return v___x_6015_;
}
}
else
{
lean_object* v_a_6016_; lean_object* v___x_6018_; uint8_t v_isShared_6019_; uint8_t v_isSharedCheck_6023_; 
lean_dec_ref(v___x_5960_);
lean_dec(v_a_5954_);
lean_dec(v_a_5950_);
lean_dec_ref(v_info_5934_);
v_a_6016_ = lean_ctor_get(v___x_5963_, 0);
v_isSharedCheck_6023_ = !lean_is_exclusive(v___x_5963_);
if (v_isSharedCheck_6023_ == 0)
{
v___x_6018_ = v___x_5963_;
v_isShared_6019_ = v_isSharedCheck_6023_;
goto v_resetjp_6017_;
}
else
{
lean_inc(v_a_6016_);
lean_dec(v___x_5963_);
v___x_6018_ = lean_box(0);
v_isShared_6019_ = v_isSharedCheck_6023_;
goto v_resetjp_6017_;
}
v_resetjp_6017_:
{
lean_object* v___x_6021_; 
if (v_isShared_6019_ == 0)
{
v___x_6021_ = v___x_6018_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_a_6016_);
v___x_6021_ = v_reuseFailAlloc_6022_;
goto v_reusejp_6020_;
}
v_reusejp_6020_:
{
return v___x_6021_;
}
}
}
}
else
{
lean_object* v_a_6024_; lean_object* v___x_6026_; uint8_t v_isShared_6027_; uint8_t v_isSharedCheck_6031_; 
lean_dec(v_a_5950_);
lean_dec_ref(v_info_5934_);
v_a_6024_ = lean_ctor_get(v___x_5953_, 0);
v_isSharedCheck_6031_ = !lean_is_exclusive(v___x_5953_);
if (v_isSharedCheck_6031_ == 0)
{
v___x_6026_ = v___x_5953_;
v_isShared_6027_ = v_isSharedCheck_6031_;
goto v_resetjp_6025_;
}
else
{
lean_inc(v_a_6024_);
lean_dec(v___x_5953_);
v___x_6026_ = lean_box(0);
v_isShared_6027_ = v_isSharedCheck_6031_;
goto v_resetjp_6025_;
}
v_resetjp_6025_:
{
lean_object* v___x_6029_; 
if (v_isShared_6027_ == 0)
{
v___x_6029_ = v___x_6026_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6030_; 
v_reuseFailAlloc_6030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_a_6024_);
v___x_6029_ = v_reuseFailAlloc_6030_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
return v___x_6029_;
}
}
}
}
else
{
lean_object* v_a_6032_; lean_object* v___x_6034_; uint8_t v_isShared_6035_; uint8_t v_isSharedCheck_6039_; 
lean_dec(v_a_5950_);
lean_dec_ref(v_info_5934_);
v_a_6032_ = lean_ctor_get(v___x_5951_, 0);
v_isSharedCheck_6039_ = !lean_is_exclusive(v___x_5951_);
if (v_isSharedCheck_6039_ == 0)
{
v___x_6034_ = v___x_5951_;
v_isShared_6035_ = v_isSharedCheck_6039_;
goto v_resetjp_6033_;
}
else
{
lean_inc(v_a_6032_);
lean_dec(v___x_5951_);
v___x_6034_ = lean_box(0);
v_isShared_6035_ = v_isSharedCheck_6039_;
goto v_resetjp_6033_;
}
v_resetjp_6033_:
{
lean_object* v___x_6037_; 
if (v_isShared_6035_ == 0)
{
v___x_6037_ = v___x_6034_;
goto v_reusejp_6036_;
}
else
{
lean_object* v_reuseFailAlloc_6038_; 
v_reuseFailAlloc_6038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6038_, 0, v_a_6032_);
v___x_6037_ = v_reuseFailAlloc_6038_;
goto v_reusejp_6036_;
}
v_reusejp_6036_:
{
return v___x_6037_;
}
}
}
}
else
{
lean_object* v_a_6040_; lean_object* v___x_6042_; uint8_t v_isShared_6043_; uint8_t v_isSharedCheck_6047_; 
lean_dec_ref(v_info_5934_);
lean_dec(v_goal_5933_);
v_a_6040_ = lean_ctor_get(v___x_5949_, 0);
v_isSharedCheck_6047_ = !lean_is_exclusive(v___x_5949_);
if (v_isSharedCheck_6047_ == 0)
{
v___x_6042_ = v___x_5949_;
v_isShared_6043_ = v_isSharedCheck_6047_;
goto v_resetjp_6041_;
}
else
{
lean_inc(v_a_6040_);
lean_dec(v___x_5949_);
v___x_6042_ = lean_box(0);
v_isShared_6043_ = v_isSharedCheck_6047_;
goto v_resetjp_6041_;
}
v_resetjp_6041_:
{
lean_object* v___x_6045_; 
if (v_isShared_6043_ == 0)
{
v___x_6045_ = v___x_6042_;
goto v_reusejp_6044_;
}
else
{
lean_object* v_reuseFailAlloc_6046_; 
v_reuseFailAlloc_6046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6046_, 0, v_a_6040_);
v___x_6045_ = v_reuseFailAlloc_6046_;
goto v_reusejp_6044_;
}
v_reusejp_6044_:
{
return v___x_6045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule___boxed(lean_object* v_goal_6048_, lean_object* v_info_6049_, lean_object* v_fp_6050_, lean_object* v_a_6051_, lean_object* v_a_6052_, lean_object* v_a_6053_, lean_object* v_a_6054_, lean_object* v_a_6055_, lean_object* v_a_6056_, lean_object* v_a_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_){
_start:
{
lean_object* v_res_6063_; 
v_res_6063_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule(v_goal_6048_, v_info_6049_, v_fp_6050_, v_a_6051_, v_a_6052_, v_a_6053_, v_a_6054_, v_a_6055_, v_a_6056_, v_a_6057_, v_a_6058_, v_a_6059_, v_a_6060_, v_a_6061_);
lean_dec(v_a_6061_);
lean_dec_ref(v_a_6060_);
lean_dec(v_a_6059_);
lean_dec_ref(v_a_6058_);
lean_dec(v_a_6057_);
lean_dec_ref(v_a_6056_);
lean_dec(v_a_6055_);
lean_dec_ref(v_a_6054_);
lean_dec(v_a_6053_);
lean_dec(v_a_6052_);
lean_dec_ref(v_a_6051_);
return v_res_6063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg___lam__0(lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_m_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_){
_start:
{
lean_object* v___x_6080_; 
lean_inc(v_m_6066_);
v___x_6080_ = l_Lean_MVarId_getType(v_m_6066_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_);
if (lean_obj_tag(v___x_6080_) == 0)
{
lean_object* v_a_6081_; lean_object* v___x_6082_; uint8_t v___x_6083_; 
v_a_6081_ = lean_ctor_get(v___x_6080_, 0);
lean_inc(v_a_6081_);
lean_dec_ref_known(v___x_6080_, 1);
v___x_6082_ = l_Lean_Expr_cleanupAnnotations(v_a_6081_);
lean_dec(v_a_6081_);
v___x_6083_ = l_Lean_Expr_isApp(v___x_6082_);
if (v___x_6083_ == 0)
{
lean_dec_ref(v___x_6082_);
lean_dec(v_m_6066_);
goto v___jp_6077_;
}
else
{
lean_object* v___x_6084_; uint8_t v___x_6085_; 
v___x_6084_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6082_);
v___x_6085_ = l_Lean_Expr_isApp(v___x_6084_);
if (v___x_6085_ == 0)
{
lean_dec_ref(v___x_6084_);
lean_dec_ref(v___x_6082_);
lean_dec(v_m_6066_);
goto v___jp_6077_;
}
else
{
lean_object* v___x_6086_; uint8_t v___x_6087_; 
v___x_6086_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6084_);
lean_dec_ref(v___x_6084_);
v___x_6087_ = l_Lean_Expr_isApp(v___x_6086_);
if (v___x_6087_ == 0)
{
lean_dec_ref(v___x_6086_);
lean_dec_ref(v___x_6082_);
lean_dec(v_m_6066_);
goto v___jp_6077_;
}
else
{
lean_object* v___x_6088_; uint8_t v___x_6089_; 
v___x_6088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6086_);
lean_dec_ref(v___x_6086_);
v___x_6089_ = l_Lean_Expr_isApp(v___x_6088_);
if (v___x_6089_ == 0)
{
lean_dec_ref(v___x_6088_);
lean_dec_ref(v___x_6082_);
lean_dec(v_m_6066_);
goto v___jp_6077_;
}
else
{
lean_object* v___x_6090_; lean_object* v___x_6091_; uint8_t v___x_6092_; 
v___x_6090_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6088_);
lean_dec_ref(v___x_6088_);
v___x_6091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10));
v___x_6092_ = l_Lean_Expr_isConstOf(v___x_6090_, v___x_6091_);
lean_dec_ref(v___x_6090_);
if (v___x_6092_ == 0)
{
lean_dec_ref(v___x_6082_);
lean_dec(v_m_6066_);
goto v___jp_6077_;
}
else
{
lean_object* v_arg_6093_; lean_object* v___x_6094_; 
v_arg_6093_ = lean_ctor_get(v___x_6082_, 1);
lean_inc_ref(v_arg_6093_);
lean_dec_ref(v___x_6082_);
v___x_6094_ = l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(v_m_6066_, v_arg_6093_, v_a_6064_, v_a_6065_, v___y_6067_, v___y_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_);
return v___x_6094_;
}
}
}
}
}
}
else
{
lean_object* v_a_6095_; lean_object* v___x_6097_; uint8_t v_isShared_6098_; uint8_t v_isSharedCheck_6102_; 
lean_dec(v_m_6066_);
v_a_6095_ = lean_ctor_get(v___x_6080_, 0);
v_isSharedCheck_6102_ = !lean_is_exclusive(v___x_6080_);
if (v_isSharedCheck_6102_ == 0)
{
v___x_6097_ = v___x_6080_;
v_isShared_6098_ = v_isSharedCheck_6102_;
goto v_resetjp_6096_;
}
else
{
lean_inc(v_a_6095_);
lean_dec(v___x_6080_);
v___x_6097_ = lean_box(0);
v_isShared_6098_ = v_isSharedCheck_6102_;
goto v_resetjp_6096_;
}
v_resetjp_6096_:
{
lean_object* v___x_6100_; 
if (v_isShared_6098_ == 0)
{
v___x_6100_ = v___x_6097_;
goto v_reusejp_6099_;
}
else
{
lean_object* v_reuseFailAlloc_6101_; 
v_reuseFailAlloc_6101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6101_, 0, v_a_6095_);
v___x_6100_ = v_reuseFailAlloc_6101_;
goto v_reusejp_6099_;
}
v_reusejp_6099_:
{
return v___x_6100_;
}
}
}
v___jp_6077_:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; 
v___x_6078_ = lean_box(0);
v___x_6079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
return v___x_6079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg___lam__0___boxed(lean_object* v_a_6103_, lean_object* v_a_6104_, lean_object* v_m_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_){
_start:
{
lean_object* v_res_6116_; 
v_res_6116_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg___lam__0(v_a_6103_, v_a_6104_, v_m_6105_, v___y_6106_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_);
lean_dec(v___y_6114_);
lean_dec_ref(v___y_6113_);
lean_dec(v___y_6112_);
lean_dec_ref(v___y_6111_);
lean_dec(v___y_6110_);
lean_dec_ref(v___y_6109_);
lean_dec(v___y_6108_);
lean_dec_ref(v___y_6107_);
lean_dec(v___y_6106_);
lean_dec(v_a_6104_);
lean_dec_ref(v_a_6103_);
return v_res_6116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg(lean_object* v_a_6117_, lean_object* v_a_6118_){
_start:
{
lean_object* v___f_6120_; lean_object* v___x_6121_; 
lean_inc(v_a_6118_);
lean_inc_ref(v_a_6117_);
v___f_6120_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_6120_, 0, v_a_6117_);
lean_closure_set(v___f_6120_, 1, v_a_6118_);
v___x_6121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6121_, 0, v___f_6120_);
return v___x_6121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg___boxed(lean_object* v_a_6122_, lean_object* v_a_6123_, lean_object* v_a_6124_){
_start:
{
lean_object* v_res_6125_; 
v_res_6125_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg(v_a_6122_, v_a_6123_);
lean_dec(v_a_6123_);
lean_dec_ref(v_a_6122_);
return v_res_6125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback(lean_object* v_a_6126_, lean_object* v_a_6127_, lean_object* v_a_6128_, lean_object* v_a_6129_, lean_object* v_a_6130_, lean_object* v_a_6131_, lean_object* v_a_6132_, lean_object* v_a_6133_, lean_object* v_a_6134_, lean_object* v_a_6135_, lean_object* v_a_6136_){
_start:
{
lean_object* v___x_6138_; 
v___x_6138_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg(v_a_6126_, v_a_6127_);
return v___x_6138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___boxed(lean_object* v_a_6139_, lean_object* v_a_6140_, lean_object* v_a_6141_, lean_object* v_a_6142_, lean_object* v_a_6143_, lean_object* v_a_6144_, lean_object* v_a_6145_, lean_object* v_a_6146_, lean_object* v_a_6147_, lean_object* v_a_6148_, lean_object* v_a_6149_, lean_object* v_a_6150_){
_start:
{
lean_object* v_res_6151_; 
v_res_6151_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback(v_a_6139_, v_a_6140_, v_a_6141_, v_a_6142_, v_a_6143_, v_a_6144_, v_a_6145_, v_a_6146_, v_a_6147_, v_a_6148_, v_a_6149_);
lean_dec(v_a_6149_);
lean_dec_ref(v_a_6148_);
lean_dec(v_a_6147_);
lean_dec_ref(v_a_6146_);
lean_dec(v_a_6145_);
lean_dec_ref(v_a_6144_);
lean_dec(v_a_6143_);
lean_dec_ref(v_a_6142_);
lean_dec(v_a_6141_);
lean_dec(v_a_6140_);
lean_dec_ref(v_a_6139_);
return v_res_6151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0(lean_object* v_mkOpAppM_6152_, lean_object* v_info_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_){
_start:
{
lean_object* v___x_6161_; 
lean_inc(v___y_6159_);
lean_inc_ref(v___y_6158_);
lean_inc(v___y_6157_);
lean_inc_ref(v___y_6156_);
v___x_6161_ = lean_apply_6(v_mkOpAppM_6152_, v_info_6153_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_, lean_box(0));
if (lean_obj_tag(v___x_6161_) == 0)
{
lean_object* v_a_6162_; lean_object* v___x_6163_; 
v_a_6162_ = lean_ctor_get(v___x_6161_, 0);
lean_inc(v_a_6162_);
lean_dec_ref_known(v___x_6161_, 1);
v___x_6163_ = l_Lean_Meta_Sym_shareCommon(v_a_6162_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_);
return v___x_6163_;
}
else
{
return v___x_6161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0___boxed(lean_object* v_mkOpAppM_6164_, lean_object* v_info_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_){
_start:
{
lean_object* v_res_6173_; 
v_res_6173_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0(v_mkOpAppM_6164_, v_info_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_);
lean_dec(v___y_6171_);
lean_dec_ref(v___y_6170_);
lean_dec(v___y_6169_);
lean_dec_ref(v___y_6168_);
lean_dec(v___y_6167_);
lean_dec_ref(v___y_6166_);
return v_res_6173_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(lean_object* v_a_6174_, lean_object* v_a_6175_){
_start:
{
if (lean_obj_tag(v_a_6174_) == 0)
{
lean_object* v___x_6176_; 
v___x_6176_ = l_List_reverse___redArg(v_a_6175_);
return v___x_6176_;
}
else
{
lean_object* v_head_6177_; lean_object* v_tail_6178_; lean_object* v___x_6180_; uint8_t v_isShared_6181_; uint8_t v_isSharedCheck_6187_; 
v_head_6177_ = lean_ctor_get(v_a_6174_, 0);
v_tail_6178_ = lean_ctor_get(v_a_6174_, 1);
v_isSharedCheck_6187_ = !lean_is_exclusive(v_a_6174_);
if (v_isSharedCheck_6187_ == 0)
{
v___x_6180_ = v_a_6174_;
v_isShared_6181_ = v_isSharedCheck_6187_;
goto v_resetjp_6179_;
}
else
{
lean_inc(v_tail_6178_);
lean_inc(v_head_6177_);
lean_dec(v_a_6174_);
v___x_6180_ = lean_box(0);
v_isShared_6181_ = v_isSharedCheck_6187_;
goto v_resetjp_6179_;
}
v_resetjp_6179_:
{
lean_object* v___x_6182_; lean_object* v___x_6184_; 
v___x_6182_ = l_Lean_MessageData_ofExpr(v_head_6177_);
if (v_isShared_6181_ == 0)
{
lean_ctor_set(v___x_6180_, 1, v_a_6175_);
lean_ctor_set(v___x_6180_, 0, v___x_6182_);
v___x_6184_ = v___x_6180_;
goto v_reusejp_6183_;
}
else
{
lean_object* v_reuseFailAlloc_6186_; 
v_reuseFailAlloc_6186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6186_, 0, v___x_6182_);
lean_ctor_set(v_reuseFailAlloc_6186_, 1, v_a_6175_);
v___x_6184_ = v_reuseFailAlloc_6186_;
goto v_reusejp_6183_;
}
v_reusejp_6183_:
{
v_a_6174_ = v_tail_6178_;
v_a_6175_ = v___x_6184_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1(void){
_start:
{
lean_object* v___x_6189_; lean_object* v___x_6190_; 
v___x_6189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__0));
v___x_6190_ = l_Lean_stringToMessageData(v___x_6189_);
return v___x_6190_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3(void){
_start:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; 
v___x_6192_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__2));
v___x_6193_ = l_Lean_stringToMessageData(v___x_6192_);
return v___x_6193_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5(void){
_start:
{
lean_object* v___x_6195_; lean_object* v___x_6196_; 
v___x_6195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__4));
v___x_6196_ = l_Lean_stringToMessageData(v___x_6195_);
return v___x_6196_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7(void){
_start:
{
lean_object* v___x_6198_; lean_object* v___x_6199_; 
v___x_6198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__6));
v___x_6199_ = l_Lean_stringToMessageData(v___x_6198_);
return v___x_6199_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9(void){
_start:
{
lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6201_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__8));
v___x_6202_ = l_Lean_stringToMessageData(v___x_6201_);
return v___x_6202_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11(void){
_start:
{
lean_object* v___x_6204_; lean_object* v___x_6205_; 
v___x_6204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__10));
v___x_6205_ = l_Lean_stringToMessageData(v___x_6204_);
return v___x_6205_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13(void){
_start:
{
lean_object* v___x_6207_; lean_object* v___x_6208_; 
v___x_6207_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__12));
v___x_6208_ = l_Lean_stringToMessageData(v___x_6207_);
return v___x_6208_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15(void){
_start:
{
lean_object* v___x_6210_; lean_object* v___x_6211_; 
v___x_6210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__14));
v___x_6211_ = l_Lean_stringToMessageData(v___x_6210_);
return v___x_6211_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17(void){
_start:
{
lean_object* v___x_6213_; lean_object* v___x_6214_; 
v___x_6213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__16));
v___x_6214_ = l_Lean_stringToMessageData(v___x_6213_);
return v___x_6214_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19(void){
_start:
{
lean_object* v___x_6216_; lean_object* v___x_6217_; 
v___x_6216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__18));
v___x_6217_ = l_Lean_stringToMessageData(v___x_6216_);
return v___x_6217_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__21(void){
_start:
{
lean_object* v___x_6219_; lean_object* v___x_6220_; 
v___x_6219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__20));
v___x_6220_ = l_Lean_stringToMessageData(v___x_6219_);
return v___x_6220_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__23(void){
_start:
{
lean_object* v___x_6222_; lean_object* v___x_6223_; 
v___x_6222_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__22));
v___x_6223_ = l_Lean_stringToMessageData(v___x_6222_);
return v___x_6223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(lean_object* v_scope_6224_, lean_object* v_goal_6225_, lean_object* v_info_6226_, lean_object* v_thm_6227_, lean_object* v_fp_6228_, lean_object* v_providedFrame_x3f_6229_, lean_object* v_a_6230_, lean_object* v_a_6231_, lean_object* v_a_6232_, lean_object* v_a_6233_, lean_object* v_a_6234_, lean_object* v_a_6235_, lean_object* v_a_6236_, lean_object* v_a_6237_, lean_object* v_a_6238_, lean_object* v_a_6239_, lean_object* v_a_6240_){
_start:
{
lean_object* v___y_6243_; lean_object* v___y_6244_; lean_object* v___y_6245_; lean_object* v___y_6246_; lean_object* v___y_6247_; lean_object* v___y_6248_; lean_object* v___y_6249_; lean_object* v___y_6250_; lean_object* v___y_6251_; lean_object* v___y_6252_; lean_object* v___y_6253_; lean_object* v___y_6254_; lean_object* v___y_6291_; lean_object* v___y_6292_; lean_object* v___y_6293_; lean_object* v___y_6294_; lean_object* v___y_6295_; lean_object* v___y_6296_; lean_object* v___y_6297_; lean_object* v___y_6298_; lean_object* v___y_6299_; lean_object* v___y_6300_; lean_object* v___y_6301_; lean_object* v___y_6302_; lean_object* v___y_6303_; lean_object* v___y_6304_; lean_object* v___y_6305_; lean_object* v___y_6330_; lean_object* v___y_6331_; lean_object* v___y_6332_; lean_object* v___y_6333_; lean_object* v___y_6334_; lean_object* v___y_6335_; lean_object* v___y_6336_; lean_object* v___y_6337_; lean_object* v___y_6338_; lean_object* v___y_6339_; lean_object* v___y_6340_; lean_object* v___y_6341_; lean_object* v___x_6369_; lean_object* v___y_6371_; lean_object* v___y_6372_; lean_object* v___y_6373_; lean_object* v___y_6374_; lean_object* v___y_6375_; lean_object* v___y_6376_; lean_object* v___y_6377_; lean_object* v___y_6412_; lean_object* v___y_6413_; lean_object* v___y_6414_; lean_object* v___y_6415_; lean_object* v___y_6416_; lean_object* v___y_6417_; lean_object* v___y_6418_; lean_object* v___y_6419_; lean_object* v___y_6420_; lean_object* v___y_6421_; lean_object* v___y_6422_; lean_object* v___y_6423_; lean_object* v___y_6424_; lean_object* v___y_6425_; lean_object* v___y_6426_; lean_object* v_a_6507_; lean_object* v___x_6580_; 
v___x_6369_ = lean_box(0);
lean_inc_ref(v_info_6226_);
lean_inc_ref(v_thm_6227_);
v___x_6580_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(v_thm_6227_, v_info_6226_, v_a_6230_, v_a_6231_, v_a_6232_, v_a_6233_, v_a_6234_, v_a_6235_, v_a_6236_, v_a_6237_, v_a_6238_, v_a_6239_, v_a_6240_);
if (lean_obj_tag(v___x_6580_) == 0)
{
lean_object* v_a_6581_; 
v_a_6581_ = lean_ctor_get(v___x_6580_, 0);
lean_inc(v_a_6581_);
lean_dec_ref_known(v___x_6580_, 1);
v_a_6507_ = v_a_6581_;
goto v___jp_6506_;
}
else
{
lean_object* v_a_6582_; lean_object* v___x_6584_; uint8_t v_isShared_6585_; uint8_t v_isSharedCheck_6662_; 
lean_dec(v_providedFrame_x3f_6229_);
lean_dec_ref(v_fp_6228_);
lean_dec_ref(v_scope_6224_);
v_a_6582_ = lean_ctor_get(v___x_6580_, 0);
v_isSharedCheck_6662_ = !lean_is_exclusive(v___x_6580_);
if (v_isSharedCheck_6662_ == 0)
{
v___x_6584_ = v___x_6580_;
v_isShared_6585_ = v_isSharedCheck_6662_;
goto v_resetjp_6583_;
}
else
{
lean_inc(v_a_6582_);
lean_dec(v___x_6580_);
v___x_6584_ = lean_box(0);
v_isShared_6585_ = v_isSharedCheck_6662_;
goto v_resetjp_6583_;
}
v_resetjp_6583_:
{
uint8_t v___x_6586_; 
v___x_6586_ = l_Lean_Exception_isInterrupt(v_a_6582_);
if (v___x_6586_ == 0)
{
uint8_t v___x_6587_; 
lean_inc(v_a_6582_);
v___x_6587_ = l_Lean_Exception_isRuntime(v_a_6582_);
if (v___x_6587_ == 0)
{
lean_object* v___x_6588_; 
lean_del_object(v___x_6584_);
v___x_6588_ = l_Lean_MVarId_getType(v_goal_6225_, v_a_6237_, v_a_6238_, v_a_6239_, v_a_6240_);
if (lean_obj_tag(v___x_6588_) == 0)
{
lean_object* v_a_6589_; lean_object* v_proof_6590_; lean_object* v___x_6591_; lean_object* v___y_6593_; 
v_a_6589_ = lean_ctor_get(v___x_6588_, 0);
lean_inc(v_a_6589_);
lean_dec_ref_known(v___x_6588_, 1);
v_proof_6590_ = lean_ctor_get(v_thm_6227_, 1);
lean_inc_ref(v_proof_6590_);
lean_dec_ref(v_thm_6227_);
v___x_6591_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__15);
switch(lean_obj_tag(v_proof_6590_))
{
case 0:
{
lean_object* v_declName_6630_; lean_object* v___x_6631_; lean_object* v___x_6632_; lean_object* v___x_6633_; 
v_declName_6630_ = lean_ctor_get(v_proof_6590_, 0);
lean_inc(v_declName_6630_);
lean_dec_ref_known(v_proof_6590_, 1);
v___x_6631_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_6632_ = l_Lean_MessageData_ofName(v_declName_6630_);
v___x_6633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6633_, 0, v___x_6631_);
lean_ctor_set(v___x_6633_, 1, v___x_6632_);
v___y_6593_ = v___x_6633_;
goto v___jp_6592_;
}
case 1:
{
lean_object* v_fvarId_6634_; lean_object* v___x_6635_; lean_object* v___x_6636_; lean_object* v___x_6637_; lean_object* v___x_6638_; 
v_fvarId_6634_ = lean_ctor_get(v_proof_6590_, 0);
lean_inc(v_fvarId_6634_);
lean_dec_ref_known(v_proof_6590_, 1);
v___x_6635_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_6636_ = l_Lean_mkFVar(v_fvarId_6634_);
v___x_6637_ = l_Lean_MessageData_ofExpr(v___x_6636_);
v___x_6638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6638_, 0, v___x_6635_);
lean_ctor_set(v___x_6638_, 1, v___x_6637_);
v___y_6593_ = v___x_6638_;
goto v___jp_6592_;
}
default: 
{
lean_object* v_ref_6639_; lean_object* v_proof_6640_; lean_object* v___x_6641_; lean_object* v___x_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; 
v_ref_6639_ = lean_ctor_get(v_proof_6590_, 1);
lean_inc(v_ref_6639_);
v_proof_6640_ = lean_ctor_get(v_proof_6590_, 2);
lean_inc_ref(v_proof_6640_);
lean_dec_ref_known(v_proof_6590_, 3);
v___x_6641_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_6642_ = l_Lean_MessageData_ofSyntax(v_ref_6639_);
v___x_6643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6643_, 0, v___x_6641_);
lean_ctor_set(v___x_6643_, 1, v___x_6642_);
v___x_6644_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_6645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6645_, 0, v___x_6643_);
lean_ctor_set(v___x_6645_, 1, v___x_6644_);
v___x_6646_ = l_Lean_MessageData_ofExpr(v_proof_6640_);
v___x_6647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6647_, 0, v___x_6645_);
lean_ctor_set(v___x_6647_, 1, v___x_6646_);
v___y_6593_ = v___x_6647_;
goto v___jp_6592_;
}
}
v___jp_6592_:
{
lean_object* v_excessArgs_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; lean_object* v___x_6599_; lean_object* v___x_6600_; lean_object* v___x_6601_; lean_object* v___x_6602_; lean_object* v___x_6603_; lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; lean_object* v___x_6614_; lean_object* v___x_6615_; lean_object* v___x_6616_; lean_object* v___x_6617_; lean_object* v___x_6618_; lean_object* v___x_6619_; lean_object* v___x_6620_; lean_object* v___x_6621_; lean_object* v_a_6622_; lean_object* v___x_6624_; uint8_t v_isShared_6625_; uint8_t v_isSharedCheck_6629_; 
v_excessArgs_6594_ = lean_ctor_get(v_info_6226_, 3);
lean_inc_ref(v_excessArgs_6594_);
v___x_6595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6595_, 0, v___x_6591_);
lean_ctor_set(v___x_6595_, 1, v___y_6593_);
v___x_6596_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_6597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6597_, 0, v___x_6595_);
lean_ctor_set(v___x_6597_, 1, v___x_6596_);
v___x_6598_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_6226_);
v___x_6599_ = l_Lean_indentExpr(v___x_6598_);
v___x_6600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6600_, 0, v___x_6597_);
lean_ctor_set(v___x_6600_, 1, v___x_6599_);
v___x_6601_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__17);
v___x_6602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6602_, 0, v___x_6600_);
lean_ctor_set(v___x_6602_, 1, v___x_6601_);
v___x_6603_ = l_Lean_Exception_toMessageData(v_a_6582_);
v___x_6604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6604_, 0, v___x_6602_);
lean_ctor_set(v___x_6604_, 1, v___x_6603_);
v___x_6605_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__19);
v___x_6606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6606_, 0, v___x_6604_);
lean_ctor_set(v___x_6606_, 1, v___x_6605_);
v___x_6607_ = l_Lean_indentExpr(v_a_6589_);
v___x_6608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6608_, 0, v___x_6606_);
lean_ctor_set(v___x_6608_, 1, v___x_6607_);
v___x_6609_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__21, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__21_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__21);
v___x_6610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6610_, 0, v___x_6608_);
lean_ctor_set(v___x_6610_, 1, v___x_6609_);
v___x_6611_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_6226_);
lean_dec_ref(v_info_6226_);
v___x_6612_ = l_Lean_indentExpr(v___x_6611_);
v___x_6613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6613_, 0, v___x_6610_);
lean_ctor_set(v___x_6613_, 1, v___x_6612_);
v___x_6614_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__23, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__23_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__23);
v___x_6615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6615_, 0, v___x_6613_);
lean_ctor_set(v___x_6615_, 1, v___x_6614_);
v___x_6616_ = lean_array_to_list(v_excessArgs_6594_);
v___x_6617_ = lean_box(0);
v___x_6618_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(v___x_6616_, v___x_6617_);
v___x_6619_ = l_Lean_MessageData_ofList(v___x_6618_);
v___x_6620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6620_, 0, v___x_6615_);
lean_ctor_set(v___x_6620_, 1, v___x_6619_);
v___x_6621_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_6620_, v_a_6237_, v_a_6238_, v_a_6239_, v_a_6240_);
v_a_6622_ = lean_ctor_get(v___x_6621_, 0);
v_isSharedCheck_6629_ = !lean_is_exclusive(v___x_6621_);
if (v_isSharedCheck_6629_ == 0)
{
v___x_6624_ = v___x_6621_;
v_isShared_6625_ = v_isSharedCheck_6629_;
goto v_resetjp_6623_;
}
else
{
lean_inc(v_a_6622_);
lean_dec(v___x_6621_);
v___x_6624_ = lean_box(0);
v_isShared_6625_ = v_isSharedCheck_6629_;
goto v_resetjp_6623_;
}
v_resetjp_6623_:
{
lean_object* v___x_6627_; 
if (v_isShared_6625_ == 0)
{
v___x_6627_ = v___x_6624_;
goto v_reusejp_6626_;
}
else
{
lean_object* v_reuseFailAlloc_6628_; 
v_reuseFailAlloc_6628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6628_, 0, v_a_6622_);
v___x_6627_ = v_reuseFailAlloc_6628_;
goto v_reusejp_6626_;
}
v_reusejp_6626_:
{
return v___x_6627_;
}
}
}
}
else
{
lean_object* v_a_6648_; lean_object* v___x_6650_; uint8_t v_isShared_6651_; uint8_t v_isSharedCheck_6655_; 
lean_dec(v_a_6582_);
lean_dec_ref(v_thm_6227_);
lean_dec_ref(v_info_6226_);
v_a_6648_ = lean_ctor_get(v___x_6588_, 0);
v_isSharedCheck_6655_ = !lean_is_exclusive(v___x_6588_);
if (v_isSharedCheck_6655_ == 0)
{
v___x_6650_ = v___x_6588_;
v_isShared_6651_ = v_isSharedCheck_6655_;
goto v_resetjp_6649_;
}
else
{
lean_inc(v_a_6648_);
lean_dec(v___x_6588_);
v___x_6650_ = lean_box(0);
v_isShared_6651_ = v_isSharedCheck_6655_;
goto v_resetjp_6649_;
}
v_resetjp_6649_:
{
lean_object* v___x_6653_; 
if (v_isShared_6651_ == 0)
{
v___x_6653_ = v___x_6650_;
goto v_reusejp_6652_;
}
else
{
lean_object* v_reuseFailAlloc_6654_; 
v_reuseFailAlloc_6654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6654_, 0, v_a_6648_);
v___x_6653_ = v_reuseFailAlloc_6654_;
goto v_reusejp_6652_;
}
v_reusejp_6652_:
{
return v___x_6653_;
}
}
}
}
else
{
lean_object* v___x_6657_; 
lean_dec_ref(v_thm_6227_);
lean_dec_ref(v_info_6226_);
lean_dec(v_goal_6225_);
if (v_isShared_6585_ == 0)
{
v___x_6657_ = v___x_6584_;
goto v_reusejp_6656_;
}
else
{
lean_object* v_reuseFailAlloc_6658_; 
v_reuseFailAlloc_6658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6658_, 0, v_a_6582_);
v___x_6657_ = v_reuseFailAlloc_6658_;
goto v_reusejp_6656_;
}
v_reusejp_6656_:
{
return v___x_6657_;
}
}
}
else
{
lean_object* v___x_6660_; 
lean_dec_ref(v_thm_6227_);
lean_dec_ref(v_info_6226_);
lean_dec(v_goal_6225_);
if (v_isShared_6585_ == 0)
{
v___x_6660_ = v___x_6584_;
goto v_reusejp_6659_;
}
else
{
lean_object* v_reuseFailAlloc_6661_; 
v_reuseFailAlloc_6661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6661_, 0, v_a_6582_);
v___x_6660_ = v_reuseFailAlloc_6661_;
goto v_reusejp_6659_;
}
v_reusejp_6659_:
{
return v___x_6660_;
}
}
}
}
v___jp_6242_:
{
lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6260_; 
v___x_6255_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__1);
v___x_6256_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_6226_);
lean_dec_ref(v_info_6226_);
v___x_6257_ = l_Lean_indentExpr(v___x_6256_);
v___x_6258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6258_, 0, v___x_6255_);
lean_ctor_set(v___x_6258_, 1, v___x_6257_);
v___x_6259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6259_, 0, v___x_6258_);
v___x_6260_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v___y_6243_, v_goal_6225_, v___x_6259_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_);
if (lean_obj_tag(v___x_6260_) == 0)
{
lean_object* v_a_6261_; lean_object* v___x_6263_; uint8_t v_isShared_6264_; uint8_t v_isSharedCheck_6281_; 
v_a_6261_ = lean_ctor_get(v___x_6260_, 0);
v_isSharedCheck_6281_ = !lean_is_exclusive(v___x_6260_);
if (v_isSharedCheck_6281_ == 0)
{
v___x_6263_ = v___x_6260_;
v_isShared_6264_ = v_isSharedCheck_6281_;
goto v_resetjp_6262_;
}
else
{
lean_inc(v_a_6261_);
lean_dec(v___x_6260_);
v___x_6263_ = lean_box(0);
v_isShared_6264_ = v_isSharedCheck_6281_;
goto v_resetjp_6262_;
}
v_resetjp_6262_:
{
if (lean_obj_tag(v_a_6261_) == 1)
{
lean_object* v_mvarIds_6265_; lean_object* v___x_6267_; uint8_t v_isShared_6268_; uint8_t v_isSharedCheck_6276_; 
v_mvarIds_6265_ = lean_ctor_get(v_a_6261_, 0);
v_isSharedCheck_6276_ = !lean_is_exclusive(v_a_6261_);
if (v_isSharedCheck_6276_ == 0)
{
v___x_6267_ = v_a_6261_;
v_isShared_6268_ = v_isSharedCheck_6276_;
goto v_resetjp_6266_;
}
else
{
lean_inc(v_mvarIds_6265_);
lean_dec(v_a_6261_);
v___x_6267_ = lean_box(0);
v_isShared_6268_ = v_isSharedCheck_6276_;
goto v_resetjp_6266_;
}
v_resetjp_6266_:
{
lean_object* v___x_6269_; lean_object* v___x_6271_; 
v___x_6269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6269_, 0, v_scope_6224_);
lean_ctor_set(v___x_6269_, 1, v_mvarIds_6265_);
if (v_isShared_6268_ == 0)
{
lean_ctor_set(v___x_6267_, 0, v___x_6269_);
v___x_6271_ = v___x_6267_;
goto v_reusejp_6270_;
}
else
{
lean_object* v_reuseFailAlloc_6275_; 
v_reuseFailAlloc_6275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6275_, 0, v___x_6269_);
v___x_6271_ = v_reuseFailAlloc_6275_;
goto v_reusejp_6270_;
}
v_reusejp_6270_:
{
lean_object* v___x_6273_; 
if (v_isShared_6264_ == 0)
{
lean_ctor_set(v___x_6263_, 0, v___x_6271_);
v___x_6273_ = v___x_6263_;
goto v_reusejp_6272_;
}
else
{
lean_object* v_reuseFailAlloc_6274_; 
v_reuseFailAlloc_6274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6274_, 0, v___x_6271_);
v___x_6273_ = v_reuseFailAlloc_6274_;
goto v_reusejp_6272_;
}
v_reusejp_6272_:
{
return v___x_6273_;
}
}
}
}
else
{
lean_object* v___x_6277_; lean_object* v___x_6279_; 
lean_dec(v_a_6261_);
lean_dec_ref(v_scope_6224_);
v___x_6277_ = lean_box(0);
if (v_isShared_6264_ == 0)
{
lean_ctor_set(v___x_6263_, 0, v___x_6277_);
v___x_6279_ = v___x_6263_;
goto v_reusejp_6278_;
}
else
{
lean_object* v_reuseFailAlloc_6280_; 
v_reuseFailAlloc_6280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6280_, 0, v___x_6277_);
v___x_6279_ = v_reuseFailAlloc_6280_;
goto v_reusejp_6278_;
}
v_reusejp_6278_:
{
return v___x_6279_;
}
}
}
}
else
{
lean_object* v_a_6282_; lean_object* v___x_6284_; uint8_t v_isShared_6285_; uint8_t v_isSharedCheck_6289_; 
lean_dec_ref(v_scope_6224_);
v_a_6282_ = lean_ctor_get(v___x_6260_, 0);
v_isSharedCheck_6289_ = !lean_is_exclusive(v___x_6260_);
if (v_isSharedCheck_6289_ == 0)
{
v___x_6284_ = v___x_6260_;
v_isShared_6285_ = v_isSharedCheck_6289_;
goto v_resetjp_6283_;
}
else
{
lean_inc(v_a_6282_);
lean_dec(v___x_6260_);
v___x_6284_ = lean_box(0);
v_isShared_6285_ = v_isSharedCheck_6289_;
goto v_resetjp_6283_;
}
v_resetjp_6283_:
{
lean_object* v___x_6287_; 
if (v_isShared_6285_ == 0)
{
v___x_6287_ = v___x_6284_;
goto v_reusejp_6286_;
}
else
{
lean_object* v_reuseFailAlloc_6288_; 
v_reuseFailAlloc_6288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6288_, 0, v_a_6282_);
v___x_6287_ = v_reuseFailAlloc_6288_;
goto v_reusejp_6286_;
}
v_reusejp_6286_:
{
return v___x_6287_;
}
}
}
}
v___jp_6290_:
{
lean_object* v_excessArgs_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; lean_object* v___x_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; 
v_excessArgs_6306_ = lean_ctor_get(v_info_6226_, 3);
lean_inc_ref(v___y_6298_);
v___x_6307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6307_, 0, v___y_6298_);
lean_ctor_set(v___x_6307_, 1, v___y_6305_);
v___x_6308_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_6309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6309_, 0, v___x_6307_);
lean_ctor_set(v___x_6309_, 1, v___x_6308_);
v___x_6310_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_6226_);
v___x_6311_ = l_Lean_MessageData_ofExpr(v___x_6310_);
v___x_6312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6312_, 0, v___x_6309_);
lean_ctor_set(v___x_6312_, 1, v___x_6311_);
v___x_6313_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__5);
v___x_6314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6314_, 0, v___x_6312_);
lean_ctor_set(v___x_6314_, 1, v___x_6313_);
lean_inc_ref(v_excessArgs_6306_);
v___x_6315_ = lean_array_to_list(v_excessArgs_6306_);
v___x_6316_ = lean_box(0);
v___x_6317_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec_spec__0(v___x_6315_, v___x_6316_);
v___x_6318_ = l_Lean_MessageData_ofList(v___x_6317_);
v___x_6319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6319_, 0, v___x_6314_);
lean_ctor_set(v___x_6319_, 1, v___x_6318_);
lean_inc(v___y_6301_);
v___x_6320_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___y_6301_, v___x_6319_, v___y_6296_, v___y_6291_, v___y_6294_, v___y_6302_);
if (lean_obj_tag(v___x_6320_) == 0)
{
lean_dec_ref_known(v___x_6320_, 1);
v___y_6243_ = v___y_6295_;
v___y_6244_ = v___y_6303_;
v___y_6245_ = v___y_6292_;
v___y_6246_ = v___y_6293_;
v___y_6247_ = v___y_6299_;
v___y_6248_ = v___y_6304_;
v___y_6249_ = v___y_6300_;
v___y_6250_ = v___y_6297_;
v___y_6251_ = v___y_6296_;
v___y_6252_ = v___y_6291_;
v___y_6253_ = v___y_6294_;
v___y_6254_ = v___y_6302_;
goto v___jp_6242_;
}
else
{
lean_object* v_a_6321_; lean_object* v___x_6323_; uint8_t v_isShared_6324_; uint8_t v_isSharedCheck_6328_; 
lean_dec_ref(v___y_6295_);
lean_dec_ref(v_info_6226_);
lean_dec(v_goal_6225_);
lean_dec_ref(v_scope_6224_);
v_a_6321_ = lean_ctor_get(v___x_6320_, 0);
v_isSharedCheck_6328_ = !lean_is_exclusive(v___x_6320_);
if (v_isSharedCheck_6328_ == 0)
{
v___x_6323_ = v___x_6320_;
v_isShared_6324_ = v_isSharedCheck_6328_;
goto v_resetjp_6322_;
}
else
{
lean_inc(v_a_6321_);
lean_dec(v___x_6320_);
v___x_6323_ = lean_box(0);
v_isShared_6324_ = v_isSharedCheck_6328_;
goto v_resetjp_6322_;
}
v_resetjp_6322_:
{
lean_object* v___x_6326_; 
if (v_isShared_6324_ == 0)
{
v___x_6326_ = v___x_6323_;
goto v_reusejp_6325_;
}
else
{
lean_object* v_reuseFailAlloc_6327_; 
v_reuseFailAlloc_6327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6327_, 0, v_a_6321_);
v___x_6326_ = v_reuseFailAlloc_6327_;
goto v_reusejp_6325_;
}
v_reusejp_6325_:
{
return v___x_6326_;
}
}
}
}
v___jp_6329_:
{
lean_object* v_toCold_6342_; lean_object* v_options_6343_; uint8_t v_hasTrace_6344_; 
v_toCold_6342_ = lean_ctor_get(v___y_6340_, 0);
v_options_6343_ = lean_ctor_get(v_toCold_6342_, 2);
v_hasTrace_6344_ = lean_ctor_get_uint8(v_options_6343_, sizeof(void*)*1);
if (v_hasTrace_6344_ == 0)
{
lean_dec_ref(v_thm_6227_);
v___y_6243_ = v___y_6330_;
v___y_6244_ = v___y_6331_;
v___y_6245_ = v___y_6332_;
v___y_6246_ = v___y_6333_;
v___y_6247_ = v___y_6334_;
v___y_6248_ = v___y_6335_;
v___y_6249_ = v___y_6336_;
v___y_6250_ = v___y_6337_;
v___y_6251_ = v___y_6338_;
v___y_6252_ = v___y_6339_;
v___y_6253_ = v___y_6340_;
v___y_6254_ = v___y_6341_;
goto v___jp_6242_;
}
else
{
lean_object* v_inheritedTraceOptions_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; uint8_t v___x_6348_; 
v_inheritedTraceOptions_6345_ = lean_ctor_get(v_toCold_6342_, 11);
v___x_6346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_6347_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_6348_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6345_, v_options_6343_, v___x_6347_);
if (v___x_6348_ == 0)
{
lean_dec_ref(v_thm_6227_);
v___y_6243_ = v___y_6330_;
v___y_6244_ = v___y_6331_;
v___y_6245_ = v___y_6332_;
v___y_6246_ = v___y_6333_;
v___y_6247_ = v___y_6334_;
v___y_6248_ = v___y_6335_;
v___y_6249_ = v___y_6336_;
v___y_6250_ = v___y_6337_;
v___y_6251_ = v___y_6338_;
v___y_6252_ = v___y_6339_;
v___y_6253_ = v___y_6340_;
v___y_6254_ = v___y_6341_;
goto v___jp_6242_;
}
else
{
lean_object* v_proof_6349_; lean_object* v___x_6350_; 
v_proof_6349_ = lean_ctor_get(v_thm_6227_, 1);
lean_inc_ref(v_proof_6349_);
lean_dec_ref(v_thm_6227_);
v___x_6350_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__7);
switch(lean_obj_tag(v_proof_6349_))
{
case 0:
{
lean_object* v_declName_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; 
v_declName_6351_ = lean_ctor_get(v_proof_6349_, 0);
lean_inc(v_declName_6351_);
lean_dec_ref_known(v_proof_6349_, 1);
v___x_6352_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_6353_ = l_Lean_MessageData_ofName(v_declName_6351_);
v___x_6354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6354_, 0, v___x_6352_);
lean_ctor_set(v___x_6354_, 1, v___x_6353_);
v___y_6291_ = v___y_6339_;
v___y_6292_ = v___y_6332_;
v___y_6293_ = v___y_6333_;
v___y_6294_ = v___y_6340_;
v___y_6295_ = v___y_6330_;
v___y_6296_ = v___y_6338_;
v___y_6297_ = v___y_6337_;
v___y_6298_ = v___x_6350_;
v___y_6299_ = v___y_6334_;
v___y_6300_ = v___y_6336_;
v___y_6301_ = v___x_6346_;
v___y_6302_ = v___y_6341_;
v___y_6303_ = v___y_6331_;
v___y_6304_ = v___y_6335_;
v___y_6305_ = v___x_6354_;
goto v___jp_6290_;
}
case 1:
{
lean_object* v_fvarId_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; 
v_fvarId_6355_ = lean_ctor_get(v_proof_6349_, 0);
lean_inc(v_fvarId_6355_);
lean_dec_ref_known(v_proof_6349_, 1);
v___x_6356_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_6357_ = l_Lean_mkFVar(v_fvarId_6355_);
v___x_6358_ = l_Lean_MessageData_ofExpr(v___x_6357_);
v___x_6359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6359_, 0, v___x_6356_);
lean_ctor_set(v___x_6359_, 1, v___x_6358_);
v___y_6291_ = v___y_6339_;
v___y_6292_ = v___y_6332_;
v___y_6293_ = v___y_6333_;
v___y_6294_ = v___y_6340_;
v___y_6295_ = v___y_6330_;
v___y_6296_ = v___y_6338_;
v___y_6297_ = v___y_6337_;
v___y_6298_ = v___x_6350_;
v___y_6299_ = v___y_6334_;
v___y_6300_ = v___y_6336_;
v___y_6301_ = v___x_6346_;
v___y_6302_ = v___y_6341_;
v___y_6303_ = v___y_6331_;
v___y_6304_ = v___y_6335_;
v___y_6305_ = v___x_6359_;
goto v___jp_6290_;
}
default: 
{
lean_object* v_ref_6360_; lean_object* v_proof_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; lean_object* v___x_6368_; 
v_ref_6360_ = lean_ctor_get(v_proof_6349_, 1);
lean_inc(v_ref_6360_);
v_proof_6361_ = lean_ctor_get(v_proof_6349_, 2);
lean_inc_ref(v_proof_6361_);
lean_dec_ref_known(v_proof_6349_, 3);
v___x_6362_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_6363_ = l_Lean_MessageData_ofSyntax(v_ref_6360_);
v___x_6364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6364_, 0, v___x_6362_);
lean_ctor_set(v___x_6364_, 1, v___x_6363_);
v___x_6365_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_6366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6366_, 0, v___x_6364_);
lean_ctor_set(v___x_6366_, 1, v___x_6365_);
v___x_6367_ = l_Lean_MessageData_ofExpr(v_proof_6361_);
v___x_6368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6368_, 0, v___x_6366_);
lean_ctor_set(v___x_6368_, 1, v___x_6367_);
v___y_6291_ = v___y_6339_;
v___y_6292_ = v___y_6332_;
v___y_6293_ = v___y_6333_;
v___y_6294_ = v___y_6340_;
v___y_6295_ = v___y_6330_;
v___y_6296_ = v___y_6338_;
v___y_6297_ = v___y_6337_;
v___y_6298_ = v___x_6350_;
v___y_6299_ = v___y_6334_;
v___y_6300_ = v___y_6336_;
v___y_6301_ = v___x_6346_;
v___y_6302_ = v___y_6341_;
v___y_6303_ = v___y_6331_;
v___y_6304_ = v___y_6335_;
v___y_6305_ = v___x_6368_;
goto v___jp_6290_;
}
}
}
}
}
v___jp_6370_:
{
lean_object* v_splitVCProof_6378_; lean_object* v_subgoals_6379_; lean_object* v___x_6381_; uint8_t v_isShared_6382_; uint8_t v_isSharedCheck_6410_; 
v_splitVCProof_6378_ = lean_ctor_get(v___y_6374_, 0);
v_subgoals_6379_ = lean_ctor_get(v___y_6374_, 1);
v_isSharedCheck_6410_ = !lean_is_exclusive(v___y_6374_);
if (v_isSharedCheck_6410_ == 0)
{
v___x_6381_ = v___y_6374_;
v_isShared_6382_ = v_isSharedCheck_6410_;
goto v_resetjp_6380_;
}
else
{
lean_inc(v_subgoals_6379_);
lean_inc(v_splitVCProof_6378_);
lean_dec(v___y_6374_);
v___x_6381_ = lean_box(0);
v_isShared_6382_ = v_isSharedCheck_6410_;
goto v_resetjp_6380_;
}
v_resetjp_6380_:
{
lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v___x_6386_; uint8_t v_isShared_6387_; uint8_t v_isSharedCheck_6408_; 
v___x_6383_ = lean_array_get_borrowed(v___x_6369_, v___y_6375_, v___y_6373_);
lean_dec(v___y_6373_);
lean_inc(v___x_6383_);
v___x_6384_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg(v___x_6383_, v_splitVCProof_6378_, v___y_6377_);
v_isSharedCheck_6408_ = !lean_is_exclusive(v___x_6384_);
if (v_isSharedCheck_6408_ == 0)
{
lean_object* v_unused_6409_; 
v_unused_6409_ = lean_ctor_get(v___x_6384_, 0);
lean_dec(v_unused_6409_);
v___x_6386_ = v___x_6384_;
v_isShared_6387_ = v_isSharedCheck_6408_;
goto v_resetjp_6385_;
}
else
{
lean_dec(v___x_6384_);
v___x_6386_ = lean_box(0);
v_isShared_6387_ = v_isSharedCheck_6408_;
goto v_resetjp_6385_;
}
v_resetjp_6385_:
{
lean_object* v___x_6388_; lean_object* v___x_6390_; uint8_t v_isShared_6391_; uint8_t v_isSharedCheck_6406_; 
v___x_6388_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__2___redArg(v_goal_6225_, v___y_6376_, v___y_6377_);
v_isSharedCheck_6406_ = !lean_is_exclusive(v___x_6388_);
if (v_isSharedCheck_6406_ == 0)
{
lean_object* v_unused_6407_; 
v_unused_6407_ = lean_ctor_get(v___x_6388_, 0);
lean_dec(v_unused_6407_);
v___x_6390_ = v___x_6388_;
v_isShared_6391_ = v_isSharedCheck_6406_;
goto v_resetjp_6389_;
}
else
{
lean_dec(v___x_6388_);
v___x_6390_ = lean_box(0);
v_isShared_6391_ = v_isSharedCheck_6406_;
goto v_resetjp_6389_;
}
v_resetjp_6389_:
{
lean_object* v_preVC_6392_; lean_object* v___x_6393_; lean_object* v___x_6395_; 
v_preVC_6392_ = lean_ctor_get(v___y_6372_, 4);
lean_inc(v_preVC_6392_);
lean_dec_ref(v___y_6372_);
v___x_6393_ = lean_array_to_list(v___y_6375_);
if (v_isShared_6382_ == 0)
{
lean_ctor_set_tag(v___x_6381_, 1);
lean_ctor_set(v___x_6381_, 1, v___y_6371_);
lean_ctor_set(v___x_6381_, 0, v_preVC_6392_);
v___x_6395_ = v___x_6381_;
goto v_reusejp_6394_;
}
else
{
lean_object* v_reuseFailAlloc_6405_; 
v_reuseFailAlloc_6405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6405_, 0, v_preVC_6392_);
lean_ctor_set(v_reuseFailAlloc_6405_, 1, v___y_6371_);
v___x_6395_ = v_reuseFailAlloc_6405_;
goto v_reusejp_6394_;
}
v_reusejp_6394_:
{
lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6400_; 
v___x_6396_ = l_List_appendTR___redArg(v___x_6393_, v___x_6395_);
v___x_6397_ = l_List_appendTR___redArg(v___x_6396_, v_subgoals_6379_);
v___x_6398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6398_, 0, v_scope_6224_);
lean_ctor_set(v___x_6398_, 1, v___x_6397_);
if (v_isShared_6387_ == 0)
{
lean_ctor_set_tag(v___x_6386_, 1);
lean_ctor_set(v___x_6386_, 0, v___x_6398_);
v___x_6400_ = v___x_6386_;
goto v_reusejp_6399_;
}
else
{
lean_object* v_reuseFailAlloc_6404_; 
v_reuseFailAlloc_6404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6404_, 0, v___x_6398_);
v___x_6400_ = v_reuseFailAlloc_6404_;
goto v_reusejp_6399_;
}
v_reusejp_6399_:
{
lean_object* v___x_6402_; 
if (v_isShared_6391_ == 0)
{
lean_ctor_set(v___x_6390_, 0, v___x_6400_);
v___x_6402_ = v___x_6390_;
goto v_reusejp_6401_;
}
else
{
lean_object* v_reuseFailAlloc_6403_; 
v_reuseFailAlloc_6403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6403_, 0, v___x_6400_);
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
}
}
v___jp_6411_:
{
lean_object* v___x_6427_; 
lean_inc_ref(v_info_6226_);
lean_inc(v_goal_6225_);
v___x_6427_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_commitFrameRule(v_goal_6225_, v_info_6226_, v_fp_6228_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_, v___y_6425_, v___y_6426_);
if (lean_obj_tag(v___x_6427_) == 0)
{
lean_object* v_a_6428_; lean_object* v_snd_6429_; lean_object* v_snd_6430_; lean_object* v_fst_6431_; lean_object* v_fst_6432_; lean_object* v_fst_6433_; lean_object* v_snd_6434_; lean_object* v___x_6435_; lean_object* v_a_6436_; lean_object* v_splitVCIdx_6437_; lean_object* v_frameIdx_6438_; lean_object* v___x_6439_; lean_object* v___x_6440_; 
v_a_6428_ = lean_ctor_get(v___x_6427_, 0);
lean_inc(v_a_6428_);
lean_dec_ref_known(v___x_6427_, 1);
v_snd_6429_ = lean_ctor_get(v_a_6428_, 1);
lean_inc(v_snd_6429_);
v_snd_6430_ = lean_ctor_get(v_snd_6429_, 1);
lean_inc(v_snd_6430_);
v_fst_6431_ = lean_ctor_get(v_a_6428_, 0);
lean_inc(v_fst_6431_);
lean_dec(v_a_6428_);
v_fst_6432_ = lean_ctor_get(v_snd_6429_, 0);
lean_inc(v_fst_6432_);
lean_dec(v_snd_6429_);
v_fst_6433_ = lean_ctor_get(v_snd_6430_, 0);
lean_inc(v_fst_6433_);
v_snd_6434_ = lean_ctor_get(v_snd_6430_, 1);
lean_inc(v_snd_6434_);
lean_dec(v_snd_6430_);
v___x_6435_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitLatticeOpCallback___redArg(v___y_6416_, v___y_6417_);
v_a_6436_ = lean_ctor_get(v___x_6435_, 0);
lean_inc(v_a_6436_);
lean_dec_ref(v___x_6435_);
v_splitVCIdx_6437_ = lean_ctor_get(v_fst_6432_, 1);
lean_inc(v_splitVCIdx_6437_);
v_frameIdx_6438_ = lean_ctor_get(v_fst_6432_, 2);
lean_inc(v_frameIdx_6438_);
lean_dec(v_fst_6432_);
v___x_6439_ = lean_array_get_borrowed(v___x_6369_, v_fst_6433_, v_frameIdx_6438_);
lean_dec(v_frameIdx_6438_);
lean_inc(v___x_6439_);
v___x_6440_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecToFootprint(v_info_6226_, v___y_6414_, v___y_6415_, v_snd_6434_, v___y_6413_, v___x_6439_, v_a_6436_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_, v___y_6425_, v___y_6426_);
lean_dec_ref(v___y_6413_);
if (lean_obj_tag(v___x_6440_) == 0)
{
lean_object* v_a_6441_; lean_object* v___x_6443_; uint8_t v_isShared_6444_; uint8_t v_isSharedCheck_6489_; 
v_a_6441_ = lean_ctor_get(v___x_6440_, 0);
v_isSharedCheck_6489_ = !lean_is_exclusive(v___x_6440_);
if (v_isSharedCheck_6489_ == 0)
{
v___x_6443_ = v___x_6440_;
v_isShared_6444_ = v_isSharedCheck_6489_;
goto v_resetjp_6442_;
}
else
{
lean_inc(v_a_6441_);
lean_dec(v___x_6440_);
v___x_6443_ = lean_box(0);
v_isShared_6444_ = v_isSharedCheck_6489_;
goto v_resetjp_6442_;
}
v_resetjp_6442_:
{
if (lean_obj_tag(v_a_6441_) == 1)
{
lean_object* v_val_6445_; lean_object* v_fst_6446_; lean_object* v_snd_6447_; lean_object* v___x_6449_; uint8_t v_isShared_6450_; uint8_t v_isSharedCheck_6484_; 
lean_del_object(v___x_6443_);
v_val_6445_ = lean_ctor_get(v_a_6441_, 0);
lean_inc(v_val_6445_);
lean_dec_ref_known(v_a_6441_, 1);
v_fst_6446_ = lean_ctor_get(v_val_6445_, 0);
v_snd_6447_ = lean_ctor_get(v_val_6445_, 1);
v_isSharedCheck_6484_ = !lean_is_exclusive(v_val_6445_);
if (v_isSharedCheck_6484_ == 0)
{
v___x_6449_ = v_val_6445_;
v_isShared_6450_ = v_isSharedCheck_6484_;
goto v_resetjp_6448_;
}
else
{
lean_inc(v_snd_6447_);
lean_inc(v_fst_6446_);
lean_dec(v_val_6445_);
v___x_6449_ = lean_box(0);
v_isShared_6450_ = v_isSharedCheck_6484_;
goto v_resetjp_6448_;
}
v_resetjp_6448_:
{
lean_object* v___x_6451_; 
lean_inc(v___y_6426_);
lean_inc_ref(v___y_6425_);
lean_inc(v___y_6424_);
lean_inc_ref(v___y_6423_);
lean_inc(v___y_6422_);
lean_inc_ref(v___y_6421_);
lean_inc(v___y_6420_);
lean_inc_ref(v___y_6419_);
lean_inc(v___y_6418_);
lean_inc(v_fst_6446_);
v___x_6451_ = lean_apply_11(v___y_6412_, v_fst_6446_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_, v___y_6425_, v___y_6426_, lean_box(0));
if (lean_obj_tag(v___x_6451_) == 0)
{
lean_object* v_toCold_6452_; lean_object* v_options_6453_; uint8_t v_hasTrace_6454_; 
v_toCold_6452_ = lean_ctor_get(v___y_6425_, 0);
v_options_6453_ = lean_ctor_get(v_toCold_6452_, 2);
v_hasTrace_6454_ = lean_ctor_get_uint8(v_options_6453_, sizeof(void*)*1);
if (v_hasTrace_6454_ == 0)
{
lean_object* v_a_6455_; 
lean_del_object(v___x_6449_);
lean_dec_ref(v_info_6226_);
v_a_6455_ = lean_ctor_get(v___x_6451_, 0);
lean_inc(v_a_6455_);
lean_dec_ref_known(v___x_6451_, 1);
v___y_6371_ = v_snd_6447_;
v___y_6372_ = v_fst_6446_;
v___y_6373_ = v_splitVCIdx_6437_;
v___y_6374_ = v_a_6455_;
v___y_6375_ = v_fst_6433_;
v___y_6376_ = v_fst_6431_;
v___y_6377_ = v___y_6424_;
goto v___jp_6370_;
}
else
{
lean_object* v_a_6456_; lean_object* v_inheritedTraceOptions_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; uint8_t v___x_6460_; 
v_a_6456_ = lean_ctor_get(v___x_6451_, 0);
lean_inc(v_a_6456_);
lean_dec_ref_known(v___x_6451_, 1);
v_inheritedTraceOptions_6457_ = lean_ctor_get(v_toCold_6452_, 11);
v___x_6458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_6459_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_6460_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6457_, v_options_6453_, v___x_6459_);
if (v___x_6460_ == 0)
{
lean_del_object(v___x_6449_);
lean_dec_ref(v_info_6226_);
v___y_6371_ = v_snd_6447_;
v___y_6372_ = v_fst_6446_;
v___y_6373_ = v_splitVCIdx_6437_;
v___y_6374_ = v_a_6456_;
v___y_6375_ = v_fst_6433_;
v___y_6376_ = v_fst_6431_;
v___y_6377_ = v___y_6424_;
goto v___jp_6370_;
}
else
{
lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___x_6465_; 
v___x_6461_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__9);
v___x_6462_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_6226_);
lean_dec_ref(v_info_6226_);
v___x_6463_ = l_Lean_MessageData_ofExpr(v___x_6462_);
if (v_isShared_6450_ == 0)
{
lean_ctor_set_tag(v___x_6449_, 7);
lean_ctor_set(v___x_6449_, 1, v___x_6463_);
lean_ctor_set(v___x_6449_, 0, v___x_6461_);
v___x_6465_ = v___x_6449_;
goto v_reusejp_6464_;
}
else
{
lean_object* v_reuseFailAlloc_6475_; 
v_reuseFailAlloc_6475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6475_, 0, v___x_6461_);
lean_ctor_set(v_reuseFailAlloc_6475_, 1, v___x_6463_);
v___x_6465_ = v_reuseFailAlloc_6475_;
goto v_reusejp_6464_;
}
v_reusejp_6464_:
{
lean_object* v___x_6466_; 
v___x_6466_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_6458_, v___x_6465_, v___y_6423_, v___y_6424_, v___y_6425_, v___y_6426_);
if (lean_obj_tag(v___x_6466_) == 0)
{
lean_dec_ref_known(v___x_6466_, 1);
v___y_6371_ = v_snd_6447_;
v___y_6372_ = v_fst_6446_;
v___y_6373_ = v_splitVCIdx_6437_;
v___y_6374_ = v_a_6456_;
v___y_6375_ = v_fst_6433_;
v___y_6376_ = v_fst_6431_;
v___y_6377_ = v___y_6424_;
goto v___jp_6370_;
}
else
{
lean_object* v_a_6467_; lean_object* v___x_6469_; uint8_t v_isShared_6470_; uint8_t v_isSharedCheck_6474_; 
lean_dec(v_a_6456_);
lean_dec(v_snd_6447_);
lean_dec(v_fst_6446_);
lean_dec(v_splitVCIdx_6437_);
lean_dec(v_fst_6433_);
lean_dec(v_fst_6431_);
lean_dec(v_goal_6225_);
lean_dec_ref(v_scope_6224_);
v_a_6467_ = lean_ctor_get(v___x_6466_, 0);
v_isSharedCheck_6474_ = !lean_is_exclusive(v___x_6466_);
if (v_isSharedCheck_6474_ == 0)
{
v___x_6469_ = v___x_6466_;
v_isShared_6470_ = v_isSharedCheck_6474_;
goto v_resetjp_6468_;
}
else
{
lean_inc(v_a_6467_);
lean_dec(v___x_6466_);
v___x_6469_ = lean_box(0);
v_isShared_6470_ = v_isSharedCheck_6474_;
goto v_resetjp_6468_;
}
v_resetjp_6468_:
{
lean_object* v___x_6472_; 
if (v_isShared_6470_ == 0)
{
v___x_6472_ = v___x_6469_;
goto v_reusejp_6471_;
}
else
{
lean_object* v_reuseFailAlloc_6473_; 
v_reuseFailAlloc_6473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6473_, 0, v_a_6467_);
v___x_6472_ = v_reuseFailAlloc_6473_;
goto v_reusejp_6471_;
}
v_reusejp_6471_:
{
return v___x_6472_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6476_; lean_object* v___x_6478_; uint8_t v_isShared_6479_; uint8_t v_isSharedCheck_6483_; 
lean_del_object(v___x_6449_);
lean_dec(v_snd_6447_);
lean_dec(v_fst_6446_);
lean_dec(v_splitVCIdx_6437_);
lean_dec(v_fst_6433_);
lean_dec(v_fst_6431_);
lean_dec_ref(v_info_6226_);
lean_dec(v_goal_6225_);
lean_dec_ref(v_scope_6224_);
v_a_6476_ = lean_ctor_get(v___x_6451_, 0);
v_isSharedCheck_6483_ = !lean_is_exclusive(v___x_6451_);
if (v_isSharedCheck_6483_ == 0)
{
v___x_6478_ = v___x_6451_;
v_isShared_6479_ = v_isSharedCheck_6483_;
goto v_resetjp_6477_;
}
else
{
lean_inc(v_a_6476_);
lean_dec(v___x_6451_);
v___x_6478_ = lean_box(0);
v_isShared_6479_ = v_isSharedCheck_6483_;
goto v_resetjp_6477_;
}
v_resetjp_6477_:
{
lean_object* v___x_6481_; 
if (v_isShared_6479_ == 0)
{
v___x_6481_ = v___x_6478_;
goto v_reusejp_6480_;
}
else
{
lean_object* v_reuseFailAlloc_6482_; 
v_reuseFailAlloc_6482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6482_, 0, v_a_6476_);
v___x_6481_ = v_reuseFailAlloc_6482_;
goto v_reusejp_6480_;
}
v_reusejp_6480_:
{
return v___x_6481_;
}
}
}
}
}
else
{
lean_object* v___x_6485_; lean_object* v___x_6487_; 
lean_dec(v_a_6441_);
lean_dec(v_splitVCIdx_6437_);
lean_dec(v_fst_6433_);
lean_dec(v_fst_6431_);
lean_dec_ref(v___y_6412_);
lean_dec_ref(v_info_6226_);
lean_dec(v_goal_6225_);
lean_dec_ref(v_scope_6224_);
v___x_6485_ = lean_box(0);
if (v_isShared_6444_ == 0)
{
lean_ctor_set(v___x_6443_, 0, v___x_6485_);
v___x_6487_ = v___x_6443_;
goto v_reusejp_6486_;
}
else
{
lean_object* v_reuseFailAlloc_6488_; 
v_reuseFailAlloc_6488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6488_, 0, v___x_6485_);
v___x_6487_ = v_reuseFailAlloc_6488_;
goto v_reusejp_6486_;
}
v_reusejp_6486_:
{
return v___x_6487_;
}
}
}
}
else
{
lean_object* v_a_6490_; lean_object* v___x_6492_; uint8_t v_isShared_6493_; uint8_t v_isSharedCheck_6497_; 
lean_dec(v_splitVCIdx_6437_);
lean_dec(v_fst_6433_);
lean_dec(v_fst_6431_);
lean_dec_ref(v___y_6412_);
lean_dec_ref(v_info_6226_);
lean_dec(v_goal_6225_);
lean_dec_ref(v_scope_6224_);
v_a_6490_ = lean_ctor_get(v___x_6440_, 0);
v_isSharedCheck_6497_ = !lean_is_exclusive(v___x_6440_);
if (v_isSharedCheck_6497_ == 0)
{
v___x_6492_ = v___x_6440_;
v_isShared_6493_ = v_isSharedCheck_6497_;
goto v_resetjp_6491_;
}
else
{
lean_inc(v_a_6490_);
lean_dec(v___x_6440_);
v___x_6492_ = lean_box(0);
v_isShared_6493_ = v_isSharedCheck_6497_;
goto v_resetjp_6491_;
}
v_resetjp_6491_:
{
lean_object* v___x_6495_; 
if (v_isShared_6493_ == 0)
{
v___x_6495_ = v___x_6492_;
goto v_reusejp_6494_;
}
else
{
lean_object* v_reuseFailAlloc_6496_; 
v_reuseFailAlloc_6496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6496_, 0, v_a_6490_);
v___x_6495_ = v_reuseFailAlloc_6496_;
goto v_reusejp_6494_;
}
v_reusejp_6494_:
{
return v___x_6495_;
}
}
}
}
else
{
lean_object* v_a_6498_; lean_object* v___x_6500_; uint8_t v_isShared_6501_; uint8_t v_isSharedCheck_6505_; 
lean_dec_ref(v___y_6415_);
lean_dec_ref(v___y_6414_);
lean_dec_ref(v___y_6413_);
lean_dec_ref(v___y_6412_);
lean_dec_ref(v_info_6226_);
lean_dec(v_goal_6225_);
lean_dec_ref(v_scope_6224_);
v_a_6498_ = lean_ctor_get(v___x_6427_, 0);
v_isSharedCheck_6505_ = !lean_is_exclusive(v___x_6427_);
if (v_isSharedCheck_6505_ == 0)
{
v___x_6500_ = v___x_6427_;
v_isShared_6501_ = v_isSharedCheck_6505_;
goto v_resetjp_6499_;
}
else
{
lean_inc(v_a_6498_);
lean_dec(v___x_6427_);
v___x_6500_ = lean_box(0);
v_isShared_6501_ = v_isSharedCheck_6505_;
goto v_resetjp_6499_;
}
v_resetjp_6499_:
{
lean_object* v___x_6503_; 
if (v_isShared_6501_ == 0)
{
v___x_6503_ = v___x_6500_;
goto v_reusejp_6502_;
}
else
{
lean_object* v_reuseFailAlloc_6504_; 
v_reuseFailAlloc_6504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6498_);
v___x_6503_ = v_reuseFailAlloc_6504_;
goto v_reusejp_6502_;
}
v_reusejp_6502_:
{
return v___x_6503_;
}
}
}
}
v___jp_6506_:
{
if (lean_obj_tag(v_a_6507_) == 1)
{
uint8_t v_conjunctivePre_6508_; 
v_conjunctivePre_6508_ = lean_ctor_get_uint8(v_thm_6227_, sizeof(void*)*4);
if (v_conjunctivePre_6508_ == 0)
{
lean_object* v_val_6509_; lean_object* v___x_6511_; uint8_t v_isShared_6512_; uint8_t v_isSharedCheck_6576_; 
v_val_6509_ = lean_ctor_get(v_a_6507_, 0);
v_isSharedCheck_6576_ = !lean_is_exclusive(v_a_6507_);
if (v_isSharedCheck_6576_ == 0)
{
v___x_6511_ = v_a_6507_;
v_isShared_6512_ = v_isSharedCheck_6576_;
goto v_resetjp_6510_;
}
else
{
lean_inc(v_val_6509_);
lean_dec(v_a_6507_);
v___x_6511_ = lean_box(0);
v_isShared_6512_ = v_isSharedCheck_6576_;
goto v_resetjp_6510_;
}
v_resetjp_6510_:
{
lean_object* v___x_6513_; 
lean_inc(v_goal_6225_);
v___x_6513_ = l_Lean_MVarId_getType(v_goal_6225_, v_a_6237_, v_a_6238_, v_a_6239_, v_a_6240_);
if (lean_obj_tag(v___x_6513_) == 0)
{
lean_object* v_a_6514_; lean_object* v_mkOpAppM_6515_; lean_object* v_proc_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___f_6522_; lean_object* v___x_6523_; lean_object* v___x_6524_; 
v_a_6514_ = lean_ctor_get(v___x_6513_, 0);
lean_inc(v_a_6514_);
lean_dec_ref_known(v___x_6513_, 1);
v_mkOpAppM_6515_ = lean_ctor_get(v_fp_6228_, 2);
v_proc_6516_ = lean_ctor_get(v_fp_6228_, 4);
v___x_6517_ = l_Lean_Expr_appFn_x21(v_a_6514_);
v___x_6518_ = l_Lean_Expr_appArg_x21(v___x_6517_);
lean_dec_ref(v___x_6517_);
v___x_6519_ = lean_unsigned_to_nat(2u);
v___x_6520_ = l_Lean_Expr_stripArgsN(v_a_6514_, v___x_6519_);
lean_dec(v_a_6514_);
lean_inc_ref(v_thm_6227_);
v___x_6521_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorem_global_x3f(v_thm_6227_);
lean_inc_ref_n(v_info_6226_, 2);
lean_inc_ref(v_mkOpAppM_6515_);
v___f_6522_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___lam__0___boxed), 9, 2);
lean_closure_set(v___f_6522_, 0, v_mkOpAppM_6515_);
lean_closure_set(v___f_6522_, 1, v_info_6226_);
lean_inc_ref(v___x_6520_);
v___x_6523_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6523_, 0, v___x_6518_);
lean_ctor_set(v___x_6523_, 1, v___x_6520_);
lean_ctor_set(v___x_6523_, 2, v_info_6226_);
lean_ctor_set(v___x_6523_, 3, v_providedFrame_x3f_6229_);
lean_ctor_set(v___x_6523_, 4, v___x_6521_);
lean_ctor_set(v___x_6523_, 5, v___f_6522_);
lean_inc_ref(v_proc_6516_);
lean_inc(v_a_6240_);
lean_inc_ref(v_a_6239_);
lean_inc(v_a_6238_);
lean_inc_ref(v_a_6237_);
lean_inc(v_a_6236_);
lean_inc_ref(v_a_6235_);
lean_inc(v_a_6234_);
lean_inc_ref(v_a_6233_);
lean_inc(v_a_6232_);
v___x_6524_ = lean_apply_11(v_proc_6516_, v___x_6523_, v_a_6232_, v_a_6233_, v_a_6234_, v_a_6235_, v_a_6236_, v_a_6237_, v_a_6238_, v_a_6239_, v_a_6240_, lean_box(0));
if (lean_obj_tag(v___x_6524_) == 0)
{
lean_object* v_a_6525_; 
v_a_6525_ = lean_ctor_get(v___x_6524_, 0);
lean_inc(v_a_6525_);
lean_dec_ref_known(v___x_6524_, 1);
if (lean_obj_tag(v_a_6525_) == 0)
{
lean_dec_ref(v___x_6520_);
lean_del_object(v___x_6511_);
lean_dec_ref(v_fp_6228_);
v___y_6330_ = v_val_6509_;
v___y_6331_ = v_a_6230_;
v___y_6332_ = v_a_6231_;
v___y_6333_ = v_a_6232_;
v___y_6334_ = v_a_6233_;
v___y_6335_ = v_a_6234_;
v___y_6336_ = v_a_6235_;
v___y_6337_ = v_a_6236_;
v___y_6338_ = v_a_6237_;
v___y_6339_ = v_a_6238_;
v___y_6340_ = v_a_6239_;
v___y_6341_ = v_a_6240_;
goto v___jp_6329_;
}
else
{
lean_object* v_excessStates_6526_; lean_object* v_k_6527_; lean_object* v___x_6529_; uint8_t v_isShared_6530_; uint8_t v_isSharedCheck_6559_; 
lean_dec_ref(v_thm_6227_);
v_excessStates_6526_ = lean_ctor_get(v_a_6525_, 0);
v_k_6527_ = lean_ctor_get(v_a_6525_, 1);
v_isSharedCheck_6559_ = !lean_is_exclusive(v_a_6525_);
if (v_isSharedCheck_6559_ == 0)
{
v___x_6529_ = v_a_6525_;
v_isShared_6530_ = v_isSharedCheck_6559_;
goto v_resetjp_6528_;
}
else
{
lean_inc(v_k_6527_);
lean_inc(v_excessStates_6526_);
lean_dec(v_a_6525_);
v___x_6529_ = lean_box(0);
v_isShared_6530_ = v_isSharedCheck_6559_;
goto v_resetjp_6528_;
}
v_resetjp_6528_:
{
lean_object* v_excessArgs_6531_; lean_object* v___x_6532_; lean_object* v___x_6533_; uint8_t v___x_6534_; 
v_excessArgs_6531_ = lean_ctor_get(v_info_6226_, 3);
v___x_6532_ = lean_array_get_size(v_excessStates_6526_);
v___x_6533_ = lean_array_get_size(v_excessArgs_6531_);
v___x_6534_ = lean_nat_dec_eq(v___x_6532_, v___x_6533_);
if (v___x_6534_ == 0)
{
lean_object* v___x_6535_; lean_object* v___x_6536_; lean_object* v___x_6538_; 
lean_dec_ref(v_k_6527_);
lean_dec_ref(v_excessStates_6526_);
lean_dec_ref(v___x_6520_);
lean_dec(v_val_6509_);
lean_dec_ref(v_fp_6228_);
lean_dec_ref(v_info_6226_);
lean_dec(v_goal_6225_);
lean_dec_ref(v_scope_6224_);
v___x_6535_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__11);
v___x_6536_ = l_Nat_reprFast(v___x_6533_);
if (v_isShared_6512_ == 0)
{
lean_ctor_set_tag(v___x_6511_, 3);
lean_ctor_set(v___x_6511_, 0, v___x_6536_);
v___x_6538_ = v___x_6511_;
goto v_reusejp_6537_;
}
else
{
lean_object* v_reuseFailAlloc_6558_; 
v_reuseFailAlloc_6558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6558_, 0, v___x_6536_);
v___x_6538_ = v_reuseFailAlloc_6558_;
goto v_reusejp_6537_;
}
v_reusejp_6537_:
{
lean_object* v___x_6539_; lean_object* v___x_6541_; 
v___x_6539_ = l_Lean_MessageData_ofFormat(v___x_6538_);
if (v_isShared_6530_ == 0)
{
lean_ctor_set_tag(v___x_6529_, 7);
lean_ctor_set(v___x_6529_, 1, v___x_6539_);
lean_ctor_set(v___x_6529_, 0, v___x_6535_);
v___x_6541_ = v___x_6529_;
goto v_reusejp_6540_;
}
else
{
lean_object* v_reuseFailAlloc_6557_; 
v_reuseFailAlloc_6557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6557_, 0, v___x_6535_);
lean_ctor_set(v_reuseFailAlloc_6557_, 1, v___x_6539_);
v___x_6541_ = v_reuseFailAlloc_6557_;
goto v_reusejp_6540_;
}
v_reusejp_6540_:
{
lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v_a_6549_; lean_object* v___x_6551_; uint8_t v_isShared_6552_; uint8_t v_isSharedCheck_6556_; 
v___x_6542_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__13);
v___x_6543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6543_, 0, v___x_6541_);
lean_ctor_set(v___x_6543_, 1, v___x_6542_);
v___x_6544_ = l_Nat_reprFast(v___x_6532_);
v___x_6545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6545_, 0, v___x_6544_);
v___x_6546_ = l_Lean_MessageData_ofFormat(v___x_6545_);
v___x_6547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6547_, 0, v___x_6543_);
lean_ctor_set(v___x_6547_, 1, v___x_6546_);
v___x_6548_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f_spec__1___redArg(v___x_6547_, v_a_6237_, v_a_6238_, v_a_6239_, v_a_6240_);
v_a_6549_ = lean_ctor_get(v___x_6548_, 0);
v_isSharedCheck_6556_ = !lean_is_exclusive(v___x_6548_);
if (v_isSharedCheck_6556_ == 0)
{
v___x_6551_ = v___x_6548_;
v_isShared_6552_ = v_isSharedCheck_6556_;
goto v_resetjp_6550_;
}
else
{
lean_inc(v_a_6549_);
lean_dec(v___x_6548_);
v___x_6551_ = lean_box(0);
v_isShared_6552_ = v_isSharedCheck_6556_;
goto v_resetjp_6550_;
}
v_resetjp_6550_:
{
lean_object* v___x_6554_; 
if (v_isShared_6552_ == 0)
{
v___x_6554_ = v___x_6551_;
goto v_reusejp_6553_;
}
else
{
lean_object* v_reuseFailAlloc_6555_; 
v_reuseFailAlloc_6555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6555_, 0, v_a_6549_);
v___x_6554_ = v_reuseFailAlloc_6555_;
goto v_reusejp_6553_;
}
v_reusejp_6553_:
{
return v___x_6554_;
}
}
}
}
}
else
{
lean_del_object(v___x_6529_);
lean_del_object(v___x_6511_);
v___y_6412_ = v_k_6527_;
v___y_6413_ = v_excessStates_6526_;
v___y_6414_ = v_val_6509_;
v___y_6415_ = v___x_6520_;
v___y_6416_ = v_a_6230_;
v___y_6417_ = v_a_6231_;
v___y_6418_ = v_a_6232_;
v___y_6419_ = v_a_6233_;
v___y_6420_ = v_a_6234_;
v___y_6421_ = v_a_6235_;
v___y_6422_ = v_a_6236_;
v___y_6423_ = v_a_6237_;
v___y_6424_ = v_a_6238_;
v___y_6425_ = v_a_6239_;
v___y_6426_ = v_a_6240_;
goto v___jp_6411_;
}
}
}
}
else
{
lean_object* v_a_6560_; lean_object* v___x_6562_; uint8_t v_isShared_6563_; uint8_t v_isSharedCheck_6567_; 
lean_dec_ref(v___x_6520_);
lean_del_object(v___x_6511_);
lean_dec(v_val_6509_);
lean_dec_ref(v_fp_6228_);
lean_dec_ref(v_thm_6227_);
lean_dec_ref(v_info_6226_);
lean_dec(v_goal_6225_);
lean_dec_ref(v_scope_6224_);
v_a_6560_ = lean_ctor_get(v___x_6524_, 0);
v_isSharedCheck_6567_ = !lean_is_exclusive(v___x_6524_);
if (v_isSharedCheck_6567_ == 0)
{
v___x_6562_ = v___x_6524_;
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
else
{
lean_inc(v_a_6560_);
lean_dec(v___x_6524_);
v___x_6562_ = lean_box(0);
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
v_resetjp_6561_:
{
lean_object* v___x_6565_; 
if (v_isShared_6563_ == 0)
{
v___x_6565_ = v___x_6562_;
goto v_reusejp_6564_;
}
else
{
lean_object* v_reuseFailAlloc_6566_; 
v_reuseFailAlloc_6566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6566_, 0, v_a_6560_);
v___x_6565_ = v_reuseFailAlloc_6566_;
goto v_reusejp_6564_;
}
v_reusejp_6564_:
{
return v___x_6565_;
}
}
}
}
else
{
lean_object* v_a_6568_; lean_object* v___x_6570_; uint8_t v_isShared_6571_; uint8_t v_isSharedCheck_6575_; 
lean_del_object(v___x_6511_);
lean_dec(v_val_6509_);
lean_dec(v_providedFrame_x3f_6229_);
lean_dec_ref(v_fp_6228_);
lean_dec_ref(v_thm_6227_);
lean_dec_ref(v_info_6226_);
lean_dec(v_goal_6225_);
lean_dec_ref(v_scope_6224_);
v_a_6568_ = lean_ctor_get(v___x_6513_, 0);
v_isSharedCheck_6575_ = !lean_is_exclusive(v___x_6513_);
if (v_isSharedCheck_6575_ == 0)
{
v___x_6570_ = v___x_6513_;
v_isShared_6571_ = v_isSharedCheck_6575_;
goto v_resetjp_6569_;
}
else
{
lean_inc(v_a_6568_);
lean_dec(v___x_6513_);
v___x_6570_ = lean_box(0);
v_isShared_6571_ = v_isSharedCheck_6575_;
goto v_resetjp_6569_;
}
v_resetjp_6569_:
{
lean_object* v___x_6573_; 
if (v_isShared_6571_ == 0)
{
v___x_6573_ = v___x_6570_;
goto v_reusejp_6572_;
}
else
{
lean_object* v_reuseFailAlloc_6574_; 
v_reuseFailAlloc_6574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6574_, 0, v_a_6568_);
v___x_6573_ = v_reuseFailAlloc_6574_;
goto v_reusejp_6572_;
}
v_reusejp_6572_:
{
return v___x_6573_;
}
}
}
}
}
else
{
lean_object* v_val_6577_; 
lean_dec(v_providedFrame_x3f_6229_);
lean_dec_ref(v_fp_6228_);
v_val_6577_ = lean_ctor_get(v_a_6507_, 0);
lean_inc(v_val_6577_);
lean_dec_ref_known(v_a_6507_, 1);
v___y_6330_ = v_val_6577_;
v___y_6331_ = v_a_6230_;
v___y_6332_ = v_a_6231_;
v___y_6333_ = v_a_6232_;
v___y_6334_ = v_a_6233_;
v___y_6335_ = v_a_6234_;
v___y_6336_ = v_a_6235_;
v___y_6337_ = v_a_6236_;
v___y_6338_ = v_a_6237_;
v___y_6339_ = v_a_6238_;
v___y_6340_ = v_a_6239_;
v___y_6341_ = v_a_6240_;
goto v___jp_6329_;
}
}
else
{
lean_object* v___x_6578_; lean_object* v___x_6579_; 
lean_dec(v_a_6507_);
lean_dec(v_providedFrame_x3f_6229_);
lean_dec_ref(v_fp_6228_);
lean_dec_ref(v_thm_6227_);
lean_dec_ref(v_info_6226_);
lean_dec(v_goal_6225_);
lean_dec_ref(v_scope_6224_);
v___x_6578_ = lean_box(0);
v___x_6579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6579_, 0, v___x_6578_);
return v___x_6579_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___boxed(lean_object** _args){
lean_object* v_scope_6663_ = _args[0];
lean_object* v_goal_6664_ = _args[1];
lean_object* v_info_6665_ = _args[2];
lean_object* v_thm_6666_ = _args[3];
lean_object* v_fp_6667_ = _args[4];
lean_object* v_providedFrame_x3f_6668_ = _args[5];
lean_object* v_a_6669_ = _args[6];
lean_object* v_a_6670_ = _args[7];
lean_object* v_a_6671_ = _args[8];
lean_object* v_a_6672_ = _args[9];
lean_object* v_a_6673_ = _args[10];
lean_object* v_a_6674_ = _args[11];
lean_object* v_a_6675_ = _args[12];
lean_object* v_a_6676_ = _args[13];
lean_object* v_a_6677_ = _args[14];
lean_object* v_a_6678_ = _args[15];
lean_object* v_a_6679_ = _args[16];
lean_object* v_a_6680_ = _args[17];
_start:
{
lean_object* v_res_6681_; 
v_res_6681_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(v_scope_6663_, v_goal_6664_, v_info_6665_, v_thm_6666_, v_fp_6667_, v_providedFrame_x3f_6668_, v_a_6669_, v_a_6670_, v_a_6671_, v_a_6672_, v_a_6673_, v_a_6674_, v_a_6675_, v_a_6676_, v_a_6677_, v_a_6678_, v_a_6679_);
lean_dec(v_a_6679_);
lean_dec_ref(v_a_6678_);
lean_dec(v_a_6677_);
lean_dec_ref(v_a_6676_);
lean_dec(v_a_6675_);
lean_dec_ref(v_a_6674_);
lean_dec(v_a_6673_);
lean_dec_ref(v_a_6672_);
lean_dec(v_a_6671_);
lean_dec(v_a_6670_);
lean_dec_ref(v_a_6669_);
return v_res_6681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1___redArg(lean_object* v_a_6682_, lean_object* v_x_6683_){
_start:
{
if (lean_obj_tag(v_x_6683_) == 0)
{
lean_object* v___x_6684_; 
v___x_6684_ = lean_box(0);
return v___x_6684_;
}
else
{
lean_object* v_key_6685_; lean_object* v_value_6686_; lean_object* v_tail_6687_; uint8_t v___x_6688_; 
v_key_6685_ = lean_ctor_get(v_x_6683_, 0);
v_value_6686_ = lean_ctor_get(v_x_6683_, 1);
v_tail_6687_ = lean_ctor_get(v_x_6683_, 2);
v___x_6688_ = lean_name_eq(v_key_6685_, v_a_6682_);
if (v___x_6688_ == 0)
{
v_x_6683_ = v_tail_6687_;
goto _start;
}
else
{
lean_object* v___x_6690_; 
lean_inc(v_value_6686_);
v___x_6690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6690_, 0, v_value_6686_);
return v___x_6690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1___redArg___boxed(lean_object* v_a_6691_, lean_object* v_x_6692_){
_start:
{
lean_object* v_res_6693_; 
v_res_6693_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1___redArg(v_a_6691_, v_x_6692_);
lean_dec(v_x_6692_);
lean_dec(v_a_6691_);
return v_res_6693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1___redArg(lean_object* v_m_6694_, lean_object* v_a_6695_){
_start:
{
lean_object* v_buckets_6696_; lean_object* v___x_6697_; uint64_t v___y_6699_; 
v_buckets_6696_ = lean_ctor_get(v_m_6694_, 1);
v___x_6697_ = lean_array_get_size(v_buckets_6696_);
if (lean_obj_tag(v_a_6695_) == 0)
{
uint64_t v___x_6713_; 
v___x_6713_ = 1723ULL;
v___y_6699_ = v___x_6713_;
goto v___jp_6698_;
}
else
{
uint64_t v_hash_6714_; 
v_hash_6714_ = lean_ctor_get_uint64(v_a_6695_, sizeof(void*)*2);
v___y_6699_ = v_hash_6714_;
goto v___jp_6698_;
}
v___jp_6698_:
{
uint64_t v___x_6700_; uint64_t v___x_6701_; uint64_t v_fold_6702_; uint64_t v___x_6703_; uint64_t v___x_6704_; uint64_t v___x_6705_; size_t v___x_6706_; size_t v___x_6707_; size_t v___x_6708_; size_t v___x_6709_; size_t v___x_6710_; lean_object* v___x_6711_; lean_object* v___x_6712_; 
v___x_6700_ = 32ULL;
v___x_6701_ = lean_uint64_shift_right(v___y_6699_, v___x_6700_);
v_fold_6702_ = lean_uint64_xor(v___y_6699_, v___x_6701_);
v___x_6703_ = 16ULL;
v___x_6704_ = lean_uint64_shift_right(v_fold_6702_, v___x_6703_);
v___x_6705_ = lean_uint64_xor(v_fold_6702_, v___x_6704_);
v___x_6706_ = lean_uint64_to_usize(v___x_6705_);
v___x_6707_ = lean_usize_of_nat(v___x_6697_);
v___x_6708_ = ((size_t)1ULL);
v___x_6709_ = lean_usize_sub(v___x_6707_, v___x_6708_);
v___x_6710_ = lean_usize_land(v___x_6706_, v___x_6709_);
v___x_6711_ = lean_array_uget_borrowed(v_buckets_6696_, v___x_6710_);
v___x_6712_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1___redArg(v_a_6695_, v___x_6711_);
return v___x_6712_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1___redArg___boxed(lean_object* v_m_6715_, lean_object* v_a_6716_){
_start:
{
lean_object* v_res_6717_; 
v_res_6717_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1___redArg(v_m_6715_, v_a_6716_);
lean_dec(v_a_6716_);
lean_dec_ref(v_m_6715_);
return v_res_6717_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_6722_; lean_object* v___x_6723_; 
v___x_6722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__1));
v___x_6723_ = l_Lean_stringToMessageData(v___x_6722_);
return v___x_6723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(lean_object* v_scope_6724_, lean_object* v_goal_6725_, lean_object* v_info_6726_, lean_object* v___y_6727_, lean_object* v_providedFrame_x3f_6728_, lean_object* v___x_6729_, lean_object* v_as_6730_, size_t v_sz_6731_, size_t v_i_6732_, lean_object* v_b_6733_, lean_object* v___y_6734_, lean_object* v___y_6735_, lean_object* v___y_6736_, lean_object* v___y_6737_, lean_object* v___y_6738_, lean_object* v___y_6739_, lean_object* v___y_6740_, lean_object* v___y_6741_, lean_object* v___y_6742_, lean_object* v___y_6743_, lean_object* v___y_6744_){
_start:
{
lean_object* v_a_6747_; uint8_t v___x_6751_; 
v___x_6751_ = lean_usize_dec_lt(v_i_6732_, v_sz_6731_);
if (v___x_6751_ == 0)
{
lean_object* v___x_6752_; 
lean_dec_ref(v___x_6729_);
lean_dec(v_providedFrame_x3f_6728_);
lean_dec_ref(v___y_6727_);
lean_dec_ref(v_info_6726_);
lean_dec(v_goal_6725_);
lean_dec_ref(v_scope_6724_);
v___x_6752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6752_, 0, v_b_6733_);
return v___x_6752_;
}
else
{
lean_object* v___x_6753_; lean_object* v___x_6754_; lean_object* v_a_6755_; lean_object* v___x_6756_; 
lean_dec_ref(v_b_6733_);
v___x_6753_ = lean_box(0);
v___x_6754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0));
v_a_6755_ = lean_array_uget_borrowed(v_as_6730_, v_i_6732_);
lean_inc(v_providedFrame_x3f_6728_);
lean_inc_ref(v___y_6727_);
lean_inc(v_a_6755_);
lean_inc_ref(v_info_6726_);
lean_inc(v_goal_6725_);
lean_inc_ref(v_scope_6724_);
v___x_6756_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec(v_scope_6724_, v_goal_6725_, v_info_6726_, v_a_6755_, v___y_6727_, v_providedFrame_x3f_6728_, v___y_6734_, v___y_6735_, v___y_6736_, v___y_6737_, v___y_6738_, v___y_6739_, v___y_6740_, v___y_6741_, v___y_6742_, v___y_6743_, v___y_6744_);
if (lean_obj_tag(v___x_6756_) == 0)
{
lean_object* v_a_6757_; lean_object* v___x_6759_; uint8_t v_isShared_6760_; uint8_t v_isSharedCheck_6808_; 
v_a_6757_ = lean_ctor_get(v___x_6756_, 0);
v_isSharedCheck_6808_ = !lean_is_exclusive(v___x_6756_);
if (v_isSharedCheck_6808_ == 0)
{
v___x_6759_ = v___x_6756_;
v_isShared_6760_ = v_isSharedCheck_6808_;
goto v_resetjp_6758_;
}
else
{
lean_inc(v_a_6757_);
lean_dec(v___x_6756_);
v___x_6759_ = lean_box(0);
v_isShared_6760_ = v_isSharedCheck_6808_;
goto v_resetjp_6758_;
}
v_resetjp_6758_:
{
if (lean_obj_tag(v_a_6757_) == 1)
{
lean_object* v___x_6761_; lean_object* v___x_6763_; 
lean_dec_ref(v___x_6729_);
lean_dec(v_providedFrame_x3f_6728_);
lean_dec_ref(v___y_6727_);
lean_dec_ref(v_info_6726_);
lean_dec(v_goal_6725_);
lean_dec_ref(v_scope_6724_);
v___x_6761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6761_, 0, v_a_6757_);
lean_ctor_set(v___x_6761_, 1, v___x_6753_);
if (v_isShared_6760_ == 0)
{
lean_ctor_set(v___x_6759_, 0, v___x_6761_);
v___x_6763_ = v___x_6759_;
goto v_reusejp_6762_;
}
else
{
lean_object* v_reuseFailAlloc_6764_; 
v_reuseFailAlloc_6764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6764_, 0, v___x_6761_);
v___x_6763_ = v_reuseFailAlloc_6764_;
goto v_reusejp_6762_;
}
v_reusejp_6762_:
{
return v___x_6763_;
}
}
else
{
lean_object* v_toCold_6765_; lean_object* v_options_6766_; uint8_t v_hasTrace_6767_; 
lean_del_object(v___x_6759_);
lean_dec(v_a_6757_);
v_toCold_6765_ = lean_ctor_get(v___y_6743_, 0);
v_options_6766_ = lean_ctor_get(v_toCold_6765_, 2);
v_hasTrace_6767_ = lean_ctor_get_uint8(v_options_6766_, sizeof(void*)*1);
if (v_hasTrace_6767_ == 0)
{
v_a_6747_ = v___x_6754_;
goto v___jp_6746_;
}
else
{
lean_object* v_inheritedTraceOptions_6768_; lean_object* v___x_6769_; lean_object* v___x_6770_; uint8_t v___x_6771_; 
v_inheritedTraceOptions_6768_ = lean_ctor_get(v_toCold_6765_, 11);
v___x_6769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
v___x_6770_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_6771_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6768_, v_options_6766_, v___x_6770_);
if (v___x_6771_ == 0)
{
v_a_6747_ = v___x_6754_;
goto v___jp_6746_;
}
else
{
lean_object* v_proof_6772_; lean_object* v___x_6773_; lean_object* v___y_6775_; 
v_proof_6772_ = lean_ctor_get(v_a_6755_, 1);
v___x_6773_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__2);
switch(lean_obj_tag(v_proof_6772_))
{
case 0:
{
lean_object* v_declName_6790_; lean_object* v___x_6791_; lean_object* v___x_6792_; lean_object* v___x_6793_; 
v_declName_6790_ = lean_ctor_get(v_proof_6772_, 0);
v___x_6791_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_6790_);
v___x_6792_ = l_Lean_MessageData_ofName(v_declName_6790_);
v___x_6793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6793_, 0, v___x_6791_);
lean_ctor_set(v___x_6793_, 1, v___x_6792_);
v___y_6775_ = v___x_6793_;
goto v___jp_6774_;
}
case 1:
{
lean_object* v_fvarId_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; lean_object* v___x_6797_; lean_object* v___x_6798_; 
v_fvarId_6794_ = lean_ctor_get(v_proof_6772_, 0);
v___x_6795_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_6794_);
v___x_6796_ = l_Lean_mkFVar(v_fvarId_6794_);
v___x_6797_ = l_Lean_MessageData_ofExpr(v___x_6796_);
v___x_6798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6798_, 0, v___x_6795_);
lean_ctor_set(v___x_6798_, 1, v___x_6797_);
v___y_6775_ = v___x_6798_;
goto v___jp_6774_;
}
default: 
{
lean_object* v_ref_6799_; lean_object* v_proof_6800_; lean_object* v___x_6801_; lean_object* v___x_6802_; lean_object* v___x_6803_; lean_object* v___x_6804_; lean_object* v___x_6805_; lean_object* v___x_6806_; lean_object* v___x_6807_; 
v_ref_6799_ = lean_ctor_get(v_proof_6772_, 1);
v_proof_6800_ = lean_ctor_get(v_proof_6772_, 2);
v___x_6801_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_6799_);
v___x_6802_ = l_Lean_MessageData_ofSyntax(v_ref_6799_);
v___x_6803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6803_, 0, v___x_6801_);
lean_ctor_set(v___x_6803_, 1, v___x_6802_);
v___x_6804_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_6805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6805_, 0, v___x_6803_);
lean_ctor_set(v___x_6805_, 1, v___x_6804_);
lean_inc_ref(v_proof_6800_);
v___x_6806_ = l_Lean_MessageData_ofExpr(v_proof_6800_);
v___x_6807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6807_, 0, v___x_6805_);
lean_ctor_set(v___x_6807_, 1, v___x_6806_);
v___y_6775_ = v___x_6807_;
goto v___jp_6774_;
}
}
v___jp_6774_:
{
lean_object* v___x_6776_; lean_object* v___x_6777_; lean_object* v___x_6778_; lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; 
v___x_6776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6776_, 0, v___x_6773_);
lean_ctor_set(v___x_6776_, 1, v___y_6775_);
v___x_6777_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpec___closed__3);
v___x_6778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6778_, 0, v___x_6776_);
lean_ctor_set(v___x_6778_, 1, v___x_6777_);
lean_inc_ref(v___x_6729_);
v___x_6779_ = l_Lean_MessageData_ofExpr(v___x_6729_);
v___x_6780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6780_, 0, v___x_6778_);
lean_ctor_set(v___x_6780_, 1, v___x_6779_);
v___x_6781_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_6769_, v___x_6780_, v___y_6741_, v___y_6742_, v___y_6743_, v___y_6744_);
if (lean_obj_tag(v___x_6781_) == 0)
{
lean_dec_ref_known(v___x_6781_, 1);
v_a_6747_ = v___x_6754_;
goto v___jp_6746_;
}
else
{
lean_object* v_a_6782_; lean_object* v___x_6784_; uint8_t v_isShared_6785_; uint8_t v_isSharedCheck_6789_; 
lean_dec_ref(v___x_6729_);
lean_dec(v_providedFrame_x3f_6728_);
lean_dec_ref(v___y_6727_);
lean_dec_ref(v_info_6726_);
lean_dec(v_goal_6725_);
lean_dec_ref(v_scope_6724_);
v_a_6782_ = lean_ctor_get(v___x_6781_, 0);
v_isSharedCheck_6789_ = !lean_is_exclusive(v___x_6781_);
if (v_isSharedCheck_6789_ == 0)
{
v___x_6784_ = v___x_6781_;
v_isShared_6785_ = v_isSharedCheck_6789_;
goto v_resetjp_6783_;
}
else
{
lean_inc(v_a_6782_);
lean_dec(v___x_6781_);
v___x_6784_ = lean_box(0);
v_isShared_6785_ = v_isSharedCheck_6789_;
goto v_resetjp_6783_;
}
v_resetjp_6783_:
{
lean_object* v___x_6787_; 
if (v_isShared_6785_ == 0)
{
v___x_6787_ = v___x_6784_;
goto v_reusejp_6786_;
}
else
{
lean_object* v_reuseFailAlloc_6788_; 
v_reuseFailAlloc_6788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6788_, 0, v_a_6782_);
v___x_6787_ = v_reuseFailAlloc_6788_;
goto v_reusejp_6786_;
}
v_reusejp_6786_:
{
return v___x_6787_;
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
lean_object* v_a_6809_; lean_object* v___x_6811_; uint8_t v_isShared_6812_; uint8_t v_isSharedCheck_6816_; 
lean_dec_ref(v___x_6729_);
lean_dec(v_providedFrame_x3f_6728_);
lean_dec_ref(v___y_6727_);
lean_dec_ref(v_info_6726_);
lean_dec(v_goal_6725_);
lean_dec_ref(v_scope_6724_);
v_a_6809_ = lean_ctor_get(v___x_6756_, 0);
v_isSharedCheck_6816_ = !lean_is_exclusive(v___x_6756_);
if (v_isSharedCheck_6816_ == 0)
{
v___x_6811_ = v___x_6756_;
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
else
{
lean_inc(v_a_6809_);
lean_dec(v___x_6756_);
v___x_6811_ = lean_box(0);
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
v_resetjp_6810_:
{
lean_object* v___x_6814_; 
if (v_isShared_6812_ == 0)
{
v___x_6814_ = v___x_6811_;
goto v_reusejp_6813_;
}
else
{
lean_object* v_reuseFailAlloc_6815_; 
v_reuseFailAlloc_6815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6815_, 0, v_a_6809_);
v___x_6814_ = v_reuseFailAlloc_6815_;
goto v_reusejp_6813_;
}
v_reusejp_6813_:
{
return v___x_6814_;
}
}
}
}
v___jp_6746_:
{
size_t v___x_6748_; size_t v___x_6749_; 
v___x_6748_ = ((size_t)1ULL);
v___x_6749_ = lean_usize_add(v_i_6732_, v___x_6748_);
lean_inc_ref(v_a_6747_);
v_i_6732_ = v___x_6749_;
v_b_6733_ = v_a_6747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___boxed(lean_object** _args){
lean_object* v_scope_6817_ = _args[0];
lean_object* v_goal_6818_ = _args[1];
lean_object* v_info_6819_ = _args[2];
lean_object* v___y_6820_ = _args[3];
lean_object* v_providedFrame_x3f_6821_ = _args[4];
lean_object* v___x_6822_ = _args[5];
lean_object* v_as_6823_ = _args[6];
lean_object* v_sz_6824_ = _args[7];
lean_object* v_i_6825_ = _args[8];
lean_object* v_b_6826_ = _args[9];
lean_object* v___y_6827_ = _args[10];
lean_object* v___y_6828_ = _args[11];
lean_object* v___y_6829_ = _args[12];
lean_object* v___y_6830_ = _args[13];
lean_object* v___y_6831_ = _args[14];
lean_object* v___y_6832_ = _args[15];
lean_object* v___y_6833_ = _args[16];
lean_object* v___y_6834_ = _args[17];
lean_object* v___y_6835_ = _args[18];
lean_object* v___y_6836_ = _args[19];
lean_object* v___y_6837_ = _args[20];
lean_object* v___y_6838_ = _args[21];
_start:
{
size_t v_sz_boxed_6839_; size_t v_i_boxed_6840_; lean_object* v_res_6841_; 
v_sz_boxed_6839_ = lean_unbox_usize(v_sz_6824_);
lean_dec(v_sz_6824_);
v_i_boxed_6840_ = lean_unbox_usize(v_i_6825_);
lean_dec(v_i_6825_);
v_res_6841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(v_scope_6817_, v_goal_6818_, v_info_6819_, v___y_6820_, v_providedFrame_x3f_6821_, v___x_6822_, v_as_6823_, v_sz_boxed_6839_, v_i_boxed_6840_, v_b_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_, v___y_6833_, v___y_6834_, v___y_6835_, v___y_6836_, v___y_6837_);
lean_dec(v___y_6837_);
lean_dec_ref(v___y_6836_);
lean_dec(v___y_6835_);
lean_dec_ref(v___y_6834_);
lean_dec(v___y_6833_);
lean_dec_ref(v___y_6832_);
lean_dec(v___y_6831_);
lean_dec_ref(v___y_6830_);
lean_dec(v___y_6829_);
lean_dec(v___y_6828_);
lean_dec_ref(v___y_6827_);
lean_dec_ref(v_as_6823_);
return v_res_6841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0(lean_object* v_specs_6842_, lean_object* v___x_6843_, lean_object* v_info_6844_, lean_object* v_scope_6845_, lean_object* v_goal_6846_, lean_object* v___y_6847_, lean_object* v___y_6848_, lean_object* v___y_6849_, lean_object* v___y_6850_, lean_object* v___y_6851_, lean_object* v___y_6852_, lean_object* v___y_6853_, lean_object* v___y_6854_, lean_object* v___y_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_){
_start:
{
lean_object* v___x_6859_; 
lean_inc_ref(v___x_6843_);
v___x_6859_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_findSpecs(v_specs_6842_, v___x_6843_, v___y_6852_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_);
if (lean_obj_tag(v___x_6859_) == 0)
{
lean_object* v_a_6860_; lean_object* v___x_6861_; lean_object* v___y_6863_; lean_object* v_providedFrame_x3f_6864_; lean_object* v___y_6865_; lean_object* v___y_6866_; lean_object* v___y_6867_; lean_object* v___y_6868_; lean_object* v___y_6869_; lean_object* v___y_6870_; lean_object* v___y_6871_; lean_object* v___y_6872_; lean_object* v___y_6873_; lean_object* v___y_6874_; lean_object* v___y_6875_; lean_object* v___y_6900_; lean_object* v___x_6917_; lean_object* v___x_6918_; 
v_a_6860_ = lean_ctor_get(v___x_6859_, 0);
lean_inc(v_a_6860_);
lean_dec_ref_known(v___x_6859_, 1);
v___x_6861_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v_info_6844_);
v___x_6917_ = l_Lean_Expr_getAppFn(v___x_6861_);
v___x_6918_ = l_Lean_Expr_constName_x3f(v___x_6917_);
lean_dec_ref(v___x_6917_);
if (lean_obj_tag(v___x_6918_) == 0)
{
goto v___jp_6915_;
}
else
{
lean_object* v_val_6919_; lean_object* v_frameProcs_6920_; lean_object* v___x_6921_; 
v_val_6919_ = lean_ctor_get(v___x_6918_, 0);
lean_inc(v_val_6919_);
lean_dec_ref_known(v___x_6918_, 1);
v_frameProcs_6920_ = lean_ctor_get(v___y_6847_, 1);
v___x_6921_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1___redArg(v_frameProcs_6920_, v_val_6919_);
lean_dec(v_val_6919_);
if (lean_obj_tag(v___x_6921_) == 0)
{
goto v___jp_6915_;
}
else
{
lean_object* v_val_6922_; 
v_val_6922_ = lean_ctor_get(v___x_6921_, 0);
lean_inc(v_val_6922_);
lean_dec_ref_known(v___x_6921_, 1);
v___y_6900_ = v_val_6922_;
goto v___jp_6899_;
}
}
v___jp_6862_:
{
lean_object* v___x_6876_; size_t v_sz_6877_; size_t v___x_6878_; lean_object* v___x_6879_; 
v___x_6876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0___closed__0));
v_sz_6877_ = lean_array_size(v_a_6860_);
v___x_6878_ = ((size_t)0ULL);
lean_inc_ref(v___x_6843_);
v___x_6879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__0(v_scope_6845_, v_goal_6846_, v_info_6844_, v___y_6863_, v_providedFrame_x3f_6864_, v___x_6843_, v_a_6860_, v_sz_6877_, v___x_6878_, v___x_6876_, v___y_6865_, v___y_6866_, v___y_6867_, v___y_6868_, v___y_6869_, v___y_6870_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_);
if (lean_obj_tag(v___x_6879_) == 0)
{
lean_object* v_a_6880_; lean_object* v___x_6882_; uint8_t v_isShared_6883_; uint8_t v_isSharedCheck_6890_; 
v_a_6880_ = lean_ctor_get(v___x_6879_, 0);
v_isSharedCheck_6890_ = !lean_is_exclusive(v___x_6879_);
if (v_isSharedCheck_6890_ == 0)
{
v___x_6882_ = v___x_6879_;
v_isShared_6883_ = v_isSharedCheck_6890_;
goto v_resetjp_6881_;
}
else
{
lean_inc(v_a_6880_);
lean_dec(v___x_6879_);
v___x_6882_ = lean_box(0);
v_isShared_6883_ = v_isSharedCheck_6890_;
goto v_resetjp_6881_;
}
v_resetjp_6881_:
{
lean_object* v_fst_6884_; 
v_fst_6884_ = lean_ctor_get(v_a_6880_, 0);
lean_inc(v_fst_6884_);
lean_dec(v_a_6880_);
if (lean_obj_tag(v_fst_6884_) == 0)
{
lean_object* v___x_6885_; 
lean_del_object(v___x_6882_);
v___x_6885_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_6843_, v___x_6861_, v_a_6860_, v___y_6865_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_);
return v___x_6885_;
}
else
{
lean_object* v_val_6886_; lean_object* v___x_6888_; 
lean_dec_ref(v___x_6861_);
lean_dec(v_a_6860_);
lean_dec_ref(v___x_6843_);
v_val_6886_ = lean_ctor_get(v_fst_6884_, 0);
lean_inc(v_val_6886_);
lean_dec_ref_known(v_fst_6884_, 1);
if (v_isShared_6883_ == 0)
{
lean_ctor_set(v___x_6882_, 0, v_val_6886_);
v___x_6888_ = v___x_6882_;
goto v_reusejp_6887_;
}
else
{
lean_object* v_reuseFailAlloc_6889_; 
v_reuseFailAlloc_6889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6889_, 0, v_val_6886_);
v___x_6888_ = v_reuseFailAlloc_6889_;
goto v_reusejp_6887_;
}
v_reusejp_6887_:
{
return v___x_6888_;
}
}
}
}
else
{
lean_object* v_a_6891_; lean_object* v___x_6893_; uint8_t v_isShared_6894_; uint8_t v_isSharedCheck_6898_; 
lean_dec_ref(v___x_6861_);
lean_dec(v_a_6860_);
lean_dec_ref(v___x_6843_);
v_a_6891_ = lean_ctor_get(v___x_6879_, 0);
v_isSharedCheck_6898_ = !lean_is_exclusive(v___x_6879_);
if (v_isSharedCheck_6898_ == 0)
{
v___x_6893_ = v___x_6879_;
v_isShared_6894_ = v_isSharedCheck_6898_;
goto v_resetjp_6892_;
}
else
{
lean_inc(v_a_6891_);
lean_dec(v___x_6879_);
v___x_6893_ = lean_box(0);
v_isShared_6894_ = v_isSharedCheck_6898_;
goto v_resetjp_6892_;
}
v_resetjp_6892_:
{
lean_object* v___x_6896_; 
if (v_isShared_6894_ == 0)
{
v___x_6896_ = v___x_6893_;
goto v_reusejp_6895_;
}
else
{
lean_object* v_reuseFailAlloc_6897_; 
v_reuseFailAlloc_6897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6897_, 0, v_a_6891_);
v___x_6896_ = v_reuseFailAlloc_6897_;
goto v_reusejp_6895_;
}
v_reusejp_6895_:
{
return v___x_6896_;
}
}
}
}
v___jp_6899_:
{
lean_object* v___x_6901_; lean_object* v___x_6902_; uint8_t v___x_6903_; 
v___x_6901_ = lean_array_get_size(v_a_6860_);
v___x_6902_ = lean_unsigned_to_nat(0u);
v___x_6903_ = lean_nat_dec_eq(v___x_6901_, v___x_6902_);
if (v___x_6903_ == 0)
{
lean_object* v___x_6904_; 
lean_inc_ref(v_info_6844_);
lean_inc_ref(v___y_6900_);
v___x_6904_ = l_Lean_Elab_Tactic_VCGen_matchFrame_x3f(v___y_6900_, v_info_6844_, v___y_6847_, v___y_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_);
if (lean_obj_tag(v___x_6904_) == 0)
{
lean_object* v_a_6905_; 
v_a_6905_ = lean_ctor_get(v___x_6904_, 0);
lean_inc(v_a_6905_);
lean_dec_ref_known(v___x_6904_, 1);
v___y_6863_ = v___y_6900_;
v_providedFrame_x3f_6864_ = v_a_6905_;
v___y_6865_ = v___y_6847_;
v___y_6866_ = v___y_6848_;
v___y_6867_ = v___y_6849_;
v___y_6868_ = v___y_6850_;
v___y_6869_ = v___y_6851_;
v___y_6870_ = v___y_6852_;
v___y_6871_ = v___y_6853_;
v___y_6872_ = v___y_6854_;
v___y_6873_ = v___y_6855_;
v___y_6874_ = v___y_6856_;
v___y_6875_ = v___y_6857_;
goto v___jp_6862_;
}
else
{
lean_object* v_a_6906_; lean_object* v___x_6908_; uint8_t v_isShared_6909_; uint8_t v_isSharedCheck_6913_; 
lean_dec_ref(v___y_6900_);
lean_dec_ref(v___x_6861_);
lean_dec(v_a_6860_);
lean_dec(v_goal_6846_);
lean_dec_ref(v_scope_6845_);
lean_dec_ref(v_info_6844_);
lean_dec_ref(v___x_6843_);
v_a_6906_ = lean_ctor_get(v___x_6904_, 0);
v_isSharedCheck_6913_ = !lean_is_exclusive(v___x_6904_);
if (v_isSharedCheck_6913_ == 0)
{
v___x_6908_ = v___x_6904_;
v_isShared_6909_ = v_isSharedCheck_6913_;
goto v_resetjp_6907_;
}
else
{
lean_inc(v_a_6906_);
lean_dec(v___x_6904_);
v___x_6908_ = lean_box(0);
v_isShared_6909_ = v_isSharedCheck_6913_;
goto v_resetjp_6907_;
}
v_resetjp_6907_:
{
lean_object* v___x_6911_; 
if (v_isShared_6909_ == 0)
{
v___x_6911_ = v___x_6908_;
goto v_reusejp_6910_;
}
else
{
lean_object* v_reuseFailAlloc_6912_; 
v_reuseFailAlloc_6912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6912_, 0, v_a_6906_);
v___x_6911_ = v_reuseFailAlloc_6912_;
goto v_reusejp_6910_;
}
v_reusejp_6910_:
{
return v___x_6911_;
}
}
}
}
else
{
lean_object* v___x_6914_; 
v___x_6914_ = lean_box(0);
v___y_6863_ = v___y_6900_;
v_providedFrame_x3f_6864_ = v___x_6914_;
v___y_6865_ = v___y_6847_;
v___y_6866_ = v___y_6848_;
v___y_6867_ = v___y_6849_;
v___y_6868_ = v___y_6850_;
v___y_6869_ = v___y_6851_;
v___y_6870_ = v___y_6852_;
v___y_6871_ = v___y_6853_;
v___y_6872_ = v___y_6854_;
v___y_6873_ = v___y_6855_;
v___y_6874_ = v___y_6856_;
v___y_6875_ = v___y_6857_;
goto v___jp_6862_;
}
}
v___jp_6915_:
{
lean_object* v___x_6916_; 
v___x_6916_ = l_Lean_Elab_Tactic_VCGen_meetFrameProc;
v___y_6900_ = v___x_6916_;
goto v___jp_6899_;
}
}
else
{
lean_object* v_a_6923_; lean_object* v___x_6925_; uint8_t v_isShared_6926_; uint8_t v_isSharedCheck_6930_; 
lean_dec(v_goal_6846_);
lean_dec_ref(v_scope_6845_);
lean_dec_ref(v_info_6844_);
lean_dec_ref(v___x_6843_);
v_a_6923_ = lean_ctor_get(v___x_6859_, 0);
v_isSharedCheck_6930_ = !lean_is_exclusive(v___x_6859_);
if (v_isSharedCheck_6930_ == 0)
{
v___x_6925_ = v___x_6859_;
v_isShared_6926_ = v_isSharedCheck_6930_;
goto v_resetjp_6924_;
}
else
{
lean_inc(v_a_6923_);
lean_dec(v___x_6859_);
v___x_6925_ = lean_box(0);
v_isShared_6926_ = v_isSharedCheck_6930_;
goto v_resetjp_6924_;
}
v_resetjp_6924_:
{
lean_object* v___x_6928_; 
if (v_isShared_6926_ == 0)
{
v___x_6928_ = v___x_6925_;
goto v_reusejp_6927_;
}
else
{
lean_object* v_reuseFailAlloc_6929_; 
v_reuseFailAlloc_6929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6929_, 0, v_a_6923_);
v___x_6928_ = v_reuseFailAlloc_6929_;
goto v_reusejp_6927_;
}
v_reusejp_6927_:
{
return v___x_6928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0___boxed(lean_object** _args){
lean_object* v_specs_6931_ = _args[0];
lean_object* v___x_6932_ = _args[1];
lean_object* v_info_6933_ = _args[2];
lean_object* v_scope_6934_ = _args[3];
lean_object* v_goal_6935_ = _args[4];
lean_object* v___y_6936_ = _args[5];
lean_object* v___y_6937_ = _args[6];
lean_object* v___y_6938_ = _args[7];
lean_object* v___y_6939_ = _args[8];
lean_object* v___y_6940_ = _args[9];
lean_object* v___y_6941_ = _args[10];
lean_object* v___y_6942_ = _args[11];
lean_object* v___y_6943_ = _args[12];
lean_object* v___y_6944_ = _args[13];
lean_object* v___y_6945_ = _args[14];
lean_object* v___y_6946_ = _args[15];
lean_object* v___y_6947_ = _args[16];
_start:
{
lean_object* v_res_6948_; 
v_res_6948_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0(v_specs_6931_, v___x_6932_, v_info_6933_, v_scope_6934_, v_goal_6935_, v___y_6936_, v___y_6937_, v___y_6938_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_);
lean_dec(v___y_6946_);
lean_dec_ref(v___y_6945_);
lean_dec(v___y_6944_);
lean_dec_ref(v___y_6943_);
lean_dec(v___y_6942_);
lean_dec_ref(v___y_6941_);
lean_dec(v___y_6940_);
lean_dec_ref(v___y_6939_);
lean_dec(v___y_6938_);
lean_dec(v___y_6937_);
lean_dec_ref(v___y_6936_);
lean_dec_ref(v_specs_6931_);
return v_res_6948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(lean_object* v_scope_6949_, lean_object* v_goal_6950_, lean_object* v_info_6951_, lean_object* v_a_6952_, lean_object* v_a_6953_, lean_object* v_a_6954_, lean_object* v_a_6955_, lean_object* v_a_6956_, lean_object* v_a_6957_, lean_object* v_a_6958_, lean_object* v_a_6959_, lean_object* v_a_6960_, lean_object* v_a_6961_, lean_object* v_a_6962_){
_start:
{
lean_object* v_specs_6964_; lean_object* v___x_6965_; lean_object* v___f_6966_; lean_object* v___x_6967_; 
v_specs_6964_ = lean_ctor_get(v_scope_6949_, 0);
lean_inc_ref(v_specs_6964_);
v___x_6965_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_info_6951_);
lean_inc(v_goal_6950_);
v___f_6966_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___lam__0___boxed), 17, 5);
lean_closure_set(v___f_6966_, 0, v_specs_6964_);
lean_closure_set(v___f_6966_, 1, v___x_6965_);
lean_closure_set(v___f_6966_, 2, v_info_6951_);
lean_closure_set(v___f_6966_, 3, v_scope_6949_);
lean_closure_set(v___f_6966_, 4, v_goal_6950_);
v___x_6967_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg(v_goal_6950_, v___f_6966_, v_a_6952_, v_a_6953_, v_a_6954_, v_a_6955_, v_a_6956_, v_a_6957_, v_a_6958_, v_a_6959_, v_a_6960_, v_a_6961_, v_a_6962_);
return v___x_6967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs___boxed(lean_object* v_scope_6968_, lean_object* v_goal_6969_, lean_object* v_info_6970_, lean_object* v_a_6971_, lean_object* v_a_6972_, lean_object* v_a_6973_, lean_object* v_a_6974_, lean_object* v_a_6975_, lean_object* v_a_6976_, lean_object* v_a_6977_, lean_object* v_a_6978_, lean_object* v_a_6979_, lean_object* v_a_6980_, lean_object* v_a_6981_, lean_object* v_a_6982_){
_start:
{
lean_object* v_res_6983_; 
v_res_6983_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(v_scope_6968_, v_goal_6969_, v_info_6970_, v_a_6971_, v_a_6972_, v_a_6973_, v_a_6974_, v_a_6975_, v_a_6976_, v_a_6977_, v_a_6978_, v_a_6979_, v_a_6980_, v_a_6981_);
lean_dec(v_a_6981_);
lean_dec_ref(v_a_6980_);
lean_dec(v_a_6979_);
lean_dec_ref(v_a_6978_);
lean_dec(v_a_6977_);
lean_dec_ref(v_a_6976_);
lean_dec(v_a_6975_);
lean_dec_ref(v_a_6974_);
lean_dec(v_a_6973_);
lean_dec(v_a_6972_);
lean_dec_ref(v_a_6971_);
return v_res_6983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1(lean_object* v_00_u03b2_6984_, lean_object* v_m_6985_, lean_object* v_a_6986_){
_start:
{
lean_object* v___x_6987_; 
v___x_6987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1___redArg(v_m_6985_, v_a_6986_);
return v___x_6987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1___boxed(lean_object* v_00_u03b2_6988_, lean_object* v_m_6989_, lean_object* v_a_6990_){
_start:
{
lean_object* v_res_6991_; 
v_res_6991_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1(v_00_u03b2_6988_, v_m_6989_, v_a_6990_);
lean_dec(v_a_6990_);
lean_dec_ref(v_m_6989_);
return v_res_6991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1(lean_object* v_00_u03b2_6992_, lean_object* v_a_6993_, lean_object* v_x_6994_){
_start:
{
lean_object* v___x_6995_; 
v___x_6995_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1___redArg(v_a_6993_, v_x_6994_);
return v___x_6995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1___boxed(lean_object* v_00_u03b2_6996_, lean_object* v_a_6997_, lean_object* v_x_6998_){
_start:
{
lean_object* v_res_6999_; 
v_res_6999_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs_spec__1_spec__1(v_00_u03b2_6996_, v_a_6997_, v_x_6998_);
lean_dec(v_x_6998_);
lean_dec(v_a_6997_);
return v_res_6999_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2(void){
_start:
{
lean_object* v___x_7003_; lean_object* v___x_7004_; 
v___x_7003_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__1));
v___x_7004_ = l_Lean_stringToMessageData(v___x_7003_);
return v___x_7004_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4(void){
_start:
{
lean_object* v___x_7006_; lean_object* v___x_7007_; 
v___x_7006_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__3));
v___x_7007_ = l_Lean_stringToMessageData(v___x_7006_);
return v___x_7007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0(lean_object* v_scope_7010_, lean_object* v_goal_7011_, lean_object* v___y_7012_, lean_object* v___y_7013_, lean_object* v___y_7014_, lean_object* v___y_7015_, lean_object* v___y_7016_, lean_object* v___y_7017_, lean_object* v___y_7018_, lean_object* v___y_7019_, lean_object* v___y_7020_, lean_object* v___y_7021_, lean_object* v___y_7022_){
_start:
{
lean_object* v_g_7025_; lean_object* v_gs_7031_; lean_object* v___y_7035_; lean_object* v_gs_7036_; lean_object* v___y_7040_; lean_object* v_gs_7041_; lean_object* v___y_7042_; lean_object* v___y_7062_; lean_object* v_g_7063_; lean_object* v___y_7064_; lean_object* v___y_7086_; lean_object* v___y_7087_; lean_object* v___y_7088_; lean_object* v___y_7089_; lean_object* v___y_7090_; lean_object* v___y_7091_; lean_object* v___y_7092_; lean_object* v___y_7093_; lean_object* v___y_7094_; lean_object* v___y_7095_; lean_object* v___y_7096_; lean_object* v___y_7097_; lean_object* v___y_7098_; lean_object* v___y_7110_; lean_object* v___y_7111_; lean_object* v___y_7112_; lean_object* v___y_7113_; lean_object* v___y_7114_; lean_object* v___y_7115_; lean_object* v___y_7116_; lean_object* v___y_7117_; lean_object* v___y_7118_; lean_object* v___y_7119_; lean_object* v___y_7120_; lean_object* v___y_7121_; lean_object* v___y_7122_; lean_object* v___x_7264_; 
v___x_7264_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v___y_7013_);
if (lean_obj_tag(v___x_7264_) == 0)
{
lean_object* v_a_7265_; lean_object* v___x_7267_; uint8_t v_isShared_7268_; uint8_t v_isSharedCheck_7539_; 
v_a_7265_ = lean_ctor_get(v___x_7264_, 0);
v_isSharedCheck_7539_ = !lean_is_exclusive(v___x_7264_);
if (v_isSharedCheck_7539_ == 0)
{
v___x_7267_ = v___x_7264_;
v_isShared_7268_ = v_isSharedCheck_7539_;
goto v_resetjp_7266_;
}
else
{
lean_inc(v_a_7265_);
lean_dec(v___x_7264_);
v___x_7267_ = lean_box(0);
v_isShared_7268_ = v_isSharedCheck_7539_;
goto v_resetjp_7266_;
}
v_resetjp_7266_:
{
uint8_t v___x_7269_; 
v___x_7269_ = lean_unbox(v_a_7265_);
lean_dec(v_a_7265_);
if (v___x_7269_ == 0)
{
lean_object* v___x_7270_; 
lean_del_object(v___x_7267_);
lean_inc(v_goal_7011_);
v___x_7270_ = l_Lean_MVarId_getType(v_goal_7011_, v___y_7019_, v___y_7020_, v___y_7021_, v___y_7022_);
if (lean_obj_tag(v___x_7270_) == 0)
{
lean_object* v_a_7271_; lean_object* v___x_7273_; uint8_t v_isShared_7274_; uint8_t v_isSharedCheck_7526_; 
v_a_7271_ = lean_ctor_get(v___x_7270_, 0);
v_isSharedCheck_7526_ = !lean_is_exclusive(v___x_7270_);
if (v_isSharedCheck_7526_ == 0)
{
v___x_7273_ = v___x_7270_;
v_isShared_7274_ = v_isSharedCheck_7526_;
goto v_resetjp_7272_;
}
else
{
lean_inc(v_a_7271_);
lean_dec(v___x_7270_);
v___x_7273_ = lean_box(0);
v_isShared_7274_ = v_isSharedCheck_7526_;
goto v_resetjp_7272_;
}
v_resetjp_7272_:
{
lean_object* v_toCold_7281_; lean_object* v_options_7282_; lean_object* v_inheritedTraceOptions_7283_; uint8_t v_hasTrace_7284_; lean_object* v___x_7285_; lean_object* v___y_7287_; lean_object* v___y_7288_; lean_object* v___y_7289_; lean_object* v___y_7290_; lean_object* v___y_7291_; lean_object* v___y_7292_; lean_object* v___y_7293_; lean_object* v___y_7294_; lean_object* v___y_7295_; lean_object* v___y_7296_; lean_object* v___y_7297_; 
v_toCold_7281_ = lean_ctor_get(v___y_7021_, 0);
v_options_7282_ = lean_ctor_get(v_toCold_7281_, 2);
v_inheritedTraceOptions_7283_ = lean_ctor_get(v_toCold_7281_, 11);
v_hasTrace_7284_ = lean_ctor_get_uint8(v_options_7282_, sizeof(void*)*1);
v___x_7285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_7284_ == 0)
{
v___y_7287_ = v___y_7012_;
v___y_7288_ = v___y_7013_;
v___y_7289_ = v___y_7014_;
v___y_7290_ = v___y_7015_;
v___y_7291_ = v___y_7016_;
v___y_7292_ = v___y_7017_;
v___y_7293_ = v___y_7018_;
v___y_7294_ = v___y_7019_;
v___y_7295_ = v___y_7020_;
v___y_7296_ = v___y_7021_;
v___y_7297_ = v___y_7022_;
goto v___jp_7286_;
}
else
{
lean_object* v___x_7512_; uint8_t v___x_7513_; 
v___x_7512_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_7513_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_7283_, v_options_7282_, v___x_7512_);
if (v___x_7513_ == 0)
{
v___y_7287_ = v___y_7012_;
v___y_7288_ = v___y_7013_;
v___y_7289_ = v___y_7014_;
v___y_7290_ = v___y_7015_;
v___y_7291_ = v___y_7016_;
v___y_7292_ = v___y_7017_;
v___y_7293_ = v___y_7018_;
v___y_7294_ = v___y_7019_;
v___y_7295_ = v___y_7020_;
v___y_7296_ = v___y_7021_;
v___y_7297_ = v___y_7022_;
goto v___jp_7286_;
}
else
{
lean_object* v___x_7514_; lean_object* v___x_7515_; lean_object* v___x_7516_; lean_object* v___x_7517_; 
v___x_7514_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__4);
lean_inc(v_a_7271_);
v___x_7515_ = l_Lean_MessageData_ofExpr(v_a_7271_);
v___x_7516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7516_, 0, v___x_7514_);
lean_ctor_set(v___x_7516_, 1, v___x_7515_);
v___x_7517_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_7285_, v___x_7516_, v___y_7019_, v___y_7020_, v___y_7021_, v___y_7022_);
if (lean_obj_tag(v___x_7517_) == 0)
{
lean_dec_ref_known(v___x_7517_, 1);
v___y_7287_ = v___y_7012_;
v___y_7288_ = v___y_7013_;
v___y_7289_ = v___y_7014_;
v___y_7290_ = v___y_7015_;
v___y_7291_ = v___y_7016_;
v___y_7292_ = v___y_7017_;
v___y_7293_ = v___y_7018_;
v___y_7294_ = v___y_7019_;
v___y_7295_ = v___y_7020_;
v___y_7296_ = v___y_7021_;
v___y_7297_ = v___y_7022_;
goto v___jp_7286_;
}
else
{
lean_object* v_a_7518_; lean_object* v___x_7520_; uint8_t v_isShared_7521_; uint8_t v_isSharedCheck_7525_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7518_ = lean_ctor_get(v___x_7517_, 0);
v_isSharedCheck_7525_ = !lean_is_exclusive(v___x_7517_);
if (v_isSharedCheck_7525_ == 0)
{
v___x_7520_ = v___x_7517_;
v_isShared_7521_ = v_isSharedCheck_7525_;
goto v_resetjp_7519_;
}
else
{
lean_inc(v_a_7518_);
lean_dec(v___x_7517_);
v___x_7520_ = lean_box(0);
v_isShared_7521_ = v_isSharedCheck_7525_;
goto v_resetjp_7519_;
}
v_resetjp_7519_:
{
lean_object* v___x_7523_; 
if (v_isShared_7521_ == 0)
{
v___x_7523_ = v___x_7520_;
goto v_reusejp_7522_;
}
else
{
lean_object* v_reuseFailAlloc_7524_; 
v_reuseFailAlloc_7524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7524_, 0, v_a_7518_);
v___x_7523_ = v_reuseFailAlloc_7524_;
goto v_reusejp_7522_;
}
v_reusejp_7522_:
{
return v___x_7523_;
}
}
}
}
}
v___jp_7275_:
{
lean_object* v___x_7276_; lean_object* v___x_7277_; lean_object* v___x_7279_; 
v___x_7276_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_7276_, 0, v_a_7271_);
v___x_7277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7277_, 0, v___x_7276_);
if (v_isShared_7274_ == 0)
{
lean_ctor_set(v___x_7273_, 0, v___x_7277_);
v___x_7279_ = v___x_7273_;
goto v_reusejp_7278_;
}
else
{
lean_object* v_reuseFailAlloc_7280_; 
v_reuseFailAlloc_7280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7280_, 0, v___x_7277_);
v___x_7279_ = v_reuseFailAlloc_7280_;
goto v_reusejp_7278_;
}
v_reusejp_7278_:
{
return v___x_7279_;
}
}
v___jp_7286_:
{
lean_object* v___x_7298_; 
lean_inc(v_goal_7011_);
v___x_7298_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_consumeMData_x3f___redArg(v_goal_7011_, v_a_7271_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7298_) == 0)
{
lean_object* v_a_7299_; 
v_a_7299_ = lean_ctor_get(v___x_7298_, 0);
lean_inc(v_a_7299_);
lean_dec_ref_known(v___x_7298_, 1);
if (lean_obj_tag(v_a_7299_) == 1)
{
lean_object* v_val_7300_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
v_val_7300_ = lean_ctor_get(v_a_7299_, 0);
lean_inc(v_val_7300_);
lean_dec_ref_known(v_a_7299_, 1);
v_g_7025_ = v_val_7300_;
goto v___jp_7024_;
}
else
{
lean_object* v___x_7301_; 
lean_dec(v_a_7299_);
lean_inc(v_a_7271_);
lean_inc(v_goal_7011_);
v___x_7301_ = l_Lean_Elab_Tactic_VCGen_consumeBinderNameHint_x3f(v_goal_7011_, v_a_7271_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7301_) == 0)
{
lean_object* v_a_7302_; 
v_a_7302_ = lean_ctor_get(v___x_7301_, 0);
lean_inc(v_a_7302_);
lean_dec_ref_known(v___x_7301_, 1);
if (lean_obj_tag(v_a_7302_) == 1)
{
lean_object* v_val_7303_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
v_val_7303_ = lean_ctor_get(v_a_7302_, 0);
lean_inc(v_val_7303_);
lean_dec_ref_known(v_a_7302_, 1);
v_g_7025_ = v_val_7303_;
goto v___jp_7024_;
}
else
{
lean_object* v___x_7304_; 
lean_dec(v_a_7302_);
lean_inc(v_goal_7011_);
v___x_7304_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_forallIntro_x3f(v_goal_7011_, v_a_7271_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7304_) == 0)
{
lean_object* v_a_7305_; 
v_a_7305_ = lean_ctor_get(v___x_7304_, 0);
lean_inc(v_a_7305_);
lean_dec_ref_known(v___x_7304_, 1);
if (lean_obj_tag(v_a_7305_) == 1)
{
lean_object* v_val_7306_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
v_val_7306_ = lean_ctor_get(v_a_7305_, 0);
lean_inc(v_val_7306_);
lean_dec_ref_known(v_a_7305_, 1);
v_gs_7031_ = v_val_7306_;
goto v___jp_7030_;
}
else
{
lean_object* v___x_7307_; 
lean_dec(v_a_7305_);
lean_inc(v_a_7271_);
lean_inc(v_goal_7011_);
v___x_7307_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f(v_goal_7011_, v_a_7271_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7307_) == 0)
{
lean_object* v_a_7308_; 
v_a_7308_ = lean_ctor_get(v___x_7307_, 0);
lean_inc(v_a_7308_);
lean_dec_ref_known(v___x_7307_, 1);
if (lean_obj_tag(v_a_7308_) == 1)
{
lean_object* v_val_7309_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
v_val_7309_ = lean_ctor_get(v_a_7308_, 0);
lean_inc(v_val_7309_);
lean_dec_ref_known(v_a_7308_, 1);
v_g_7025_ = v_val_7309_;
goto v___jp_7024_;
}
else
{
lean_object* v___x_7310_; 
lean_dec(v_a_7308_);
lean_inc(v_goal_7011_);
v___x_7310_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_tripleUnfold_x3f(v_goal_7011_, v_a_7271_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7310_) == 0)
{
lean_object* v_a_7311_; 
v_a_7311_ = lean_ctor_get(v___x_7310_, 0);
lean_inc(v_a_7311_);
lean_dec_ref_known(v___x_7310_, 1);
if (lean_obj_tag(v_a_7311_) == 1)
{
lean_object* v_val_7312_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
v_val_7312_ = lean_ctor_get(v_a_7311_, 0);
lean_inc(v_val_7312_);
lean_dec_ref_known(v_a_7311_, 1);
v_g_7025_ = v_val_7312_;
goto v___jp_7024_;
}
else
{
lean_object* v___x_7313_; 
lean_dec(v_a_7311_);
lean_inc(v_a_7271_);
lean_inc(v_goal_7011_);
v___x_7313_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg(v_goal_7011_, v_a_7271_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7313_) == 0)
{
lean_object* v_a_7314_; 
v_a_7314_ = lean_ctor_get(v___x_7313_, 0);
lean_inc(v_a_7314_);
lean_dec_ref_known(v___x_7313_, 1);
if (lean_obj_tag(v_a_7314_) == 1)
{
lean_object* v_val_7315_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
v_val_7315_ = lean_ctor_get(v_a_7314_, 0);
lean_inc(v_val_7315_);
lean_dec_ref_known(v_a_7314_, 1);
v_g_7025_ = v_val_7315_;
goto v___jp_7024_;
}
else
{
lean_object* v___x_7316_; 
lean_dec(v_a_7314_);
lean_inc(v_a_7271_);
lean_inc(v_goal_7011_);
lean_inc_ref(v_scope_7010_);
v___x_7316_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHypBare_x3f(v_scope_7010_, v_goal_7011_, v_a_7271_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7316_) == 0)
{
lean_object* v_a_7317_; 
v_a_7317_ = lean_ctor_get(v___x_7316_, 0);
lean_inc(v_a_7317_);
lean_dec_ref_known(v___x_7316_, 1);
if (lean_obj_tag(v_a_7317_) == 1)
{
lean_object* v_val_7318_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
v_val_7318_ = lean_ctor_get(v_a_7317_, 0);
lean_inc(v_val_7318_);
lean_dec_ref_known(v_a_7317_, 1);
v_gs_7031_ = v_val_7318_;
goto v___jp_7030_;
}
else
{
lean_object* v___x_7319_; 
lean_dec(v_a_7317_);
lean_inc(v_goal_7011_);
v___x_7319_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_instantiateGoal_x3f(v_goal_7011_, v_a_7271_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7319_) == 0)
{
lean_object* v_a_7320_; 
v_a_7320_ = lean_ctor_get(v___x_7319_, 0);
lean_inc(v_a_7320_);
lean_dec_ref_known(v___x_7319_, 1);
if (lean_obj_tag(v_a_7320_) == 1)
{
lean_object* v_val_7321_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
v_val_7321_ = lean_ctor_get(v_a_7320_, 0);
lean_inc(v_val_7321_);
lean_dec_ref_known(v_a_7320_, 1);
v_g_7025_ = v_val_7321_;
goto v___jp_7024_;
}
else
{
lean_object* v___x_7322_; uint8_t v___x_7323_; 
lean_dec(v_a_7320_);
v___x_7322_ = l_Lean_Expr_cleanupAnnotations(v_a_7271_);
v___x_7323_ = l_Lean_Expr_isApp(v___x_7322_);
if (v___x_7323_ == 0)
{
lean_dec_ref(v___x_7322_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
goto v___jp_7275_;
}
else
{
lean_object* v___x_7324_; uint8_t v___x_7325_; 
v___x_7324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7322_);
v___x_7325_ = l_Lean_Expr_isApp(v___x_7324_);
if (v___x_7325_ == 0)
{
lean_dec_ref(v___x_7324_);
lean_dec_ref(v___x_7322_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
goto v___jp_7275_;
}
else
{
lean_object* v___x_7326_; uint8_t v___x_7327_; 
v___x_7326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7324_);
v___x_7327_ = l_Lean_Expr_isApp(v___x_7326_);
if (v___x_7327_ == 0)
{
lean_dec_ref(v___x_7326_);
lean_dec_ref(v___x_7324_);
lean_dec_ref(v___x_7322_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
goto v___jp_7275_;
}
else
{
lean_object* v___x_7328_; uint8_t v___x_7329_; 
v___x_7328_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7326_);
lean_dec_ref(v___x_7326_);
v___x_7329_ = l_Lean_Expr_isApp(v___x_7328_);
if (v___x_7329_ == 0)
{
lean_dec_ref(v___x_7328_);
lean_dec_ref(v___x_7324_);
lean_dec_ref(v___x_7322_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
goto v___jp_7275_;
}
else
{
lean_object* v___x_7330_; lean_object* v___x_7331_; uint8_t v___x_7332_; 
v___x_7330_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7328_);
v___x_7331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_bareWPToLe_x3f___redArg___closed__10));
v___x_7332_ = l_Lean_Expr_isConstOf(v___x_7330_, v___x_7331_);
lean_dec_ref(v___x_7330_);
if (v___x_7332_ == 0)
{
lean_dec_ref(v___x_7328_);
lean_dec_ref(v___x_7324_);
lean_dec_ref(v___x_7322_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
goto v___jp_7275_;
}
else
{
lean_object* v_arg_7333_; lean_object* v_arg_7334_; lean_object* v_arg_7335_; lean_object* v___x_7336_; 
lean_del_object(v___x_7273_);
v_arg_7333_ = lean_ctor_get(v___x_7322_, 1);
lean_inc_ref(v_arg_7333_);
lean_dec_ref(v___x_7322_);
v_arg_7334_ = lean_ctor_get(v___x_7324_, 1);
lean_inc_ref(v_arg_7334_);
lean_dec_ref(v___x_7324_);
v_arg_7335_ = lean_ctor_get(v___x_7328_, 1);
lean_inc_ref(v_arg_7335_);
lean_dec_ref(v___x_7328_);
lean_inc(v_goal_7011_);
v___x_7336_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_rfl_x3f___redArg(v_goal_7011_, v___y_7287_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7336_) == 0)
{
lean_object* v_a_7337_; 
v_a_7337_ = lean_ctor_get(v___x_7336_, 0);
lean_inc(v_a_7337_);
lean_dec_ref_known(v___x_7336_, 1);
if (lean_obj_tag(v_a_7337_) == 1)
{
lean_object* v_val_7338_; 
lean_dec_ref(v_arg_7335_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
v_val_7338_ = lean_ctor_get(v_a_7337_, 0);
lean_inc(v_val_7338_);
lean_dec_ref_known(v_a_7337_, 1);
v_gs_7031_ = v_val_7338_;
goto v___jp_7030_;
}
else
{
lean_object* v___x_7339_; 
lean_dec(v_a_7337_);
lean_inc_ref(v_arg_7334_);
lean_inc(v_goal_7011_);
lean_inc_ref(v_scope_7010_);
v___x_7339_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_normalizePre_x3f(v_scope_7010_, v_goal_7011_, v_arg_7335_, v_arg_7334_, v_a_7271_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7339_) == 0)
{
lean_object* v_a_7340_; lean_object* v___x_7342_; uint8_t v_isShared_7343_; uint8_t v_isSharedCheck_7431_; 
v_a_7340_ = lean_ctor_get(v___x_7339_, 0);
v_isSharedCheck_7431_ = !lean_is_exclusive(v___x_7339_);
if (v_isSharedCheck_7431_ == 0)
{
v___x_7342_ = v___x_7339_;
v_isShared_7343_ = v_isSharedCheck_7431_;
goto v_resetjp_7341_;
}
else
{
lean_inc(v_a_7340_);
lean_dec(v___x_7339_);
v___x_7342_ = lean_box(0);
v_isShared_7343_ = v_isSharedCheck_7431_;
goto v_resetjp_7341_;
}
v_resetjp_7341_:
{
if (lean_obj_tag(v_a_7340_) == 1)
{
lean_object* v_val_7344_; lean_object* v_fst_7345_; lean_object* v_snd_7346_; lean_object* v___x_7348_; uint8_t v_isShared_7349_; uint8_t v_isSharedCheck_7356_; 
lean_dec_ref(v_arg_7335_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_val_7344_ = lean_ctor_get(v_a_7340_, 0);
lean_inc(v_val_7344_);
lean_dec_ref_known(v_a_7340_, 1);
v_fst_7345_ = lean_ctor_get(v_val_7344_, 0);
v_snd_7346_ = lean_ctor_get(v_val_7344_, 1);
v_isSharedCheck_7356_ = !lean_is_exclusive(v_val_7344_);
if (v_isSharedCheck_7356_ == 0)
{
v___x_7348_ = v_val_7344_;
v_isShared_7349_ = v_isSharedCheck_7356_;
goto v_resetjp_7347_;
}
else
{
lean_inc(v_snd_7346_);
lean_inc(v_fst_7345_);
lean_dec(v_val_7344_);
v___x_7348_ = lean_box(0);
v_isShared_7349_ = v_isSharedCheck_7356_;
goto v_resetjp_7347_;
}
v_resetjp_7347_:
{
lean_object* v___x_7351_; 
if (v_isShared_7349_ == 0)
{
v___x_7351_ = v___x_7348_;
goto v_reusejp_7350_;
}
else
{
lean_object* v_reuseFailAlloc_7355_; 
v_reuseFailAlloc_7355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7355_, 0, v_fst_7345_);
lean_ctor_set(v_reuseFailAlloc_7355_, 1, v_snd_7346_);
v___x_7351_ = v_reuseFailAlloc_7355_;
goto v_reusejp_7350_;
}
v_reusejp_7350_:
{
lean_object* v___x_7353_; 
if (v_isShared_7343_ == 0)
{
lean_ctor_set(v___x_7342_, 0, v___x_7351_);
v___x_7353_ = v___x_7342_;
goto v_reusejp_7352_;
}
else
{
lean_object* v_reuseFailAlloc_7354_; 
v_reuseFailAlloc_7354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7354_, 0, v___x_7351_);
v___x_7353_ = v_reuseFailAlloc_7354_;
goto v_reusejp_7352_;
}
v_reusejp_7352_:
{
return v___x_7353_;
}
}
}
}
else
{
lean_object* v___x_7357_; 
lean_del_object(v___x_7342_);
lean_dec(v_a_7340_);
lean_inc(v_goal_7011_);
v___x_7357_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(v_scope_7010_, v_goal_7011_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7357_) == 0)
{
lean_object* v_a_7358_; lean_object* v___x_7359_; 
v_a_7358_ = lean_ctor_get(v___x_7357_, 0);
lean_inc(v_a_7358_);
lean_dec_ref_known(v___x_7357_, 1);
lean_inc_ref(v_arg_7333_);
lean_inc(v_goal_7011_);
v___x_7359_ = l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(v_goal_7011_, v_arg_7333_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7359_) == 0)
{
lean_object* v_a_7360_; 
v_a_7360_ = lean_ctor_get(v___x_7359_, 0);
lean_inc(v_a_7360_);
lean_dec_ref_known(v___x_7359_, 1);
if (lean_obj_tag(v_a_7360_) == 1)
{
lean_object* v_val_7361_; 
lean_dec_ref(v_arg_7335_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
lean_dec(v_goal_7011_);
v_val_7361_ = lean_ctor_get(v_a_7360_, 0);
lean_inc(v_val_7361_);
lean_dec_ref_known(v_a_7360_, 1);
v___y_7035_ = v_a_7358_;
v_gs_7036_ = v_val_7361_;
goto v___jp_7034_;
}
else
{
lean_object* v___x_7362_; 
lean_dec(v_a_7360_);
lean_inc(v_goal_7011_);
v___x_7362_ = l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(v_goal_7011_, v_arg_7333_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7362_) == 0)
{
lean_object* v_a_7363_; 
v_a_7363_ = lean_ctor_get(v___x_7362_, 0);
lean_inc(v_a_7363_);
lean_dec_ref_known(v___x_7362_, 1);
if (lean_obj_tag(v_a_7363_) == 1)
{
lean_object* v_val_7364_; 
lean_dec_ref(v_arg_7335_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
lean_dec(v_goal_7011_);
v_val_7364_ = lean_ctor_get(v_a_7363_, 0);
lean_inc(v_val_7364_);
lean_dec_ref_known(v_a_7363_, 1);
v___y_7035_ = v_a_7358_;
v_gs_7036_ = v_val_7364_;
goto v___jp_7034_;
}
else
{
lean_object* v___x_7365_; 
lean_dec(v_a_7363_);
lean_inc_ref(v_arg_7333_);
lean_inc_ref(v_arg_7334_);
lean_inc(v_goal_7011_);
lean_inc(v_a_7358_);
v___x_7365_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_liftedHyp_x3f(v_a_7358_, v_goal_7011_, v_arg_7335_, v_arg_7334_, v_arg_7333_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_, v___y_7293_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
lean_dec_ref(v_arg_7335_);
if (lean_obj_tag(v___x_7365_) == 0)
{
lean_object* v_a_7366_; lean_object* v___x_7368_; uint8_t v_isShared_7369_; uint8_t v_isSharedCheck_7398_; 
v_a_7366_ = lean_ctor_get(v___x_7365_, 0);
v_isSharedCheck_7398_ = !lean_is_exclusive(v___x_7365_);
if (v_isSharedCheck_7398_ == 0)
{
v___x_7368_ = v___x_7365_;
v_isShared_7369_ = v_isSharedCheck_7398_;
goto v_resetjp_7367_;
}
else
{
lean_inc(v_a_7366_);
lean_dec(v___x_7365_);
v___x_7368_ = lean_box(0);
v_isShared_7369_ = v_isSharedCheck_7398_;
goto v_resetjp_7367_;
}
v_resetjp_7367_:
{
if (lean_obj_tag(v_a_7366_) == 1)
{
lean_object* v_val_7370_; 
lean_del_object(v___x_7368_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
lean_dec(v_goal_7011_);
v_val_7370_ = lean_ctor_get(v_a_7366_, 0);
lean_inc(v_val_7370_);
lean_dec_ref_known(v_a_7366_, 1);
v___y_7035_ = v_a_7358_;
v_gs_7036_ = v_val_7370_;
goto v___jp_7034_;
}
else
{
lean_object* v___x_7371_; 
lean_dec(v_a_7366_);
lean_inc_ref(v_arg_7333_);
v___x_7371_ = l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(v_arg_7333_);
if (lean_obj_tag(v___x_7371_) == 1)
{
lean_object* v_toCold_7372_; lean_object* v_options_7373_; uint8_t v_hasTrace_7374_; 
lean_del_object(v___x_7368_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
v_toCold_7372_ = lean_ctor_get(v___y_7296_, 0);
v_options_7373_ = lean_ctor_get(v_toCold_7372_, 2);
v_hasTrace_7374_ = lean_ctor_get_uint8(v_options_7373_, sizeof(void*)*1);
if (v_hasTrace_7374_ == 0)
{
lean_object* v_val_7375_; 
v_val_7375_ = lean_ctor_get(v___x_7371_, 0);
lean_inc(v_val_7375_);
lean_dec_ref_known(v___x_7371_, 1);
v___y_7110_ = v_val_7375_;
v___y_7111_ = v_a_7358_;
v___y_7112_ = v___y_7287_;
v___y_7113_ = v___y_7288_;
v___y_7114_ = v___y_7289_;
v___y_7115_ = v___y_7290_;
v___y_7116_ = v___y_7291_;
v___y_7117_ = v___y_7292_;
v___y_7118_ = v___y_7293_;
v___y_7119_ = v___y_7294_;
v___y_7120_ = v___y_7295_;
v___y_7121_ = v___y_7296_;
v___y_7122_ = v___y_7297_;
goto v___jp_7109_;
}
else
{
lean_object* v_val_7376_; lean_object* v_inheritedTraceOptions_7377_; lean_object* v___x_7378_; uint8_t v___x_7379_; 
v_val_7376_ = lean_ctor_get(v___x_7371_, 0);
lean_inc(v_val_7376_);
lean_dec_ref_known(v___x_7371_, 1);
v_inheritedTraceOptions_7377_ = lean_ctor_get(v_toCold_7372_, 11);
v___x_7378_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f___closed__7);
v___x_7379_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_7377_, v_options_7373_, v___x_7378_);
if (v___x_7379_ == 0)
{
v___y_7110_ = v_val_7376_;
v___y_7111_ = v_a_7358_;
v___y_7112_ = v___y_7287_;
v___y_7113_ = v___y_7288_;
v___y_7114_ = v___y_7289_;
v___y_7115_ = v___y_7290_;
v___y_7116_ = v___y_7291_;
v___y_7117_ = v___y_7292_;
v___y_7118_ = v___y_7293_;
v___y_7119_ = v___y_7294_;
v___y_7120_ = v___y_7295_;
v___y_7121_ = v___y_7296_;
v___y_7122_ = v___y_7297_;
goto v___jp_7109_;
}
else
{
lean_object* v___x_7380_; lean_object* v___x_7381_; lean_object* v___x_7382_; lean_object* v___x_7383_; lean_object* v___x_7384_; 
v___x_7380_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2, &l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__2);
v___x_7381_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v_val_7376_);
v___x_7382_ = l_Lean_MessageData_ofExpr(v___x_7381_);
v___x_7383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7383_, 0, v___x_7380_);
lean_ctor_set(v___x_7383_, 1, v___x_7382_);
v___x_7384_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_7285_, v___x_7383_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
if (lean_obj_tag(v___x_7384_) == 0)
{
lean_dec_ref_known(v___x_7384_, 1);
v___y_7110_ = v_val_7376_;
v___y_7111_ = v_a_7358_;
v___y_7112_ = v___y_7287_;
v___y_7113_ = v___y_7288_;
v___y_7114_ = v___y_7289_;
v___y_7115_ = v___y_7290_;
v___y_7116_ = v___y_7291_;
v___y_7117_ = v___y_7292_;
v___y_7118_ = v___y_7293_;
v___y_7119_ = v___y_7294_;
v___y_7120_ = v___y_7295_;
v___y_7121_ = v___y_7296_;
v___y_7122_ = v___y_7297_;
goto v___jp_7109_;
}
else
{
lean_object* v_a_7385_; lean_object* v___x_7387_; uint8_t v_isShared_7388_; uint8_t v_isSharedCheck_7392_; 
lean_dec(v_val_7376_);
lean_dec(v_a_7358_);
lean_dec(v_goal_7011_);
v_a_7385_ = lean_ctor_get(v___x_7384_, 0);
v_isSharedCheck_7392_ = !lean_is_exclusive(v___x_7384_);
if (v_isSharedCheck_7392_ == 0)
{
v___x_7387_ = v___x_7384_;
v_isShared_7388_ = v_isSharedCheck_7392_;
goto v_resetjp_7386_;
}
else
{
lean_inc(v_a_7385_);
lean_dec(v___x_7384_);
v___x_7387_ = lean_box(0);
v_isShared_7388_ = v_isSharedCheck_7392_;
goto v_resetjp_7386_;
}
v_resetjp_7386_:
{
lean_object* v___x_7390_; 
if (v_isShared_7388_ == 0)
{
v___x_7390_ = v___x_7387_;
goto v_reusejp_7389_;
}
else
{
lean_object* v_reuseFailAlloc_7391_; 
v_reuseFailAlloc_7391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7391_, 0, v_a_7385_);
v___x_7390_ = v_reuseFailAlloc_7391_;
goto v_reusejp_7389_;
}
v_reusejp_7389_:
{
return v___x_7390_;
}
}
}
}
}
}
else
{
lean_object* v___x_7393_; lean_object* v___x_7394_; lean_object* v___x_7396_; 
lean_dec(v___x_7371_);
lean_dec(v_a_7358_);
lean_dec(v_goal_7011_);
v___x_7393_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_7393_, 0, v_arg_7334_);
lean_ctor_set(v___x_7393_, 1, v_arg_7333_);
v___x_7394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7394_, 0, v___x_7393_);
if (v_isShared_7369_ == 0)
{
lean_ctor_set(v___x_7368_, 0, v___x_7394_);
v___x_7396_ = v___x_7368_;
goto v_reusejp_7395_;
}
else
{
lean_object* v_reuseFailAlloc_7397_; 
v_reuseFailAlloc_7397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7397_, 0, v___x_7394_);
v___x_7396_ = v_reuseFailAlloc_7397_;
goto v_reusejp_7395_;
}
v_reusejp_7395_:
{
return v___x_7396_;
}
}
}
}
}
else
{
lean_object* v_a_7399_; lean_object* v___x_7401_; uint8_t v_isShared_7402_; uint8_t v_isSharedCheck_7406_; 
lean_dec(v_a_7358_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
lean_dec(v_goal_7011_);
v_a_7399_ = lean_ctor_get(v___x_7365_, 0);
v_isSharedCheck_7406_ = !lean_is_exclusive(v___x_7365_);
if (v_isSharedCheck_7406_ == 0)
{
v___x_7401_ = v___x_7365_;
v_isShared_7402_ = v_isSharedCheck_7406_;
goto v_resetjp_7400_;
}
else
{
lean_inc(v_a_7399_);
lean_dec(v___x_7365_);
v___x_7401_ = lean_box(0);
v_isShared_7402_ = v_isSharedCheck_7406_;
goto v_resetjp_7400_;
}
v_resetjp_7400_:
{
lean_object* v___x_7404_; 
if (v_isShared_7402_ == 0)
{
v___x_7404_ = v___x_7401_;
goto v_reusejp_7403_;
}
else
{
lean_object* v_reuseFailAlloc_7405_; 
v_reuseFailAlloc_7405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7405_, 0, v_a_7399_);
v___x_7404_ = v_reuseFailAlloc_7405_;
goto v_reusejp_7403_;
}
v_reusejp_7403_:
{
return v___x_7404_;
}
}
}
}
}
else
{
lean_object* v_a_7407_; lean_object* v___x_7409_; uint8_t v_isShared_7410_; uint8_t v_isSharedCheck_7414_; 
lean_dec(v_a_7358_);
lean_dec_ref(v_arg_7335_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
lean_dec(v_goal_7011_);
v_a_7407_ = lean_ctor_get(v___x_7362_, 0);
v_isSharedCheck_7414_ = !lean_is_exclusive(v___x_7362_);
if (v_isSharedCheck_7414_ == 0)
{
v___x_7409_ = v___x_7362_;
v_isShared_7410_ = v_isSharedCheck_7414_;
goto v_resetjp_7408_;
}
else
{
lean_inc(v_a_7407_);
lean_dec(v___x_7362_);
v___x_7409_ = lean_box(0);
v_isShared_7410_ = v_isSharedCheck_7414_;
goto v_resetjp_7408_;
}
v_resetjp_7408_:
{
lean_object* v___x_7412_; 
if (v_isShared_7410_ == 0)
{
v___x_7412_ = v___x_7409_;
goto v_reusejp_7411_;
}
else
{
lean_object* v_reuseFailAlloc_7413_; 
v_reuseFailAlloc_7413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7413_, 0, v_a_7407_);
v___x_7412_ = v_reuseFailAlloc_7413_;
goto v_reusejp_7411_;
}
v_reusejp_7411_:
{
return v___x_7412_;
}
}
}
}
}
else
{
lean_object* v_a_7415_; lean_object* v___x_7417_; uint8_t v_isShared_7418_; uint8_t v_isSharedCheck_7422_; 
lean_dec(v_a_7358_);
lean_dec_ref(v_arg_7335_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
lean_dec(v_goal_7011_);
v_a_7415_ = lean_ctor_get(v___x_7359_, 0);
v_isSharedCheck_7422_ = !lean_is_exclusive(v___x_7359_);
if (v_isSharedCheck_7422_ == 0)
{
v___x_7417_ = v___x_7359_;
v_isShared_7418_ = v_isSharedCheck_7422_;
goto v_resetjp_7416_;
}
else
{
lean_inc(v_a_7415_);
lean_dec(v___x_7359_);
v___x_7417_ = lean_box(0);
v_isShared_7418_ = v_isSharedCheck_7422_;
goto v_resetjp_7416_;
}
v_resetjp_7416_:
{
lean_object* v___x_7420_; 
if (v_isShared_7418_ == 0)
{
v___x_7420_ = v___x_7417_;
goto v_reusejp_7419_;
}
else
{
lean_object* v_reuseFailAlloc_7421_; 
v_reuseFailAlloc_7421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7421_, 0, v_a_7415_);
v___x_7420_ = v_reuseFailAlloc_7421_;
goto v_reusejp_7419_;
}
v_reusejp_7419_:
{
return v___x_7420_;
}
}
}
}
else
{
lean_object* v_a_7423_; lean_object* v___x_7425_; uint8_t v_isShared_7426_; uint8_t v_isSharedCheck_7430_; 
lean_dec_ref(v_arg_7335_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
lean_dec(v_goal_7011_);
v_a_7423_ = lean_ctor_get(v___x_7357_, 0);
v_isSharedCheck_7430_ = !lean_is_exclusive(v___x_7357_);
if (v_isSharedCheck_7430_ == 0)
{
v___x_7425_ = v___x_7357_;
v_isShared_7426_ = v_isSharedCheck_7430_;
goto v_resetjp_7424_;
}
else
{
lean_inc(v_a_7423_);
lean_dec(v___x_7357_);
v___x_7425_ = lean_box(0);
v_isShared_7426_ = v_isSharedCheck_7430_;
goto v_resetjp_7424_;
}
v_resetjp_7424_:
{
lean_object* v___x_7428_; 
if (v_isShared_7426_ == 0)
{
v___x_7428_ = v___x_7425_;
goto v_reusejp_7427_;
}
else
{
lean_object* v_reuseFailAlloc_7429_; 
v_reuseFailAlloc_7429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7429_, 0, v_a_7423_);
v___x_7428_ = v_reuseFailAlloc_7429_;
goto v_reusejp_7427_;
}
v_reusejp_7427_:
{
return v___x_7428_;
}
}
}
}
}
}
else
{
lean_object* v_a_7432_; lean_object* v___x_7434_; uint8_t v_isShared_7435_; uint8_t v_isSharedCheck_7439_; 
lean_dec_ref(v_arg_7335_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7432_ = lean_ctor_get(v___x_7339_, 0);
v_isSharedCheck_7439_ = !lean_is_exclusive(v___x_7339_);
if (v_isSharedCheck_7439_ == 0)
{
v___x_7434_ = v___x_7339_;
v_isShared_7435_ = v_isSharedCheck_7439_;
goto v_resetjp_7433_;
}
else
{
lean_inc(v_a_7432_);
lean_dec(v___x_7339_);
v___x_7434_ = lean_box(0);
v_isShared_7435_ = v_isSharedCheck_7439_;
goto v_resetjp_7433_;
}
v_resetjp_7433_:
{
lean_object* v___x_7437_; 
if (v_isShared_7435_ == 0)
{
v___x_7437_ = v___x_7434_;
goto v_reusejp_7436_;
}
else
{
lean_object* v_reuseFailAlloc_7438_; 
v_reuseFailAlloc_7438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7438_, 0, v_a_7432_);
v___x_7437_ = v_reuseFailAlloc_7438_;
goto v_reusejp_7436_;
}
v_reusejp_7436_:
{
return v___x_7437_;
}
}
}
}
}
else
{
lean_object* v_a_7440_; lean_object* v___x_7442_; uint8_t v_isShared_7443_; uint8_t v_isSharedCheck_7447_; 
lean_dec_ref(v_arg_7335_);
lean_dec_ref(v_arg_7334_);
lean_dec_ref(v_arg_7333_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7440_ = lean_ctor_get(v___x_7336_, 0);
v_isSharedCheck_7447_ = !lean_is_exclusive(v___x_7336_);
if (v_isSharedCheck_7447_ == 0)
{
v___x_7442_ = v___x_7336_;
v_isShared_7443_ = v_isSharedCheck_7447_;
goto v_resetjp_7441_;
}
else
{
lean_inc(v_a_7440_);
lean_dec(v___x_7336_);
v___x_7442_ = lean_box(0);
v_isShared_7443_ = v_isSharedCheck_7447_;
goto v_resetjp_7441_;
}
v_resetjp_7441_:
{
lean_object* v___x_7445_; 
if (v_isShared_7443_ == 0)
{
v___x_7445_ = v___x_7442_;
goto v_reusejp_7444_;
}
else
{
lean_object* v_reuseFailAlloc_7446_; 
v_reuseFailAlloc_7446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7446_, 0, v_a_7440_);
v___x_7445_ = v_reuseFailAlloc_7446_;
goto v_reusejp_7444_;
}
v_reusejp_7444_:
{
return v___x_7445_;
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
lean_object* v_a_7448_; lean_object* v___x_7450_; uint8_t v_isShared_7451_; uint8_t v_isSharedCheck_7455_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7448_ = lean_ctor_get(v___x_7319_, 0);
v_isSharedCheck_7455_ = !lean_is_exclusive(v___x_7319_);
if (v_isSharedCheck_7455_ == 0)
{
v___x_7450_ = v___x_7319_;
v_isShared_7451_ = v_isSharedCheck_7455_;
goto v_resetjp_7449_;
}
else
{
lean_inc(v_a_7448_);
lean_dec(v___x_7319_);
v___x_7450_ = lean_box(0);
v_isShared_7451_ = v_isSharedCheck_7455_;
goto v_resetjp_7449_;
}
v_resetjp_7449_:
{
lean_object* v___x_7453_; 
if (v_isShared_7451_ == 0)
{
v___x_7453_ = v___x_7450_;
goto v_reusejp_7452_;
}
else
{
lean_object* v_reuseFailAlloc_7454_; 
v_reuseFailAlloc_7454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7454_, 0, v_a_7448_);
v___x_7453_ = v_reuseFailAlloc_7454_;
goto v_reusejp_7452_;
}
v_reusejp_7452_:
{
return v___x_7453_;
}
}
}
}
}
else
{
lean_object* v_a_7456_; lean_object* v___x_7458_; uint8_t v_isShared_7459_; uint8_t v_isSharedCheck_7463_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7456_ = lean_ctor_get(v___x_7316_, 0);
v_isSharedCheck_7463_ = !lean_is_exclusive(v___x_7316_);
if (v_isSharedCheck_7463_ == 0)
{
v___x_7458_ = v___x_7316_;
v_isShared_7459_ = v_isSharedCheck_7463_;
goto v_resetjp_7457_;
}
else
{
lean_inc(v_a_7456_);
lean_dec(v___x_7316_);
v___x_7458_ = lean_box(0);
v_isShared_7459_ = v_isSharedCheck_7463_;
goto v_resetjp_7457_;
}
v_resetjp_7457_:
{
lean_object* v___x_7461_; 
if (v_isShared_7459_ == 0)
{
v___x_7461_ = v___x_7458_;
goto v_reusejp_7460_;
}
else
{
lean_object* v_reuseFailAlloc_7462_; 
v_reuseFailAlloc_7462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7462_, 0, v_a_7456_);
v___x_7461_ = v_reuseFailAlloc_7462_;
goto v_reusejp_7460_;
}
v_reusejp_7460_:
{
return v___x_7461_;
}
}
}
}
}
else
{
lean_object* v_a_7464_; lean_object* v___x_7466_; uint8_t v_isShared_7467_; uint8_t v_isSharedCheck_7471_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7464_ = lean_ctor_get(v___x_7313_, 0);
v_isSharedCheck_7471_ = !lean_is_exclusive(v___x_7313_);
if (v_isSharedCheck_7471_ == 0)
{
v___x_7466_ = v___x_7313_;
v_isShared_7467_ = v_isSharedCheck_7471_;
goto v_resetjp_7465_;
}
else
{
lean_inc(v_a_7464_);
lean_dec(v___x_7313_);
v___x_7466_ = lean_box(0);
v_isShared_7467_ = v_isSharedCheck_7471_;
goto v_resetjp_7465_;
}
v_resetjp_7465_:
{
lean_object* v___x_7469_; 
if (v_isShared_7467_ == 0)
{
v___x_7469_ = v___x_7466_;
goto v_reusejp_7468_;
}
else
{
lean_object* v_reuseFailAlloc_7470_; 
v_reuseFailAlloc_7470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7470_, 0, v_a_7464_);
v___x_7469_ = v_reuseFailAlloc_7470_;
goto v_reusejp_7468_;
}
v_reusejp_7468_:
{
return v___x_7469_;
}
}
}
}
}
else
{
lean_object* v_a_7472_; lean_object* v___x_7474_; uint8_t v_isShared_7475_; uint8_t v_isSharedCheck_7479_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7472_ = lean_ctor_get(v___x_7310_, 0);
v_isSharedCheck_7479_ = !lean_is_exclusive(v___x_7310_);
if (v_isSharedCheck_7479_ == 0)
{
v___x_7474_ = v___x_7310_;
v_isShared_7475_ = v_isSharedCheck_7479_;
goto v_resetjp_7473_;
}
else
{
lean_inc(v_a_7472_);
lean_dec(v___x_7310_);
v___x_7474_ = lean_box(0);
v_isShared_7475_ = v_isSharedCheck_7479_;
goto v_resetjp_7473_;
}
v_resetjp_7473_:
{
lean_object* v___x_7477_; 
if (v_isShared_7475_ == 0)
{
v___x_7477_ = v___x_7474_;
goto v_reusejp_7476_;
}
else
{
lean_object* v_reuseFailAlloc_7478_; 
v_reuseFailAlloc_7478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7478_, 0, v_a_7472_);
v___x_7477_ = v_reuseFailAlloc_7478_;
goto v_reusejp_7476_;
}
v_reusejp_7476_:
{
return v___x_7477_;
}
}
}
}
}
else
{
lean_object* v_a_7480_; lean_object* v___x_7482_; uint8_t v_isShared_7483_; uint8_t v_isSharedCheck_7487_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7480_ = lean_ctor_get(v___x_7307_, 0);
v_isSharedCheck_7487_ = !lean_is_exclusive(v___x_7307_);
if (v_isSharedCheck_7487_ == 0)
{
v___x_7482_ = v___x_7307_;
v_isShared_7483_ = v_isSharedCheck_7487_;
goto v_resetjp_7481_;
}
else
{
lean_inc(v_a_7480_);
lean_dec(v___x_7307_);
v___x_7482_ = lean_box(0);
v_isShared_7483_ = v_isSharedCheck_7487_;
goto v_resetjp_7481_;
}
v_resetjp_7481_:
{
lean_object* v___x_7485_; 
if (v_isShared_7483_ == 0)
{
v___x_7485_ = v___x_7482_;
goto v_reusejp_7484_;
}
else
{
lean_object* v_reuseFailAlloc_7486_; 
v_reuseFailAlloc_7486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7486_, 0, v_a_7480_);
v___x_7485_ = v_reuseFailAlloc_7486_;
goto v_reusejp_7484_;
}
v_reusejp_7484_:
{
return v___x_7485_;
}
}
}
}
}
else
{
lean_object* v_a_7488_; lean_object* v___x_7490_; uint8_t v_isShared_7491_; uint8_t v_isSharedCheck_7495_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7488_ = lean_ctor_get(v___x_7304_, 0);
v_isSharedCheck_7495_ = !lean_is_exclusive(v___x_7304_);
if (v_isSharedCheck_7495_ == 0)
{
v___x_7490_ = v___x_7304_;
v_isShared_7491_ = v_isSharedCheck_7495_;
goto v_resetjp_7489_;
}
else
{
lean_inc(v_a_7488_);
lean_dec(v___x_7304_);
v___x_7490_ = lean_box(0);
v_isShared_7491_ = v_isSharedCheck_7495_;
goto v_resetjp_7489_;
}
v_resetjp_7489_:
{
lean_object* v___x_7493_; 
if (v_isShared_7491_ == 0)
{
v___x_7493_ = v___x_7490_;
goto v_reusejp_7492_;
}
else
{
lean_object* v_reuseFailAlloc_7494_; 
v_reuseFailAlloc_7494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7494_, 0, v_a_7488_);
v___x_7493_ = v_reuseFailAlloc_7494_;
goto v_reusejp_7492_;
}
v_reusejp_7492_:
{
return v___x_7493_;
}
}
}
}
}
else
{
lean_object* v_a_7496_; lean_object* v___x_7498_; uint8_t v_isShared_7499_; uint8_t v_isSharedCheck_7503_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7496_ = lean_ctor_get(v___x_7301_, 0);
v_isSharedCheck_7503_ = !lean_is_exclusive(v___x_7301_);
if (v_isSharedCheck_7503_ == 0)
{
v___x_7498_ = v___x_7301_;
v_isShared_7499_ = v_isSharedCheck_7503_;
goto v_resetjp_7497_;
}
else
{
lean_inc(v_a_7496_);
lean_dec(v___x_7301_);
v___x_7498_ = lean_box(0);
v_isShared_7499_ = v_isSharedCheck_7503_;
goto v_resetjp_7497_;
}
v_resetjp_7497_:
{
lean_object* v___x_7501_; 
if (v_isShared_7499_ == 0)
{
v___x_7501_ = v___x_7498_;
goto v_reusejp_7500_;
}
else
{
lean_object* v_reuseFailAlloc_7502_; 
v_reuseFailAlloc_7502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7502_, 0, v_a_7496_);
v___x_7501_ = v_reuseFailAlloc_7502_;
goto v_reusejp_7500_;
}
v_reusejp_7500_:
{
return v___x_7501_;
}
}
}
}
}
else
{
lean_object* v_a_7504_; lean_object* v___x_7506_; uint8_t v_isShared_7507_; uint8_t v_isSharedCheck_7511_; 
lean_del_object(v___x_7273_);
lean_dec(v_a_7271_);
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7504_ = lean_ctor_get(v___x_7298_, 0);
v_isSharedCheck_7511_ = !lean_is_exclusive(v___x_7298_);
if (v_isSharedCheck_7511_ == 0)
{
v___x_7506_ = v___x_7298_;
v_isShared_7507_ = v_isSharedCheck_7511_;
goto v_resetjp_7505_;
}
else
{
lean_inc(v_a_7504_);
lean_dec(v___x_7298_);
v___x_7506_ = lean_box(0);
v_isShared_7507_ = v_isSharedCheck_7511_;
goto v_resetjp_7505_;
}
v_resetjp_7505_:
{
lean_object* v___x_7509_; 
if (v_isShared_7507_ == 0)
{
v___x_7509_ = v___x_7506_;
goto v_reusejp_7508_;
}
else
{
lean_object* v_reuseFailAlloc_7510_; 
v_reuseFailAlloc_7510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7510_, 0, v_a_7504_);
v___x_7509_ = v_reuseFailAlloc_7510_;
goto v_reusejp_7508_;
}
v_reusejp_7508_:
{
return v___x_7509_;
}
}
}
}
}
}
else
{
lean_object* v_a_7527_; lean_object* v___x_7529_; uint8_t v_isShared_7530_; uint8_t v_isSharedCheck_7534_; 
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7527_ = lean_ctor_get(v___x_7270_, 0);
v_isSharedCheck_7534_ = !lean_is_exclusive(v___x_7270_);
if (v_isSharedCheck_7534_ == 0)
{
v___x_7529_ = v___x_7270_;
v_isShared_7530_ = v_isSharedCheck_7534_;
goto v_resetjp_7528_;
}
else
{
lean_inc(v_a_7527_);
lean_dec(v___x_7270_);
v___x_7529_ = lean_box(0);
v_isShared_7530_ = v_isSharedCheck_7534_;
goto v_resetjp_7528_;
}
v_resetjp_7528_:
{
lean_object* v___x_7532_; 
if (v_isShared_7530_ == 0)
{
v___x_7532_ = v___x_7529_;
goto v_reusejp_7531_;
}
else
{
lean_object* v_reuseFailAlloc_7533_; 
v_reuseFailAlloc_7533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7533_, 0, v_a_7527_);
v___x_7532_ = v_reuseFailAlloc_7533_;
goto v_reusejp_7531_;
}
v_reusejp_7531_:
{
return v___x_7532_;
}
}
}
}
else
{
lean_object* v___x_7535_; lean_object* v___x_7537_; 
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v___x_7535_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__5));
if (v_isShared_7268_ == 0)
{
lean_ctor_set(v___x_7267_, 0, v___x_7535_);
v___x_7537_ = v___x_7267_;
goto v_reusejp_7536_;
}
else
{
lean_object* v_reuseFailAlloc_7538_; 
v_reuseFailAlloc_7538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7538_, 0, v___x_7535_);
v___x_7537_ = v_reuseFailAlloc_7538_;
goto v_reusejp_7536_;
}
v_reusejp_7536_:
{
return v___x_7537_;
}
}
}
}
else
{
lean_object* v_a_7540_; lean_object* v___x_7542_; uint8_t v_isShared_7543_; uint8_t v_isSharedCheck_7547_; 
lean_dec(v_goal_7011_);
lean_dec_ref(v_scope_7010_);
v_a_7540_ = lean_ctor_get(v___x_7264_, 0);
v_isSharedCheck_7547_ = !lean_is_exclusive(v___x_7264_);
if (v_isSharedCheck_7547_ == 0)
{
v___x_7542_ = v___x_7264_;
v_isShared_7543_ = v_isSharedCheck_7547_;
goto v_resetjp_7541_;
}
else
{
lean_inc(v_a_7540_);
lean_dec(v___x_7264_);
v___x_7542_ = lean_box(0);
v_isShared_7543_ = v_isSharedCheck_7547_;
goto v_resetjp_7541_;
}
v_resetjp_7541_:
{
lean_object* v___x_7545_; 
if (v_isShared_7543_ == 0)
{
v___x_7545_ = v___x_7542_;
goto v_reusejp_7544_;
}
else
{
lean_object* v_reuseFailAlloc_7546_; 
v_reuseFailAlloc_7546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7546_, 0, v_a_7540_);
v___x_7545_ = v_reuseFailAlloc_7546_;
goto v_reusejp_7544_;
}
v_reusejp_7544_:
{
return v___x_7545_;
}
}
}
v___jp_7024_:
{
lean_object* v___x_7026_; lean_object* v___x_7027_; lean_object* v___x_7028_; lean_object* v___x_7029_; 
v___x_7026_ = lean_box(0);
v___x_7027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7027_, 0, v_g_7025_);
lean_ctor_set(v___x_7027_, 1, v___x_7026_);
v___x_7028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7028_, 0, v_scope_7010_);
lean_ctor_set(v___x_7028_, 1, v___x_7027_);
v___x_7029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7029_, 0, v___x_7028_);
return v___x_7029_;
}
v___jp_7030_:
{
lean_object* v___x_7032_; lean_object* v___x_7033_; 
v___x_7032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7032_, 0, v_scope_7010_);
lean_ctor_set(v___x_7032_, 1, v_gs_7031_);
v___x_7033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7033_, 0, v___x_7032_);
return v___x_7033_;
}
v___jp_7034_:
{
lean_object* v___x_7037_; lean_object* v___x_7038_; 
v___x_7037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7037_, 0, v___y_7035_);
lean_ctor_set(v___x_7037_, 1, v_gs_7036_);
v___x_7038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7038_, 0, v___x_7037_);
return v___x_7038_;
}
v___jp_7039_:
{
lean_object* v___x_7043_; 
v___x_7043_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_7042_);
if (lean_obj_tag(v___x_7043_) == 0)
{
lean_object* v___x_7045_; uint8_t v_isShared_7046_; uint8_t v_isSharedCheck_7051_; 
v_isSharedCheck_7051_ = !lean_is_exclusive(v___x_7043_);
if (v_isSharedCheck_7051_ == 0)
{
lean_object* v_unused_7052_; 
v_unused_7052_ = lean_ctor_get(v___x_7043_, 0);
lean_dec(v_unused_7052_);
v___x_7045_ = v___x_7043_;
v_isShared_7046_ = v_isSharedCheck_7051_;
goto v_resetjp_7044_;
}
else
{
lean_dec(v___x_7043_);
v___x_7045_ = lean_box(0);
v_isShared_7046_ = v_isSharedCheck_7051_;
goto v_resetjp_7044_;
}
v_resetjp_7044_:
{
lean_object* v___x_7047_; lean_object* v___x_7049_; 
v___x_7047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7047_, 0, v___y_7040_);
lean_ctor_set(v___x_7047_, 1, v_gs_7041_);
if (v_isShared_7046_ == 0)
{
lean_ctor_set(v___x_7045_, 0, v___x_7047_);
v___x_7049_ = v___x_7045_;
goto v_reusejp_7048_;
}
else
{
lean_object* v_reuseFailAlloc_7050_; 
v_reuseFailAlloc_7050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7050_, 0, v___x_7047_);
v___x_7049_ = v_reuseFailAlloc_7050_;
goto v_reusejp_7048_;
}
v_reusejp_7048_:
{
return v___x_7049_;
}
}
}
else
{
lean_object* v_a_7053_; lean_object* v___x_7055_; uint8_t v_isShared_7056_; uint8_t v_isSharedCheck_7060_; 
lean_dec(v_gs_7041_);
lean_dec_ref(v___y_7040_);
v_a_7053_ = lean_ctor_get(v___x_7043_, 0);
v_isSharedCheck_7060_ = !lean_is_exclusive(v___x_7043_);
if (v_isSharedCheck_7060_ == 0)
{
v___x_7055_ = v___x_7043_;
v_isShared_7056_ = v_isSharedCheck_7060_;
goto v_resetjp_7054_;
}
else
{
lean_inc(v_a_7053_);
lean_dec(v___x_7043_);
v___x_7055_ = lean_box(0);
v_isShared_7056_ = v_isSharedCheck_7060_;
goto v_resetjp_7054_;
}
v_resetjp_7054_:
{
lean_object* v___x_7058_; 
if (v_isShared_7056_ == 0)
{
v___x_7058_ = v___x_7055_;
goto v_reusejp_7057_;
}
else
{
lean_object* v_reuseFailAlloc_7059_; 
v_reuseFailAlloc_7059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7059_, 0, v_a_7053_);
v___x_7058_ = v_reuseFailAlloc_7059_;
goto v_reusejp_7057_;
}
v_reusejp_7057_:
{
return v___x_7058_;
}
}
}
}
v___jp_7061_:
{
lean_object* v___x_7065_; 
v___x_7065_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_7064_);
if (lean_obj_tag(v___x_7065_) == 0)
{
lean_object* v___x_7067_; uint8_t v_isShared_7068_; uint8_t v_isSharedCheck_7075_; 
v_isSharedCheck_7075_ = !lean_is_exclusive(v___x_7065_);
if (v_isSharedCheck_7075_ == 0)
{
lean_object* v_unused_7076_; 
v_unused_7076_ = lean_ctor_get(v___x_7065_, 0);
lean_dec(v_unused_7076_);
v___x_7067_ = v___x_7065_;
v_isShared_7068_ = v_isSharedCheck_7075_;
goto v_resetjp_7066_;
}
else
{
lean_dec(v___x_7065_);
v___x_7067_ = lean_box(0);
v_isShared_7068_ = v_isSharedCheck_7075_;
goto v_resetjp_7066_;
}
v_resetjp_7066_:
{
lean_object* v___x_7069_; lean_object* v___x_7070_; lean_object* v___x_7071_; lean_object* v___x_7073_; 
v___x_7069_ = lean_box(0);
v___x_7070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7070_, 0, v_g_7063_);
lean_ctor_set(v___x_7070_, 1, v___x_7069_);
v___x_7071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7071_, 0, v___y_7062_);
lean_ctor_set(v___x_7071_, 1, v___x_7070_);
if (v_isShared_7068_ == 0)
{
lean_ctor_set(v___x_7067_, 0, v___x_7071_);
v___x_7073_ = v___x_7067_;
goto v_reusejp_7072_;
}
else
{
lean_object* v_reuseFailAlloc_7074_; 
v_reuseFailAlloc_7074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7074_, 0, v___x_7071_);
v___x_7073_ = v_reuseFailAlloc_7074_;
goto v_reusejp_7072_;
}
v_reusejp_7072_:
{
return v___x_7073_;
}
}
}
else
{
lean_object* v_a_7077_; lean_object* v___x_7079_; uint8_t v_isShared_7080_; uint8_t v_isSharedCheck_7084_; 
lean_dec(v_g_7063_);
lean_dec_ref(v___y_7062_);
v_a_7077_ = lean_ctor_get(v___x_7065_, 0);
v_isSharedCheck_7084_ = !lean_is_exclusive(v___x_7065_);
if (v_isSharedCheck_7084_ == 0)
{
v___x_7079_ = v___x_7065_;
v_isShared_7080_ = v_isSharedCheck_7084_;
goto v_resetjp_7078_;
}
else
{
lean_inc(v_a_7077_);
lean_dec(v___x_7065_);
v___x_7079_ = lean_box(0);
v_isShared_7080_ = v_isSharedCheck_7084_;
goto v_resetjp_7078_;
}
v_resetjp_7078_:
{
lean_object* v___x_7082_; 
if (v_isShared_7080_ == 0)
{
v___x_7082_ = v___x_7079_;
goto v_reusejp_7081_;
}
else
{
lean_object* v_reuseFailAlloc_7083_; 
v_reuseFailAlloc_7083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7083_, 0, v_a_7077_);
v___x_7082_ = v_reuseFailAlloc_7083_;
goto v_reusejp_7081_;
}
v_reusejp_7081_:
{
return v___x_7082_;
}
}
}
}
v___jp_7085_:
{
lean_object* v___x_7099_; 
v___x_7099_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_7088_);
if (lean_obj_tag(v___x_7099_) == 0)
{
lean_object* v___x_7100_; 
lean_dec_ref_known(v___x_7099_, 1);
v___x_7100_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_applySpecs(v___y_7098_, v_goal_7011_, v___y_7090_, v___y_7096_, v___y_7088_, v___y_7091_, v___y_7092_, v___y_7089_, v___y_7087_, v___y_7094_, v___y_7093_, v___y_7095_, v___y_7086_, v___y_7097_);
return v___x_7100_;
}
else
{
lean_object* v_a_7101_; lean_object* v___x_7103_; uint8_t v_isShared_7104_; uint8_t v_isSharedCheck_7108_; 
lean_dec_ref(v___y_7098_);
lean_dec_ref(v___y_7090_);
lean_dec(v_goal_7011_);
v_a_7101_ = lean_ctor_get(v___x_7099_, 0);
v_isSharedCheck_7108_ = !lean_is_exclusive(v___x_7099_);
if (v_isSharedCheck_7108_ == 0)
{
v___x_7103_ = v___x_7099_;
v_isShared_7104_ = v_isSharedCheck_7108_;
goto v_resetjp_7102_;
}
else
{
lean_inc(v_a_7101_);
lean_dec(v___x_7099_);
v___x_7103_ = lean_box(0);
v_isShared_7104_ = v_isSharedCheck_7108_;
goto v_resetjp_7102_;
}
v_resetjp_7102_:
{
lean_object* v___x_7106_; 
if (v_isShared_7104_ == 0)
{
v___x_7106_ = v___x_7103_;
goto v_reusejp_7105_;
}
else
{
lean_object* v_reuseFailAlloc_7107_; 
v_reuseFailAlloc_7107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7107_, 0, v_a_7101_);
v___x_7106_ = v_reuseFailAlloc_7107_;
goto v_reusejp_7105_;
}
v_reusejp_7105_:
{
return v___x_7106_;
}
}
}
}
v___jp_7109_:
{
lean_object* v___x_7123_; lean_object* v___x_7124_; 
v___x_7123_ = l_Lean_Elab_Tactic_VCGen_WPApp_prog(v___y_7110_);
lean_inc_ref(v___x_7123_);
v___x_7124_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_matchesUntilPattern___redArg(v___x_7123_, v___y_7112_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
if (lean_obj_tag(v___x_7124_) == 0)
{
lean_object* v_a_7125_; lean_object* v___x_7127_; uint8_t v_isShared_7128_; uint8_t v_isSharedCheck_7255_; 
v_a_7125_ = lean_ctor_get(v___x_7124_, 0);
v_isSharedCheck_7255_ = !lean_is_exclusive(v___x_7124_);
if (v_isSharedCheck_7255_ == 0)
{
v___x_7127_ = v___x_7124_;
v_isShared_7128_ = v_isSharedCheck_7255_;
goto v_resetjp_7126_;
}
else
{
lean_inc(v_a_7125_);
lean_dec(v___x_7124_);
v___x_7127_ = lean_box(0);
v_isShared_7128_ = v_isSharedCheck_7255_;
goto v_resetjp_7126_;
}
v_resetjp_7126_:
{
uint8_t v___x_7129_; 
v___x_7129_ = lean_unbox(v_a_7125_);
lean_dec(v_a_7125_);
if (v___x_7129_ == 0)
{
lean_object* v___x_7130_; 
lean_del_object(v___x_7127_);
lean_inc_ref(v___y_7110_);
lean_inc(v_goal_7011_);
v___x_7130_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpConsumeMData_x3f(v_goal_7011_, v___y_7110_, v___y_7112_, v___y_7113_, v___y_7114_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
if (lean_obj_tag(v___x_7130_) == 0)
{
lean_object* v_a_7131_; lean_object* v___x_7133_; uint8_t v_isShared_7134_; uint8_t v_isSharedCheck_7240_; 
v_a_7131_ = lean_ctor_get(v___x_7130_, 0);
v_isSharedCheck_7240_ = !lean_is_exclusive(v___x_7130_);
if (v_isSharedCheck_7240_ == 0)
{
v___x_7133_ = v___x_7130_;
v_isShared_7134_ = v_isSharedCheck_7240_;
goto v_resetjp_7132_;
}
else
{
lean_inc(v_a_7131_);
lean_dec(v___x_7130_);
v___x_7133_ = lean_box(0);
v_isShared_7134_ = v_isSharedCheck_7240_;
goto v_resetjp_7132_;
}
v_resetjp_7132_:
{
if (lean_obj_tag(v_a_7131_) == 1)
{
lean_object* v_val_7135_; lean_object* v___x_7136_; lean_object* v___x_7137_; lean_object* v___x_7138_; lean_object* v___x_7140_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_val_7135_ = lean_ctor_get(v_a_7131_, 0);
lean_inc(v_val_7135_);
lean_dec_ref_known(v_a_7131_, 1);
v___x_7136_ = lean_box(0);
v___x_7137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7137_, 0, v_val_7135_);
lean_ctor_set(v___x_7137_, 1, v___x_7136_);
v___x_7138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7138_, 0, v___y_7111_);
lean_ctor_set(v___x_7138_, 1, v___x_7137_);
if (v_isShared_7134_ == 0)
{
lean_ctor_set(v___x_7133_, 0, v___x_7138_);
v___x_7140_ = v___x_7133_;
goto v_reusejp_7139_;
}
else
{
lean_object* v_reuseFailAlloc_7141_; 
v_reuseFailAlloc_7141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7141_, 0, v___x_7138_);
v___x_7140_ = v_reuseFailAlloc_7141_;
goto v_reusejp_7139_;
}
v_reusejp_7139_:
{
return v___x_7140_;
}
}
else
{
lean_object* v___x_7142_; 
lean_del_object(v___x_7133_);
lean_dec(v_a_7131_);
lean_inc_ref(v___y_7110_);
lean_inc(v_goal_7011_);
v___x_7142_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpReduceHead_x3f(v_goal_7011_, v___y_7110_, v___y_7112_, v___y_7113_, v___y_7114_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
if (lean_obj_tag(v___x_7142_) == 0)
{
lean_object* v_a_7143_; 
v_a_7143_ = lean_ctor_get(v___x_7142_, 0);
lean_inc(v_a_7143_);
lean_dec_ref_known(v___x_7142_, 1);
if (lean_obj_tag(v_a_7143_) == 1)
{
lean_object* v_val_7144_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_val_7144_ = lean_ctor_get(v_a_7143_, 0);
lean_inc(v_val_7144_);
lean_dec_ref_known(v_a_7143_, 1);
v___y_7062_ = v___y_7111_;
v_g_7063_ = v_val_7144_;
v___y_7064_ = v___y_7113_;
goto v___jp_7061_;
}
else
{
lean_object* v___x_7145_; 
lean_dec(v_a_7143_);
lean_inc_ref(v___y_7110_);
lean_inc(v_goal_7011_);
lean_inc_ref(v___y_7111_);
v___x_7145_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpLet_x3f(v___y_7111_, v_goal_7011_, v___y_7110_, v___y_7112_, v___y_7113_, v___y_7114_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
if (lean_obj_tag(v___x_7145_) == 0)
{
lean_object* v_a_7146_; 
v_a_7146_ = lean_ctor_get(v___x_7145_, 0);
lean_inc(v_a_7146_);
lean_dec_ref_known(v___x_7145_, 1);
if (lean_obj_tag(v_a_7146_) == 1)
{
lean_object* v_val_7147_; lean_object* v_fst_7148_; lean_object* v_snd_7149_; lean_object* v___x_7151_; uint8_t v_isShared_7152_; uint8_t v_isSharedCheck_7173_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7111_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_val_7147_ = lean_ctor_get(v_a_7146_, 0);
lean_inc(v_val_7147_);
lean_dec_ref_known(v_a_7146_, 1);
v_fst_7148_ = lean_ctor_get(v_val_7147_, 0);
v_snd_7149_ = lean_ctor_get(v_val_7147_, 1);
v_isSharedCheck_7173_ = !lean_is_exclusive(v_val_7147_);
if (v_isSharedCheck_7173_ == 0)
{
v___x_7151_ = v_val_7147_;
v_isShared_7152_ = v_isSharedCheck_7173_;
goto v_resetjp_7150_;
}
else
{
lean_inc(v_snd_7149_);
lean_inc(v_fst_7148_);
lean_dec(v_val_7147_);
v___x_7151_ = lean_box(0);
v_isShared_7152_ = v_isSharedCheck_7173_;
goto v_resetjp_7150_;
}
v_resetjp_7150_:
{
lean_object* v___x_7153_; 
v___x_7153_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v___y_7113_);
if (lean_obj_tag(v___x_7153_) == 0)
{
lean_object* v___x_7155_; uint8_t v_isShared_7156_; uint8_t v_isSharedCheck_7163_; 
v_isSharedCheck_7163_ = !lean_is_exclusive(v___x_7153_);
if (v_isSharedCheck_7163_ == 0)
{
lean_object* v_unused_7164_; 
v_unused_7164_ = lean_ctor_get(v___x_7153_, 0);
lean_dec(v_unused_7164_);
v___x_7155_ = v___x_7153_;
v_isShared_7156_ = v_isSharedCheck_7163_;
goto v_resetjp_7154_;
}
else
{
lean_dec(v___x_7153_);
v___x_7155_ = lean_box(0);
v_isShared_7156_ = v_isSharedCheck_7163_;
goto v_resetjp_7154_;
}
v_resetjp_7154_:
{
lean_object* v___x_7158_; 
if (v_isShared_7152_ == 0)
{
v___x_7158_ = v___x_7151_;
goto v_reusejp_7157_;
}
else
{
lean_object* v_reuseFailAlloc_7162_; 
v_reuseFailAlloc_7162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7162_, 0, v_fst_7148_);
lean_ctor_set(v_reuseFailAlloc_7162_, 1, v_snd_7149_);
v___x_7158_ = v_reuseFailAlloc_7162_;
goto v_reusejp_7157_;
}
v_reusejp_7157_:
{
lean_object* v___x_7160_; 
if (v_isShared_7156_ == 0)
{
lean_ctor_set(v___x_7155_, 0, v___x_7158_);
v___x_7160_ = v___x_7155_;
goto v_reusejp_7159_;
}
else
{
lean_object* v_reuseFailAlloc_7161_; 
v_reuseFailAlloc_7161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7161_, 0, v___x_7158_);
v___x_7160_ = v_reuseFailAlloc_7161_;
goto v_reusejp_7159_;
}
v_reusejp_7159_:
{
return v___x_7160_;
}
}
}
}
else
{
lean_object* v_a_7165_; lean_object* v___x_7167_; uint8_t v_isShared_7168_; uint8_t v_isSharedCheck_7172_; 
lean_del_object(v___x_7151_);
lean_dec(v_snd_7149_);
lean_dec(v_fst_7148_);
v_a_7165_ = lean_ctor_get(v___x_7153_, 0);
v_isSharedCheck_7172_ = !lean_is_exclusive(v___x_7153_);
if (v_isSharedCheck_7172_ == 0)
{
v___x_7167_ = v___x_7153_;
v_isShared_7168_ = v_isSharedCheck_7172_;
goto v_resetjp_7166_;
}
else
{
lean_inc(v_a_7165_);
lean_dec(v___x_7153_);
v___x_7167_ = lean_box(0);
v_isShared_7168_ = v_isSharedCheck_7172_;
goto v_resetjp_7166_;
}
v_resetjp_7166_:
{
lean_object* v___x_7170_; 
if (v_isShared_7168_ == 0)
{
v___x_7170_ = v___x_7167_;
goto v_reusejp_7169_;
}
else
{
lean_object* v_reuseFailAlloc_7171_; 
v_reuseFailAlloc_7171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7171_, 0, v_a_7165_);
v___x_7170_ = v_reuseFailAlloc_7171_;
goto v_reusejp_7169_;
}
v_reusejp_7169_:
{
return v___x_7170_;
}
}
}
}
}
else
{
lean_object* v___x_7174_; 
lean_dec(v_a_7146_);
lean_inc_ref(v___y_7110_);
lean_inc(v_goal_7011_);
v___x_7174_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpSimpStateArgs_x3f(v_goal_7011_, v___y_7110_, v___y_7112_, v___y_7113_, v___y_7114_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
if (lean_obj_tag(v___x_7174_) == 0)
{
lean_object* v_a_7175_; 
v_a_7175_ = lean_ctor_get(v___x_7174_, 0);
lean_inc(v_a_7175_);
lean_dec_ref_known(v___x_7174_, 1);
if (lean_obj_tag(v_a_7175_) == 1)
{
lean_object* v_val_7176_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_val_7176_ = lean_ctor_get(v_a_7175_, 0);
lean_inc(v_val_7176_);
lean_dec_ref_known(v_a_7175_, 1);
v___y_7035_ = v___y_7111_;
v_gs_7036_ = v_val_7176_;
goto v___jp_7034_;
}
else
{
lean_object* v___x_7177_; 
lean_dec(v_a_7175_);
lean_inc_ref(v___y_7110_);
lean_inc(v_goal_7011_);
v___x_7177_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpMatch_x3f(v_goal_7011_, v___y_7110_, v___y_7112_, v___y_7113_, v___y_7114_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
if (lean_obj_tag(v___x_7177_) == 0)
{
lean_object* v_a_7178_; 
v_a_7178_ = lean_ctor_get(v___x_7177_, 0);
lean_inc(v_a_7178_);
lean_dec_ref_known(v___x_7177_, 1);
if (lean_obj_tag(v_a_7178_) == 1)
{
lean_object* v_val_7179_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_val_7179_ = lean_ctor_get(v_a_7178_, 0);
lean_inc(v_val_7179_);
lean_dec_ref_known(v_a_7178_, 1);
v___y_7040_ = v___y_7111_;
v_gs_7041_ = v_val_7179_;
v___y_7042_ = v___y_7113_;
goto v___jp_7039_;
}
else
{
lean_object* v___x_7180_; 
lean_dec(v_a_7178_);
lean_inc_ref(v___y_7110_);
lean_inc(v_goal_7011_);
v___x_7180_ = l_Lean_Elab_Tactic_VCGen_wpJump_x3f(v___y_7111_, v_goal_7011_, v___y_7110_, v___y_7112_, v___y_7113_, v___y_7114_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
if (lean_obj_tag(v___x_7180_) == 0)
{
lean_object* v_a_7181_; 
v_a_7181_ = lean_ctor_get(v___x_7180_, 0);
lean_inc(v_a_7181_);
lean_dec_ref_known(v___x_7180_, 1);
if (lean_obj_tag(v_a_7181_) == 1)
{
lean_object* v_val_7182_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_val_7182_ = lean_ctor_get(v_a_7181_, 0);
lean_inc(v_val_7182_);
lean_dec_ref_known(v_a_7181_, 1);
v___y_7040_ = v___y_7111_;
v_gs_7041_ = v_val_7182_;
v___y_7042_ = v___y_7113_;
goto v___jp_7039_;
}
else
{
lean_object* v___x_7183_; 
lean_dec(v_a_7181_);
lean_inc_ref(v___y_7110_);
lean_inc(v_goal_7011_);
v___x_7183_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_wpFVarZeta_x3f(v_goal_7011_, v___y_7110_, v___y_7112_, v___y_7113_, v___y_7114_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
if (lean_obj_tag(v___x_7183_) == 0)
{
lean_object* v_a_7184_; 
v_a_7184_ = lean_ctor_get(v___x_7183_, 0);
lean_inc(v_a_7184_);
lean_dec_ref_known(v___x_7183_, 1);
if (lean_obj_tag(v_a_7184_) == 1)
{
lean_object* v_val_7185_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_val_7185_ = lean_ctor_get(v_a_7184_, 0);
lean_inc(v_val_7185_);
lean_dec_ref_known(v_a_7184_, 1);
v___y_7062_ = v___y_7111_;
v_g_7063_ = v_val_7185_;
v___y_7064_ = v___y_7113_;
goto v___jp_7061_;
}
else
{
lean_object* v___x_7186_; uint8_t v___x_7187_; 
lean_dec(v_a_7184_);
v___x_7186_ = l_Lean_Expr_getAppFn(v___x_7123_);
v___x_7187_ = l_Lean_Expr_isConst(v___x_7186_);
if (v___x_7187_ == 0)
{
uint8_t v___x_7188_; 
v___x_7188_ = l_Lean_Expr_isFVar(v___x_7186_);
lean_dec_ref(v___x_7186_);
if (v___x_7188_ == 0)
{
lean_object* v___x_7189_; lean_object* v___x_7190_; lean_object* v___x_7191_; 
lean_dec_ref(v___y_7111_);
lean_dec(v_goal_7011_);
v___x_7189_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v___y_7110_);
lean_dec_ref(v___y_7110_);
v___x_7190_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___closed__0));
v___x_7191_ = l___private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_7123_, v___x_7189_, v___x_7190_, v___y_7112_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
return v___x_7191_;
}
else
{
lean_dec_ref(v___x_7123_);
v___y_7086_ = v___y_7121_;
v___y_7087_ = v___y_7117_;
v___y_7088_ = v___y_7113_;
v___y_7089_ = v___y_7116_;
v___y_7090_ = v___y_7110_;
v___y_7091_ = v___y_7114_;
v___y_7092_ = v___y_7115_;
v___y_7093_ = v___y_7119_;
v___y_7094_ = v___y_7118_;
v___y_7095_ = v___y_7120_;
v___y_7096_ = v___y_7112_;
v___y_7097_ = v___y_7122_;
v___y_7098_ = v___y_7111_;
goto v___jp_7085_;
}
}
else
{
lean_dec_ref(v___x_7186_);
lean_dec_ref(v___x_7123_);
v___y_7086_ = v___y_7121_;
v___y_7087_ = v___y_7117_;
v___y_7088_ = v___y_7113_;
v___y_7089_ = v___y_7116_;
v___y_7090_ = v___y_7110_;
v___y_7091_ = v___y_7114_;
v___y_7092_ = v___y_7115_;
v___y_7093_ = v___y_7119_;
v___y_7094_ = v___y_7118_;
v___y_7095_ = v___y_7120_;
v___y_7096_ = v___y_7112_;
v___y_7097_ = v___y_7122_;
v___y_7098_ = v___y_7111_;
goto v___jp_7085_;
}
}
}
else
{
lean_object* v_a_7192_; lean_object* v___x_7194_; uint8_t v_isShared_7195_; uint8_t v_isSharedCheck_7199_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7111_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_a_7192_ = lean_ctor_get(v___x_7183_, 0);
v_isSharedCheck_7199_ = !lean_is_exclusive(v___x_7183_);
if (v_isSharedCheck_7199_ == 0)
{
v___x_7194_ = v___x_7183_;
v_isShared_7195_ = v_isSharedCheck_7199_;
goto v_resetjp_7193_;
}
else
{
lean_inc(v_a_7192_);
lean_dec(v___x_7183_);
v___x_7194_ = lean_box(0);
v_isShared_7195_ = v_isSharedCheck_7199_;
goto v_resetjp_7193_;
}
v_resetjp_7193_:
{
lean_object* v___x_7197_; 
if (v_isShared_7195_ == 0)
{
v___x_7197_ = v___x_7194_;
goto v_reusejp_7196_;
}
else
{
lean_object* v_reuseFailAlloc_7198_; 
v_reuseFailAlloc_7198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7198_, 0, v_a_7192_);
v___x_7197_ = v_reuseFailAlloc_7198_;
goto v_reusejp_7196_;
}
v_reusejp_7196_:
{
return v___x_7197_;
}
}
}
}
}
else
{
lean_object* v_a_7200_; lean_object* v___x_7202_; uint8_t v_isShared_7203_; uint8_t v_isSharedCheck_7207_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7111_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_a_7200_ = lean_ctor_get(v___x_7180_, 0);
v_isSharedCheck_7207_ = !lean_is_exclusive(v___x_7180_);
if (v_isSharedCheck_7207_ == 0)
{
v___x_7202_ = v___x_7180_;
v_isShared_7203_ = v_isSharedCheck_7207_;
goto v_resetjp_7201_;
}
else
{
lean_inc(v_a_7200_);
lean_dec(v___x_7180_);
v___x_7202_ = lean_box(0);
v_isShared_7203_ = v_isSharedCheck_7207_;
goto v_resetjp_7201_;
}
v_resetjp_7201_:
{
lean_object* v___x_7205_; 
if (v_isShared_7203_ == 0)
{
v___x_7205_ = v___x_7202_;
goto v_reusejp_7204_;
}
else
{
lean_object* v_reuseFailAlloc_7206_; 
v_reuseFailAlloc_7206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7206_, 0, v_a_7200_);
v___x_7205_ = v_reuseFailAlloc_7206_;
goto v_reusejp_7204_;
}
v_reusejp_7204_:
{
return v___x_7205_;
}
}
}
}
}
else
{
lean_object* v_a_7208_; lean_object* v___x_7210_; uint8_t v_isShared_7211_; uint8_t v_isSharedCheck_7215_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7111_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_a_7208_ = lean_ctor_get(v___x_7177_, 0);
v_isSharedCheck_7215_ = !lean_is_exclusive(v___x_7177_);
if (v_isSharedCheck_7215_ == 0)
{
v___x_7210_ = v___x_7177_;
v_isShared_7211_ = v_isSharedCheck_7215_;
goto v_resetjp_7209_;
}
else
{
lean_inc(v_a_7208_);
lean_dec(v___x_7177_);
v___x_7210_ = lean_box(0);
v_isShared_7211_ = v_isSharedCheck_7215_;
goto v_resetjp_7209_;
}
v_resetjp_7209_:
{
lean_object* v___x_7213_; 
if (v_isShared_7211_ == 0)
{
v___x_7213_ = v___x_7210_;
goto v_reusejp_7212_;
}
else
{
lean_object* v_reuseFailAlloc_7214_; 
v_reuseFailAlloc_7214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7214_, 0, v_a_7208_);
v___x_7213_ = v_reuseFailAlloc_7214_;
goto v_reusejp_7212_;
}
v_reusejp_7212_:
{
return v___x_7213_;
}
}
}
}
}
else
{
lean_object* v_a_7216_; lean_object* v___x_7218_; uint8_t v_isShared_7219_; uint8_t v_isSharedCheck_7223_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7111_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_a_7216_ = lean_ctor_get(v___x_7174_, 0);
v_isSharedCheck_7223_ = !lean_is_exclusive(v___x_7174_);
if (v_isSharedCheck_7223_ == 0)
{
v___x_7218_ = v___x_7174_;
v_isShared_7219_ = v_isSharedCheck_7223_;
goto v_resetjp_7217_;
}
else
{
lean_inc(v_a_7216_);
lean_dec(v___x_7174_);
v___x_7218_ = lean_box(0);
v_isShared_7219_ = v_isSharedCheck_7223_;
goto v_resetjp_7217_;
}
v_resetjp_7217_:
{
lean_object* v___x_7221_; 
if (v_isShared_7219_ == 0)
{
v___x_7221_ = v___x_7218_;
goto v_reusejp_7220_;
}
else
{
lean_object* v_reuseFailAlloc_7222_; 
v_reuseFailAlloc_7222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7222_, 0, v_a_7216_);
v___x_7221_ = v_reuseFailAlloc_7222_;
goto v_reusejp_7220_;
}
v_reusejp_7220_:
{
return v___x_7221_;
}
}
}
}
}
else
{
lean_object* v_a_7224_; lean_object* v___x_7226_; uint8_t v_isShared_7227_; uint8_t v_isSharedCheck_7231_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7111_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_a_7224_ = lean_ctor_get(v___x_7145_, 0);
v_isSharedCheck_7231_ = !lean_is_exclusive(v___x_7145_);
if (v_isSharedCheck_7231_ == 0)
{
v___x_7226_ = v___x_7145_;
v_isShared_7227_ = v_isSharedCheck_7231_;
goto v_resetjp_7225_;
}
else
{
lean_inc(v_a_7224_);
lean_dec(v___x_7145_);
v___x_7226_ = lean_box(0);
v_isShared_7227_ = v_isSharedCheck_7231_;
goto v_resetjp_7225_;
}
v_resetjp_7225_:
{
lean_object* v___x_7229_; 
if (v_isShared_7227_ == 0)
{
v___x_7229_ = v___x_7226_;
goto v_reusejp_7228_;
}
else
{
lean_object* v_reuseFailAlloc_7230_; 
v_reuseFailAlloc_7230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7230_, 0, v_a_7224_);
v___x_7229_ = v_reuseFailAlloc_7230_;
goto v_reusejp_7228_;
}
v_reusejp_7228_:
{
return v___x_7229_;
}
}
}
}
}
else
{
lean_object* v_a_7232_; lean_object* v___x_7234_; uint8_t v_isShared_7235_; uint8_t v_isSharedCheck_7239_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7111_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_a_7232_ = lean_ctor_get(v___x_7142_, 0);
v_isSharedCheck_7239_ = !lean_is_exclusive(v___x_7142_);
if (v_isSharedCheck_7239_ == 0)
{
v___x_7234_ = v___x_7142_;
v_isShared_7235_ = v_isSharedCheck_7239_;
goto v_resetjp_7233_;
}
else
{
lean_inc(v_a_7232_);
lean_dec(v___x_7142_);
v___x_7234_ = lean_box(0);
v_isShared_7235_ = v_isSharedCheck_7239_;
goto v_resetjp_7233_;
}
v_resetjp_7233_:
{
lean_object* v___x_7237_; 
if (v_isShared_7235_ == 0)
{
v___x_7237_ = v___x_7234_;
goto v_reusejp_7236_;
}
else
{
lean_object* v_reuseFailAlloc_7238_; 
v_reuseFailAlloc_7238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7238_, 0, v_a_7232_);
v___x_7237_ = v_reuseFailAlloc_7238_;
goto v_reusejp_7236_;
}
v_reusejp_7236_:
{
return v___x_7237_;
}
}
}
}
}
}
else
{
lean_object* v_a_7241_; lean_object* v___x_7243_; uint8_t v_isShared_7244_; uint8_t v_isSharedCheck_7248_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7111_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_a_7241_ = lean_ctor_get(v___x_7130_, 0);
v_isSharedCheck_7248_ = !lean_is_exclusive(v___x_7130_);
if (v_isSharedCheck_7248_ == 0)
{
v___x_7243_ = v___x_7130_;
v_isShared_7244_ = v_isSharedCheck_7248_;
goto v_resetjp_7242_;
}
else
{
lean_inc(v_a_7241_);
lean_dec(v___x_7130_);
v___x_7243_ = lean_box(0);
v_isShared_7244_ = v_isSharedCheck_7248_;
goto v_resetjp_7242_;
}
v_resetjp_7242_:
{
lean_object* v___x_7246_; 
if (v_isShared_7244_ == 0)
{
v___x_7246_ = v___x_7243_;
goto v_reusejp_7245_;
}
else
{
lean_object* v_reuseFailAlloc_7247_; 
v_reuseFailAlloc_7247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7247_, 0, v_a_7241_);
v___x_7246_ = v_reuseFailAlloc_7247_;
goto v_reusejp_7245_;
}
v_reusejp_7245_:
{
return v___x_7246_;
}
}
}
}
else
{
lean_object* v___x_7249_; lean_object* v___x_7250_; lean_object* v___x_7251_; lean_object* v___x_7253_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7111_);
lean_dec(v_goal_7011_);
v___x_7249_ = l_Lean_Elab_Tactic_VCGen_WPApp_M(v___y_7110_);
lean_dec_ref(v___y_7110_);
v___x_7250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7250_, 0, v___x_7249_);
v___x_7251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7251_, 0, v___x_7250_);
if (v_isShared_7128_ == 0)
{
lean_ctor_set(v___x_7127_, 0, v___x_7251_);
v___x_7253_ = v___x_7127_;
goto v_reusejp_7252_;
}
else
{
lean_object* v_reuseFailAlloc_7254_; 
v_reuseFailAlloc_7254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7254_, 0, v___x_7251_);
v___x_7253_ = v_reuseFailAlloc_7254_;
goto v_reusejp_7252_;
}
v_reusejp_7252_:
{
return v___x_7253_;
}
}
}
}
else
{
lean_object* v_a_7256_; lean_object* v___x_7258_; uint8_t v_isShared_7259_; uint8_t v_isSharedCheck_7263_; 
lean_dec_ref(v___x_7123_);
lean_dec_ref(v___y_7111_);
lean_dec_ref(v___y_7110_);
lean_dec(v_goal_7011_);
v_a_7256_ = lean_ctor_get(v___x_7124_, 0);
v_isSharedCheck_7263_ = !lean_is_exclusive(v___x_7124_);
if (v_isSharedCheck_7263_ == 0)
{
v___x_7258_ = v___x_7124_;
v_isShared_7259_ = v_isSharedCheck_7263_;
goto v_resetjp_7257_;
}
else
{
lean_inc(v_a_7256_);
lean_dec(v___x_7124_);
v___x_7258_ = lean_box(0);
v_isShared_7259_ = v_isSharedCheck_7263_;
goto v_resetjp_7257_;
}
v_resetjp_7257_:
{
lean_object* v___x_7261_; 
if (v_isShared_7259_ == 0)
{
v___x_7261_ = v___x_7258_;
goto v_reusejp_7260_;
}
else
{
lean_object* v_reuseFailAlloc_7262_; 
v_reuseFailAlloc_7262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7262_, 0, v_a_7256_);
v___x_7261_ = v_reuseFailAlloc_7262_;
goto v_reusejp_7260_;
}
v_reusejp_7260_:
{
return v___x_7261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___lam__0___boxed(lean_object* v_scope_7548_, lean_object* v_goal_7549_, lean_object* v___y_7550_, lean_object* v___y_7551_, lean_object* v___y_7552_, lean_object* v___y_7553_, lean_object* v___y_7554_, lean_object* v___y_7555_, lean_object* v___y_7556_, lean_object* v___y_7557_, lean_object* v___y_7558_, lean_object* v___y_7559_, lean_object* v___y_7560_, lean_object* v___y_7561_){
_start:
{
lean_object* v_res_7562_; 
v_res_7562_ = l_Lean_Elab_Tactic_VCGen_solve___lam__0(v_scope_7548_, v_goal_7549_, v___y_7550_, v___y_7551_, v___y_7552_, v___y_7553_, v___y_7554_, v___y_7555_, v___y_7556_, v___y_7557_, v___y_7558_, v___y_7559_, v___y_7560_);
lean_dec(v___y_7560_);
lean_dec_ref(v___y_7559_);
lean_dec(v___y_7558_);
lean_dec_ref(v___y_7557_);
lean_dec(v___y_7556_);
lean_dec_ref(v___y_7555_);
lean_dec(v___y_7554_);
lean_dec_ref(v___y_7553_);
lean_dec(v___y_7552_);
lean_dec(v___y_7551_);
lean_dec_ref(v___y_7550_);
return v_res_7562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve(lean_object* v_scope_7563_, lean_object* v_goal_7564_, lean_object* v_a_7565_, lean_object* v_a_7566_, lean_object* v_a_7567_, lean_object* v_a_7568_, lean_object* v_a_7569_, lean_object* v_a_7570_, lean_object* v_a_7571_, lean_object* v_a_7572_, lean_object* v_a_7573_, lean_object* v_a_7574_, lean_object* v_a_7575_){
_start:
{
lean_object* v___f_7577_; lean_object* v___x_7578_; 
lean_inc(v_goal_7564_);
v___f_7577_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_solve___lam__0___boxed), 14, 2);
lean_closure_set(v___f_7577_, 0, v_scope_7563_);
lean_closure_set(v___f_7577_, 1, v_goal_7564_);
v___x_7578_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Solve_0__Lean_Elab_Tactic_VCGen_splitProdBinder_spec__3___redArg(v_goal_7564_, v___f_7577_, v_a_7565_, v_a_7566_, v_a_7567_, v_a_7568_, v_a_7569_, v_a_7570_, v_a_7571_, v_a_7572_, v_a_7573_, v_a_7574_, v_a_7575_);
return v___x_7578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_solve___boxed(lean_object* v_scope_7579_, lean_object* v_goal_7580_, lean_object* v_a_7581_, lean_object* v_a_7582_, lean_object* v_a_7583_, lean_object* v_a_7584_, lean_object* v_a_7585_, lean_object* v_a_7586_, lean_object* v_a_7587_, lean_object* v_a_7588_, lean_object* v_a_7589_, lean_object* v_a_7590_, lean_object* v_a_7591_, lean_object* v_a_7592_){
_start:
{
lean_object* v_res_7593_; 
v_res_7593_ = l_Lean_Elab_Tactic_VCGen_solve(v_scope_7579_, v_goal_7580_, v_a_7581_, v_a_7582_, v_a_7583_, v_a_7584_, v_a_7585_, v_a_7586_, v_a_7587_, v_a_7588_, v_a_7589_, v_a_7590_, v_a_7591_);
lean_dec(v_a_7591_);
lean_dec_ref(v_a_7590_);
lean_dec(v_a_7589_);
lean_dec_ref(v_a_7588_);
lean_dec(v_a_7587_);
lean_dec_ref(v_a_7586_);
lean_dec(v_a_7585_);
lean_dec_ref(v_a_7584_);
lean_dec(v_a_7583_);
lean_dec(v_a_7582_);
lean_dec_ref(v_a_7581_);
return v_res_7593_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_RuleCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Entails(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_JoinPoint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_BinderName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_Tactic_VCGen_JoinPoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_BinderName(builtin);
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
res = runtime_initialize_Init_Data_Prod(builtin);
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
lean_object* initialize_Lean_Elab_Tactic_VCGen_JoinPoint(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_BinderName(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
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
res = initialize_Lean_Elab_Tactic_VCGen_JoinPoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_BinderName(builtin);
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
res = initialize_Init_Data_Prod(builtin);
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
